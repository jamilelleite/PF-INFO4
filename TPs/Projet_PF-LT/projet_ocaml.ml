
(* Exercice 1.1.1 *)


type bmvar =
  | A
  | B
  | C
  | D


type bmexp =
  | Exp of bmvar
  | F (*false*)
  | T (*true*)

type wbm =
  | MSkip 
  | MAssign of bmvar * bmexp
  | MSeq of wbm * wbm
  | MIf of bmexp * wbm * wbm
  | MWhile of bmexp * wbm



let if1_1: wbm = MAssign(C, T)

let if1_2: wbm = MAssign(A, Exp B)

let if2_1: wbm = MAssign(B, T)

let if2_2: wbm = MAssign(C, Exp A)

let if1: wbm = MSeq(if1_1, if1_2)

let if2: wbm = MSeq(if2_1, if2_2)

let if0_0: wbm = MIf(Exp C, if1, if2)

let wh: wbm = MWhile(Exp A, if0_0)


        
(* Analyse descendante récursive sur une liste avec des combinateurs *)

(* Utilitaire pour les tests *)

let list_of_string s =
  let n = String.length s in
  let rec boucle i =
    if i = n then [] else s.[i] :: boucle (i+1)
  in boucle 0

(* Le type des aspirateurs (fonctions qui aspirent le préfixe d'une liste) *)
type 'term analist = 'term list -> 'term list

exception Echec

(* terminal constant *)
let terminal (c : 't) : 't analist = function
  | x :: l when x = c -> l
  | _ -> raise Echec

(* terminal conditionnel *)
let terminal_cond (p : 'term -> bool) : 'term analist = function
  | x :: l when p x -> l
  | _ -> raise Echec

(* non-terminal vide *)
let epsilon : 'term analist = fun l -> l

(* ------------------------------------------------------------ *)
(* Combinateurs d'analyseurs purs *)
(* ------------------------------------------------------------ *)

(* a1 suivi de a2 *)
let (-->) (a1 : 'term analist) (a2 : 'term analist) : 'term analist =
  fun l -> let l = a1 l in a2 l

(* Choix entre a1 ou a2 *)
let (-|) (a1 : 'term analist) (a2 : 'term analist) : 'term analist =
  fun l -> try a1 l with Echec -> a2 l

(* Répétition (étoile de Kleene) *)
(* Grammaire :  A* ::=  A A* | ε *)
let rec star (a : 'term analist) : 'term analist = fun l -> l |>
  ( a --> star a ) -| epsilon

(* ------------------------------------------------------------ *)
(* Combinateurs d'analyseurs
   avec calcul supplémentaire, ex. d'un AST *)
(* ------------------------------------------------------------ *)

(* Le type des aspirateurs qui, en plus, rendent un résultat *)
type ('res, 'term) ranalist = 'term list -> 'res * 'term list

(* Un epsilon informatif *)
let epsilon_res (info : 'res) : ('res, 'term) ranalist =
  fun l -> (info, l)

(* Terminal conditionnel avec résultat *)
(* [f] ne retourne pas un booléen mais un résultat optionnel *)
let terminal_res (f : 'term -> 'res option) : ('res, 'term) ranalist =
  fun l -> match l with
  | x :: l -> (match f x with Some y -> y, l | None -> raise Echec)
  | _ -> raise Echec

(* a1 sans résultat suivi de a2 donnant un résultat *)
let ( -+>) (a1 : 'term analist) (a2 : ('res, 'term) ranalist) :
      ('res, 'term) ranalist =
  fun l -> let l = a1 l in a2 l

(* a1 rendant un résultat suivi de a2 rendant un résultat *)
let (++>) (a1 : ('resa, 'term) ranalist) (a2 : 'resa -> ('resb, 'term) ranalist) :
      ('resb, 'term) ranalist =
  fun l -> let (x, l) = a1 l in a2 x l

(* a1 rendant un résultat suivi de a2 sans résultat est peu utile *)

(* Choix entre a1 ou a2 informatifs *)
let (+|) (a1 : ('res, 'term) ranalist) (a2 : ('res, 'term) ranalist) :
      ('res, 'term) ranalist =
  fun l -> try a1 l with Echec -> a2 l



(* Exercice 1.1.2 *)

(*

C::= '0' | '1'
V::= 'a' | 'b' | 'c' | 'd'
A::= C | V
WBM::= V ':=' A 
     | WBM D
     | 'i(' A '){' WBM '}{' WBM '}
     | 'w(' A '){' WBM '}'
D::= ';' WBM
     | eps 
   

 *)

(* Exercice 1.1.3 *)

(*

C::= '0' | '1'
V::= 'a' | 'b' | 'c' | 'd'
A::= C | V
F::= V ':=' A H
     | 'i(' A '){' I '}{' I '}' I
     | 'w(' A '){' I '}' I
H::= ; F
     | eps
I::= F
     | eps
 *)

  (* Exercice 1.2.1 *)
          
(* if exp then P else Q.

                                 P              if exp then P else Q
          [[expr]]s1 = true   s1 ---> s2     s2 -----------------------> s3
       ---------------------------------------------------------------------
                       if exp then P else Q 
                S1 --------------------------> s3


                                    Q              if exp then P else Q
          [[expr]]s1 = false   s1 ----> s2     s2 -----------------------> s3
       ---------------------------------------------------------------------
                       if exp then P else Q 
                S1 --------------------------> s3



 *)


let p_C : char analist =
  (terminal '0')
  -| (terminal '1')

let p_V : char analist =
  (terminal 'a')
  -| (terminal 'b')
  -| (terminal 'c')
  -| (terminal 'd')

let p_A : char analist =
  (p_C)
  -| (p_V)

let rec p_F : char analist = fun l -> l |>  
  (terminal 'i' --> terminal '(' --> p_A --> terminal ')' --> terminal '{' --> p_F --> terminal '}' --> terminal '{' --> p_F --> terminal '}' --> p_I)
  -| (terminal 'w' --> terminal '('  --> p_A --> terminal ')' --> terminal '{'  --> p_F --> terminal '}' --> p_I)
  -| (p_V --> terminal ':' --> terminal '=' --> p_A --> p_H)
and p_H : char analist = fun l -> l |>
                                    (terminal ';' --> p_F)
-| (p_V --> terminal ':' --> terminal '=' --> p_A --> p_H)
  -| (epsilon)
and p_I : char analist = fun l -> l |>
                                  (p_F)
                                  -| epsilon


let _ = p_F (list_of_string "a:=1;b:=1;c:=1;w(a){i(c){c:=0;a:=b}{b:=0;c:=a}}")
let _ = p_F (list_of_string "a:=1;b:=1;c:=1;w(a){i(c){c:=0;a:=b;i(c){c:=0;a:=b}{b:=0;c:=a}c:=0}{b:=0;c:=a}}")
let _ = p_F (list_of_string "a:=1;b:=1;")

let pr_V: (bmvar, char) ranalist =
  
  (terminal 'a' -+> epsilon_res (A))
  +| (terminal 'b' -+> epsilon_res (B))
  +| (terminal 'c' -+> epsilon_res (C))
  +| (terminal 'd' -+> epsilon_res (D))

let pr_C: (bmexp, char) ranalist =
  (terminal '0' -+> epsilon_res (F))
+| (terminal '1' -+> epsilon_res (T))

let _ = pr_V (list_of_string "a:=0")

let pr_A: (bmexp, char) ranalist =
  (pr_C)
  +| (pr_V ++> fun a -> epsilon_res (Exp a))

let _ = pr_A(list_of_string "b:=1;")

let rec pr_F: (wbm, char) ranalist = fun l -> l |>
  (pr_V ++> fun a -> terminal ':' --> terminal '=' -+> pr_A ++> fun b -> pr_H ++> fun c -> (if (c=MSkip) then  epsilon_res (MAssign(a, b)) else epsilon_res (MSeq((MAssign(a, b)),c)) ))
  +| (terminal 'i' --> terminal '(' -+> pr_A ++> fun a -> terminal ')' --> terminal '{' -+> pr_I ++> fun b -> terminal '}' --> terminal '{' -+> pr_I ++> fun c -> terminal '}' -+> pr_I ++> fun d ->(if(d=MSkip) then epsilon_res (MIf (a, b, c)) else epsilon_res (MSeq(MIf (a, b, c), d))))
  +| (terminal 'w' --> terminal '(' -+> pr_A ++> fun a -> terminal ')' --> terminal '{' -+> pr_I ++> fun b -> terminal '}' -+> pr_I ++> fun d -> (if(d=MSkip) then epsilon_res (MWhile(a,b)) else   epsilon_res (MSeq(MWhile(a,b), d))) )
and pr_H: (wbm, char) ranalist = fun l -> l |>
  (terminal ';' -+> pr_F ++> fun a -> epsilon_res (a))
  +| epsilon_res MSkip
and pr_I: (wbm, char) ranalist = fun l -> l |>
  (pr_F)
  +| epsilon_res MSkip

let _ = pr_F (list_of_string "a:=1;b:=1;c:=1;w(a){i(c){c:=0;a:=b}{}a:=0}a:=1;")
let _ = pr_F (list_of_string "a:=1")
let _ = pr_F (list_of_string "i(c){c:=0;a:=b}{}")
let _ = pr_F (list_of_string "w(a){i(c){c:=0;a:=b}{}a:=0}")
