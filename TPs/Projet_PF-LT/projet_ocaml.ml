
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


(* Exercie 1.1.4 


 C ::= ’0’ | ’1’
 V ::= ’a’ | ’b’ | ’c’ | ’d’
 A ::= C | V
 E ::= T E'
 E' ::= '+'T |eps 
 T ::= F T'
 T' ::= '.' F| eps 
 F ::= ’!’ F | A | ’(’ E ’)’


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



(** Exercice 2.1.1 **)


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


(** Exercice 2.1.2 **)

let _ = pr_F (list_of_string "a:=1;b:=1;c:=1;w(a){i(c){c:=0;a:=b}{}a:=0}a:=1;")
let _ = pr_F (list_of_string "a:=1")
let _ = pr_F (list_of_string "i(c){c:=0;a:=b}{}")
let _ = pr_F (list_of_string "w(a){i(c){c:=0;a:=b}{}a:=0}")


             (** Exercice 2.1.3 **)

(* Grammaire du langage Whileb 


 C ::= ’0’ | ’1’
 V ::= ’a’ | ’b’ | ’c’ | ’d’
 A ::= C | V
 E ::= T En
 En ::= '+'T |eps 
 T ::= Fn Tn
 Tn ::= '.' Fn| eps 
 Fn ::= ’!’ Fn | A | ’(’ E ’)’
F::= V ':=' Fn H
     | 'i(' Fn '){' I '}{' I '}' I
     | 'w(' Fn '){' I '}' I
H::= ; F
     | eps
I::= F
     | eps

 *)

(* Nouveaux types pour représenter les expressions dans whileb *)

type bexp =
  | Exp of bmvar
  | F (*false*)
  | T (*true*)
  | Bnot of bexp
  | Band of bexp * bexp
  | Bor of bexp * bexp
  | Eps

type wb =
  | MSkip 
  | MAssign of bmvar * bexp
  | MSeq of wb * wb
  | MIf of bexp * wb * wb
  | MWhile of bexp * wb

(* Analyseur syntaxique de whileb *)

let pr_Vb: (bmvar, char) ranalist =
  
  (terminal 'a' -+> epsilon_res (A))
  +| (terminal 'b' -+> epsilon_res (B))
  +| (terminal 'c' -+> epsilon_res (C))
  +| (terminal 'd' -+> epsilon_res (D))


let pr_Cb: (bexp, char) ranalist =
  (terminal '0' -+> epsilon_res (F))
+| (terminal '1' -+> epsilon_res (T))

let _ = pr_Vb (list_of_string "a:=0")

let pr_Ab: (bexp, char) ranalist =
  (pr_Cb)
  +| (pr_Vb ++> fun a -> epsilon_res (Exp a))


    
let rec pr_E: (bexp, char) ranalist = fun l -> l |>
  (pr_T ++> fun a -> pr_EN ++> fun b -> (if b=Eps then (epsilon_res a) else (epsilon_res (Bor(a, b)))))
and pr_EN: (bexp, char) ranalist = fun l -> l |>
  (terminal '+' -+> pr_T ++> fun a -> epsilon_res a)
  +| (epsilon_res Eps)
and pr_T: (bexp, char) ranalist = fun l -> l |>
  (pr_FN ++> fun a -> pr_TN ++> fun b -> (if b=Eps then (epsilon_res a) else (epsilon_res (Band(a, b)))))
and pr_TN: (bexp, char) ranalist = fun l -> l |>
  (terminal '.' -+> pr_FN ++> fun a -> epsilon_res a)
  +| (epsilon_res Eps)
and pr_FN: (bexp, char) ranalist = fun l -> l |>
  (terminal '!' -+> pr_FN ++> fun a -> epsilon_res (Bnot(a)))
  +| (pr_Ab)
+| (terminal '(' -+> pr_E ++> fun a -> terminal ')' -+> epsilon_res a)

let rec pr_Fb: (wb, char) ranalist = fun l -> l |>
  (pr_Vb ++> fun a -> terminal ':' --> terminal '=' -+> pr_FN ++> fun b -> pr_Hb ++> fun c -> (if (c=MSkip) then  epsilon_res (MAssign(a, b)) else epsilon_res (MSeq((MAssign(a, b)),c)) ))
  +| (terminal 'i' --> terminal '(' -+> pr_FN ++> fun a -> terminal ')' --> terminal '{' -+> pr_Ib ++> fun b -> terminal '}' --> terminal '{' -+> pr_Ib ++> fun c -> terminal '}' -+> pr_Ib ++> fun d ->(if(d=MSkip) then epsilon_res (MIf (a, b, c)) else epsilon_res (MSeq(MIf (a, b, c), d))))
  +| (terminal 'w' --> terminal '(' -+> pr_FN ++> fun a -> terminal ')' --> terminal '{' -+> pr_Ib ++> fun b -> terminal '}' -+> pr_Ib ++> fun d -> (if(d=MSkip) then epsilon_res (MWhile(a,b)) else   epsilon_res (MSeq(MWhile(a,b), d))) )
and pr_Hb: (wb, char) ranalist = fun l -> l |>
  (terminal ';' -+> pr_Fb ++> fun a -> epsilon_res (a))
  +| epsilon_res MSkip
and pr_Ib: (wb, char) ranalist = fun l -> l |>
  (pr_Fb)
  +| epsilon_res MSkip

let _ = pr_Fb (list_of_string "a:=1;b:=1;c:=1;w(a){i(a){c:=0;a:=b;i(c){c:=0;a:=b}{b:=0;a:=0}c:=0}{b:=0;c:=a}}")

let _ = pr_Fb (list_of_string "a:=!(0+1);c:=(0.1);d:=((a+(b.0))+(!1))" )


    (***  2.2 Exécution d'un programme WHILEb **)

(*Exercice 2.2.1*)
(* Nous allons représenter l'état du programme par une liste dans laquelle chaque case contient T ou F (true ou false). la valeur de la variable représenté par la i ème lettre de l'alphabet est contenue dans la case i 
N si il n y a pas encore de valeur défini *)

   
type state = bool list

(** La fonction get x s rend la valeur de x dans s. *)

let get = fun (x : bmexp) (s : state) ->
  match x with
  |T -> true
  |F -> false
  |Exp v -> (match v with
             |A -> (match s with |a::s' -> a | _ -> raise Echec)          
             |B ->  (match s with |a::b :: s' -> b | _ -> raise Echec)            
             |C ->  (match s with |a::b :: c :: s' -> c | _ -> raise Echec)            
             |D ->  (match s with |a::b::c::d::s' -> d | _ -> raise Echec) )


let _ = get (Exp C) [true;true;false;true]



(*La mise à jour d'une variable v par un nouvel entier n dans un état s
    s'écrit 'update s v n'
    Cette fonction n'échoue jamais et écrit la valeur à sa place même
    si elle n'est pas encore définie dans l'état *)

let update = fun (s:state) (v:bmvar) (n:bool) ->
  match v with
  |A -> (match s with |a::s' -> n::s' | _ -> n::[])
  |B -> (match s with |a::b::s' -> a::n::s' |a::[] -> a::n::[] | _ ->  false::n::[] )
  |C -> (match s with |a::b::c::s' -> a::b::n::s' |a::b::s' -> a::b::n::s' |a::[] -> a::false::n::[] | _ ->  false::false::n::[])
  |D -> (match s with |a::b::c::d::s' -> a::b::c::n::s' |a::b::c::s' -> a::b::c::n::s' |a::b::[] -> a::b::false::n::[] | a::[] ->  false::false::false::n::[] | _ -> false::false::false::n::[])

let _ = Exp (A)

let rec sn_update = fun (p : wbm) (s : state) ->
  match p with
  |MSkip -> s
  |MAssign(a,b) ->  update s a (get b s)
  |MSeq (w1,w2) -> sn_update w2 (sn_update w1 s)
  |MIf (b,w1,w2) ->( match (get b s) with
                    |true -> sn_update w1 s
                    |false -> sn_update w2 s )
  |MWhile (b,w) as i -> (match (get b s) with
                        |true -> let s1 = (sn_update w s) in sn_update i s1
                        |false -> s )


let s = [true;true;false;true]
let (w,l) = pr_F (list_of_string "i(a){b:=c;a:=c}{}") in sn_update w s 
let (w1,l1) = pr_F (list_of_string "a:=1;b:=1;c:=1;w(a){i(c){c:=0;a:=b}{a:=0}}a:=1;") in sn_update w1 s


      (*** Exercice 2.2.2 ***)

let rec evalB = fun (b : bexp) (s: state) ->
  match b with
  |Exp v -> (match v with
             |A -> (match s with |a::s' -> a | _ -> raise Echec)          
             |B ->  (match s with |a::b :: s' -> b | _ -> raise Echec)            
             |C ->  (match s with |a::b :: c :: s' -> c | _ -> raise Echec)            
             |D ->  (match s with |a::b::c::d::s' -> d | _ -> raise Echec))
  |T -> true
  |F -> false
  |Bnot b1 -> not (evalB b1 s)
  |Band (b1, b2) -> (evalB b1 s) && (evalB b2 s)
  |Bor (b1, b2) -> (evalB b1 s) || (evalB b2 s)
  |Eps -> false



let rec sn_updateb = fun (p : wb) (s : state) ->
  match p with
  |MSkip -> s
  |MAssign(a,b) ->  update s a (evalB b s)
  |MSeq (w1,w2) -> sn_updateb w2 (sn_updateb w1 s)
  |MIf (b,w1,w2) ->( match (evalB b s) with
                    |true -> sn_updateb w1 s
                    |false -> sn_updateb w2 s )
  |MWhile (b,w) as i -> (match (evalB b s) with
                        |true -> let s1 = (sn_updateb w s) in sn_updateb i s1
                        |false -> s )

let s = [true;true;false;true]

let (w,l) = pr_Fb (list_of_string "a:=!(0+1);c:=(0.1);d:=((a+(b.0))+(!1))" ) in sn_updateb w s
let (w,l) = pr_Fb (list_of_string "a:=1;b:=1;c:=1;w(a){i(!c){b:=0;a:=b}{b:=0;c:=b}}") in sn_updateb w s
let (w,l) = pr_Fb (list_of_string "a:=1;b:=1;c:=1;w(a){i(a){c:=0;a:=b;i(c){c:=0;a:=b}{b:=0;a:=0}c:=0}{b:=0;c:=a}}") in sn_updateb w s


           (** 2.4 Preuves sur la SOS (option 2) ***)
