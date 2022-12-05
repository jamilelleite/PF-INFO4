
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


(*
C ::= '0' | '1'
V ::= 'a' | 'b' | 'c' | 'd'
A ::= C | V

E::= EN 
     | T
EN::= E '+' T
T::= TN
     | FN
TN::= T '.' FN
FN::= '!' FN
     | A
     | '(' E ')'

F::= V ':=' FN H
     | 'i(' FN '){' I '}{' I '}' I
     | 'w(' FN '){' I '}' I
H::= ; F
     | eps
I::= F
     | eps

 *)

type bvar =
  | A
  | B
  | C
  | D

type bexp =
  | Exp of bvar
  | F (*false*)
  | T (*true*)
  | Bnot of bexp
  | Band of bexp * bexp
  | Bor of bexp * bexp
  | Eps

type wb =
  | MSkip 
  | MAssign of bvar * bexp
  | MSeq of wb * wb
  | MIf of bexp * wb * wb
  | MWhile of bexp * wb

let pr_V: (bvar, char) ranalist =
  
  (terminal 'a' -+> epsilon_res (A))
  +| (terminal 'b' -+> epsilon_res (B))
  +| (terminal 'c' -+> epsilon_res (C))
  +| (terminal 'd' -+> epsilon_res (D))

let pr_C: (bexp, char) ranalist =
  (terminal '0' -+> epsilon_res (F))
+| (terminal '1' -+> epsilon_res (T))

let _ = pr_V (list_of_string "a:=0")

let pr_A: (bexp, char) ranalist =
  (pr_C)
  +| (pr_V ++> fun a -> epsilon_res (Exp a))

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
  +| (pr_A)
+| (terminal '(' -+> pr_E ++> fun a -> terminal ')' -+> epsilon_res a)

let rec pr_F: (wb, char) ranalist = fun l -> l |>
  (pr_V ++> fun a -> terminal ':' --> terminal '=' -+> pr_FN ++> fun b -> pr_H ++> fun c -> (if (c=MSkip) then  epsilon_res (MAssign(a, b)) else epsilon_res (MSeq((MAssign(a, b)),c)) ))
  +| (terminal 'i' --> terminal '(' -+> pr_FN ++> fun a -> terminal ')' --> terminal '{' -+> pr_I ++> fun b -> terminal '}' --> terminal '{' -+> pr_I ++> fun c -> terminal '}' -+> pr_I ++> fun d ->(if(d=MSkip) then epsilon_res (MIf (a, b, c)) else epsilon_res (MSeq(MIf (a, b, c), d))))
  +| (terminal 'w' --> terminal '(' -+> pr_FN ++> fun a -> terminal ')' --> terminal '{' -+> pr_I ++> fun b -> terminal '}' -+> pr_I ++> fun d -> (if(d=MSkip) then epsilon_res (MWhile(a,b)) else   epsilon_res (MSeq(MWhile(a,b), d))) )
and pr_H: (wb, char) ranalist = fun l -> l |>
  (terminal ';' -+> pr_F ++> fun a -> epsilon_res (a))
  +| epsilon_res MSkip
and pr_I: (wb, char) ranalist = fun l -> l |>
  (pr_F)
  +| epsilon_res MSkip

let _ = pr_F (list_of_string "a:=1;b:=1;c:=1;w(a){i(!a){c:=0;a:=b;i(c){c:=0;a:=b}{b:=0;c:=a}c:=0}{b:=0;c:=a}}")

let _ = pr_F (list_of_string "a:=!(0+1);c:=(0.1);d:=((a+(b.0))+(!1))" )
