
(* Exercice 1.1.1 *)


type bmvar =
  | A
  | B
  | C
  | D


type bmexp =
  | Exp of bmvar
  | O (*false*)
  | L (*true*)

type wbm =
  | MSkip 
  | MAssign of bmvar * bmexp
  | MSeq of wbm * wbm
  | MIf of bmexp * wbm * wbm
  | MWhile of bmexp * wbm



let if1_1: wbm = MAssign(C, O)

let if1_2: wbm = MAssign(A, Exp B)

let if2_1: wbm = MAssign(B, O)

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
     | 'i(' A '){' F '}{' F '}' I
     | 'w(' A '){' F '}' I
H::= ; F
     | eps
I::= F
     | eps
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
let _ = p_F (list_of_string "a:=1;b:=1;")
