
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
F::= V ':=' A
     | 'i(' A '){' WBM '}{' WBM '}'
     | 'w(' A '){' WBM '}'
WBM::= F D
D::= ';' WBM
     | eps


 *)
