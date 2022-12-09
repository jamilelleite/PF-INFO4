(* Analyse descendante récursive sur une liste avec des combinateurs *)

(* Utilitaire pour les tests *)

let list_of_string s =
  let n = String.length s in
  let rec boucle i =
    if i = n then [] else s.[i] :: boucle (i+1)
  in boucle 0

type 'a lazylist = unit -> 'a contentsll
and 'a contentsll = Nil | Cons of 'a * 'a lazylist

let rec range i j = fun () ->
  if (i=j) then Nil
  else Cons(i, range(i+1) j)

let rec (get: int -> 'a lazylist -> 'a list) = fun n l -> 
  match l() with
  | Nil -> []
  | Cons(a,m) -> if (n>1) then a::(get (n-1) m)
                 else a::[]

(* liste fini *)
let lf1 = range 5 10 
let _ = get 10 lf1
(* list infini *)
let li1 = range 20 0
let li2 = li1()
let _ = get 10 li1

(* Le type des aspirateurs (fonctions qui aspirent le préfixe d'une liste) *)
type 'term analist = 'term lazylist -> 'term lazylist

exception Echec

(* terminal constant *)
let terminal (c: 't): 't analist = function
  | unit -> match unit() with
            | Cons(x,l) -> if (x=c) then l else raise Echec
            | Nil -> raise Echec
                
(* terminal conditionnel *)
let terminal_cond (p: 'term -> bool) : 'term analist = function
  | unit -> match unit() with
            | Cons(x,l) -> if (p x) then l else raise Echec
            | Nil -> raise Echec

(* non-terminal vide *)
let epsilon : 'term analist = fun l -> l

let p_5: int analist = terminal 5
let new_lf1 = p_5 lf1
let _ = get 20 new_lf1

let p_6: int analist = terminal 6

let p_20: int analist = terminal 20
let new_li1 = p_20 li1
let _ = get 5 new_li1

let ts = epsilon lf1
let _ = get 10 ts

(* ------------------------------------------------------------ *)
(* Combinateurs d'analyseurs purs *)
(* ------------------------------------------------------------ *)

(* a1 suivi de a2 *)
let (-->) (a1 : 'term analist) (a2 : 'term analist) : 'term analist =
  fun l -> let l = a1 l in a2 l

(* Choix entre a1 ou a2 *)
let (-|) (a1 : 'term analist) (a2 : 'term analist) : 'term analist =
  fun l -> try a1 l with Echec -> a2 l

let p_5_6: int analist =
  p_5 --> p_6

let p_20_21: int analist =
  (terminal 20) --> (terminal 21)

let _ = get 10 (p_20_21 li1)

let p_a: int analist = p_5_6 -| p_20_21
let _ = get 10 (p_a li1)
let _ = get 10 (p_a lf1)

(* Répétition (étoile de Kleene) *)
(* Grammaire :  A* ::=  A A* | ε *)
let rec star (a : 'term analist) : 'term analist = fun l -> l |>
  ( a --> star a ) -| epsilon

(* ------------------------------------------------------------ *)
(* Combinateurs d'analyseurs
   avec calcul supplémentaire, ex. d'un AST *)
(* ------------------------------------------------------------ *)

(* Le type des aspirateurs qui, en plus, rendent un résultat *)
type ('res, 'term) ranalist = 'term lazylist -> 'res * 'term lazylist

(* Un epsilon informatif *)
let epsilon_res (info : 'res) : ('res, 'term) ranalist =
  fun l -> (info, l)

(* Terminal conditionnel avec résultat *)
(* [f] ne retourne pas un booléen mais un résultat optionnel *)
let terminal_res (f : 'term -> 'res option) : ('res, 'term) ranalist =
  fun l -> match l() with
  | Cons(x, l) -> (match f x with Some y -> y, l | None -> raise Echec)
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

type aexp =
  | Const of int
  | Amu of aexp * aexp

let pr_5: (aexp, int) ranalist = terminal 5 -+> epsilon_res (Const 5)
let pr_6: (aexp, int) ranalist = terminal 6 -+> epsilon_res (Const 6)
let pr_20: (aexp, int) ranalist = terminal 20 -+> epsilon_res (Const 20)
let pr_21: (aexp, int) ranalist = terminal 21 -+> epsilon_res (Const 21)

