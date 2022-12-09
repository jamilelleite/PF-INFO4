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

(* Le type des aspirateurs (fonctions qui aspirent le préfixe d'une liste) *)
type 'term analist = 'term list -> 'term list

type 'term panalist = 'term lazylist -> 'term lazylist

exception Echec

(* terminal constant *)
let terminal (c : 't) : 't analist = function
  | x :: l when x = c -> l
  | _ -> raise Echec

let pterminal (c: 't): 't panalist = function
  | unit -> match unit() with
            | Cons(x,l) -> if (x=c) then l else raise Echec
            | Nil -> raise Echec
                
(* terminal conditionnel *)
let terminal_cond (p : 'term -> bool) : 'term analist = function
  | x :: l when p x -> l
  | _ -> raise Echec

let pterminal_cond (p: 'term -> bool) : 'term panalist = function
  | unit -> match unit() with
            | Cons(x,l) -> if (p x) then l else raise Echec
            | Nil -> raise Echec

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
