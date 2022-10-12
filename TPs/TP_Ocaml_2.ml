(*Jamile Lima Leite*)
(*Kemgne Nasah Darryl Jordan*)


(*Echauffement*)
let rec somme_all: 'a list -> int = fun a -> match a with
                                             |[] -> 0
                                             |x::y -> x + (somme_all y)
let rec all_pos: 'a list -> bool = fun a -> match a with
                                            |[] -> true
                                            |x::y -> if(x > -1) then all_pos y else false
let rec add_list: 'a list -> 'a -> 'a list = fun a b -> match a with
                                                        |[] -> b::[]
                                                        |x::y -> x::add_list y b
let rec concat: 'a list -> 'a list -> 'a list = fun a b -> match a with
                                                           |[] -> b
                                                           |x::[] -> x::b
                                                           |x::y -> x::concat y b
let a = [1;2;3;1;4;5;6]
let b = [12;52;65;84;36;69;42;95;11]

(*Auxiliare*)

let min: 'a -> 'a -> 'a = fun a b -> if (a < b) then a else b

let rec min_list: 'a list -> 'a = fun l -> match l with
                                           |[] -> max_int
                                           |x::y -> min x (min_list y)
 let rec splitleft : 'a list -> 'a -> 'a list = fun l x -> match l with
                                                    |[] -> failwith "Cette élément n'est pas dans la liste"
                                                    |y::s -> if x = y
                                                                  then [] else y::splitleft s x 
 let rec splitright : 'a list -> 'a -> 'a list = fun l x -> match l with
                                                     |[] -> failwith "Cette élément n'est pas dans la liste"
                                                     |y::s -> if x = y then s else splitright s x
 
 let split: 'a list -> 'a -> 'a list = fun x a -> let l1 = splitleft x a in
                                                    let l2 = splitright x a in
                                                    concat l1 l2
  (*Fonctions arbre*)
 type abin = Feuille | Noeuds of abin*int*abin
  let rec insert : abin -> int -> abin = fun a b -> match a with
                                                   |Feuille -> Noeuds(Feuille, b, Feuille)
                                                   |Noeuds(g,n,d) -> if(b>n) then Noeuds(g,n,insert d b) else Noeuds(insert g b,n,d)
  let rec insertABR : 'a list -> abin -> abin = fun l a -> match l with
                                                     |[] -> a
                                                     |x::t -> insertABR t (insert a x)
  let rec insertList: 'a list -> int -> 'a list = fun l a -> match l with
                                                        |[] -> a::[]
                                                        |i::x -> i::insertList x a

 let rec concatliste : 'a list -> 'a list -> 'a list = fun l p -> match l with
                                                            |[] -> p
                                                            |x::[] -> x::p
                                                            |s::o -> s::concatliste o p
 
 let rec parcour : abin -> 'a list = fun a -> match a with
                                             |Feuille -> []
                                             |Noeuds(g,n,d) -> concatliste (insertList (parcour g) n) (parcour d)
 let triABR: 'a list -> 'a list = fun l -> match l with
                                       |[] -> []
                                       |x::k -> parcour (insertABR k Feuille)
 (*Exercice 3.1*)
 let rec trouve_min_i: 'a list -> 'a * 'a list =
   fun l ->
   match l with
   | [] -> (max_int, []) (*pas possible, liste non vide*)
   | head::[] -> (head, [])
   | head::body ->
      let (a, l) = trouve_min_i body in
      if head < a then (head, a::l) else (a, head::l);;

 trouve_min_i b;;

  let rec trouve_min: ('a -> 'a -> bool) -> 'a list -> 'a * 'a list =
   fun f l ->
   match l with
   | [] -> (max_int, []) (*pas possible, liste non vide*)
   | head::[] -> (head, [])
   | head::body ->
      let (a, l) = trouve_min f body in
      if f head a then (head, a::l) else (a, head::l);;

  trouve_min (<) b;;
  trouve_min (>) a;;

(*Exercice 3.2*)

let rec tri_selection : ('a -> 'a -> bool) -> 'a list -> 'a list =
  fun f l ->
  match l with
  | [] -> []
  | _ -> let (min, newl) = trouve_min f l in
             min::(tri_selection f newl);;

tri_selection (<) a;;
tri_selection (>) b;;

let tri_selection_i: 'a list -> 'a list = fun l -> tri_selection (<) l;;

tri_selection_i a;;

(*Exercice 28*)

let rec liste_alea: 'a -> 'a list = fun a -> let n = Random.int 20000000 in match a with
                                                                             |0 -> []
                                                                             |i -> n::(liste_alea (i-1))


(*Exercice 3.4*)

let liste1 = liste_alea 8
let liste2 = liste_alea 14

let time f x =
    let t = Sys.time() in
    let fx = f x in
    Printf.printf "Execution time: %f s\n" (Sys.time() -. t);
    fx

let time_arbre = time triABR liste1

let time_liste = time tri_selection_i liste1

(*Exercice 3.5*)

let rec renv_aux: 'a list -> 'a list -> 'a list = fun l1 l2 -> match l2 with
                                                           |[] -> l1
                                                           |x::y -> renv_aux (x::l1) y

let renv: 'a list -> 'a list = fun l -> renv_aux [] l


(*Exercice 3.6*)
let rec renv_app: 'a list -> 'a list -> 'a list = fun l1 l2 -> match l1 with
                                                           |[] -> l2
                                                           |h::t -> renv_app (h::l2) t

(*En utilisant renv_app avec une liste vide*)

(*Exercice 3.7*)

let liste10000 = liste_alea 10000

let perf_renv = time renv liste10000

let perf_renv_app = time renv_app liste10000 liste1

(*Exercice 3.8*)
let append: 'a list -> 'a list -> 'a list = fun  l1 l2 -> l1@l2

let liste3 = liste_alea 20

let listee = time append liste1 (append liste2 liste3)
let listee' = time append (append liste1 liste2) liste3

(*Excercice 3.9*)

let rec dromadaire: 'a list -> ('a -> 'a -> bool) -> 'a =
  fun l comp ->
  match l with
  | head::body -> let s = dromadaire body comp in
                  if comp head s then head else s
  | [] -> if comp 0 max_int then max_int else min_int;;

dromadaire a (<);;
dromadaire a (>);;
dromadaire b (<);;
dromadaire b (>);;

(*Exercice 3.10*)

let rec chameau_i: 'a list -> ('a -> 'a -> bool) -> ('a * 'a) =
  fun l comp ->
  match l with
  | [] -> if comp 0 max_int then (max_int, max_int) else (min_int, min_int)
  | head::body -> let (b, s) = chameau_i body comp in (*the first element in the tuple is*)
                  if comp head b then               (*going to be the bigger/smaller element*)
                    (head, b)
                  else
                    if comp head s then
                      (b, head)
                    else
                      (b, s);;

let a = [1;2;3;1;4;5;6];;
let b = [12;52;65;84;36;69;42;95;11];;

chameau_i a (>);;
chameau_i b (<);;

let chameau = fun l -> chameau_i l (>);;

chameau a;;
chameau b;;
