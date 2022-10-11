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
let rec aux : 'a list -> 'a -> 'a list -> 'a * 'a list = fun la a lb -> match la with
                                                                         |[] -> (a, lb)
                                                                         |h::b -> if h<a then aux b h (a::lb) else aux b a (h::lb)
let rec trouve_min_i: 'a list -> ('a * 'a list) = fun k -> match k with
                                                         |[] -> (max_int, [])
                                                         |x::y -> (min_list k, (split k (min_list k)))

let rec trouve_min: ('a -> 'a -> bool) -> 'a list -> 'a * 'a list = fun (f:'a -> 'a -> bool) (l:'a list) -> match l with
                                                                           |[] -> (max_int,[])
                                                                           |x::[] -> (x,[])
                                                                           |x::l -> let (y,l1) = trouve_min f l in if f x y then (x, y::l1) else (y, x::l1)

let rec trouve_min_i_recc: 'a list -> int * int list = fun l -> trouve_min (<) l

let _ = assert (trouve_min_i a = (1,[2;3;4;5;6]));;

trouve_min_i_recc a;;

trouve_min (<) a

(*Exercice 3.2*)

let rec tri_selection : ('a -> 'a -> bool) -> 'a list -> 'a list = fun (f:'a -> 'a -> bool) (l:'a list) -> let (a,b) = trouve_min f l in match l with
                                                                                                                                     |[] -> []
                                                                                                                                     |h::b -> tri_selection (f h a) b

let tri_selection_i: 'a list -> 'a list = fun l -> tri_selection (<) l;;

tri_selection (<) b

(*Exercice 3.3*)

let rec liste_alea: 'a -> 'a list = fun a -> let n = Random.int 20000000 in match a with
                                                                             |0 -> []
                                                                             |i -> n::(liste_alea (i-1))

(*Exercice 3.4*)

let liste1 = liste_alea 8
let liste2 = liste_alea 14

let time f x =
    let t = Sys.time() in
    let fx = f x in
    Printf.printf "Execution time: %fs\n" (Sys.time() -. t);
    fx
