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
 (*Exercice 3.1*)
 (*Teacher's solution*)
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


(*Exercice 29*)







