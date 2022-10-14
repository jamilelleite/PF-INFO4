(*Jamile Lima Leite*)
(*Kemgne Nasah Darryl Jordan*)

(*4 File et file à priorités*)
(*4.1 Structure de file*)

type 'a file = Vide | Stack of 'a * 'a file

let est_file_vide : 'a file -> bool = fun f -> match f with
                                                 |Vide -> true
                                                 |_ -> false

let file_vide = Vide

let enfile : 'a -> 'a file -> 'a file =
  fun a f ->
  match f with
  |Vide -> Stack(a,Vide)
  |Stack(b,c) -> Stack(a,Stack(b,c))

let rec defile: 'a file -> ('a * 'a file) =
  fun f ->
  match f with
  |Vide -> failwith "empty"
  |Stack(x,Vide) -> (x,Vide) 
  |Stack(i,l) -> let (x,y) = defile l in (x,Stack(i,y))

let test = [1;5;88;85;64] ;;

let file1 = enfile 6 (enfile 4 Vide);;

enfile 6 test;;

defile test;;
 let test2 = Vide;;
defile test2;;

(*Exercice 4.2*)

let rec conversion_lf: 'a list -> 'a file =
  fun l -> match l with
           |[] -> Vide
           |h::t -> let e = conversion_lf t in Stack(h,e);;


let testfile = conversion_lf test;;

let rec conversion_fl: 'a file -> 'a list =
  fun f ->
  match f with
  |Vide -> []
  |Stack(a,b) -> let e = conversion_fl b in a::e;;

conversion_fl testfile;;

let test_file: 'a list -> bool =
  fun l ->(conversion_fl (conversion_lf l) = l);;

test_file test;;

(*Exercice 4.3*)

type 'a file2 = 'a list * 'a list

let file_vide2: 'a file2 = ([],[])

let est_file_vide: 'a file2 -> bool = fun f2 ->
  let (l1,l2) = f2 in if(l1=[] && l2=[]) then true else false

let enfiler2: 'a -> 'a file2 -> 'a file2 = fun a f2 ->
  let (l1,l2) = f2 in
  match l1 with
  |[] -> (a::[],l2)
  |h::b -> (a::h::b,l2);;

let rec insert: 'a -> 'a list -> 'a list = fun n l ->
  match l with
  |[] -> n::[]
  |h::b -> h::(insert n b);;

let rec list_reverse: 'a list -> 'a list = fun l ->
  match l with
  |[] -> []
  |h::b -> let n = list_reverse b in insert h n;;

let rec defiler2: 'a file2 -> ('a * 'a file2) = fun f2 ->
  let (l1,l2) = f2 in
  match l2 with
     |h::t -> (h,(l1,t))
     |[] -> let (a,l) = defiler2([],list_reverse l1) in (a,l);;

let file2_test = ([],[]);;
enfiler2 4 (enfiler2 3 (enfiler2 1 file2_test));;
defiler2 (enfiler2 4 (enfiler2 3 (enfiler2 1 file2_test)));;

(*Exercice 4.4*)

type 'a fap = Vide | Fap of 'a * int * 'a fap

let fap_vide: 'a fap = Vide

let est_fap_vide: 'a fap -> bool =
  fun fa -> match fa with
            |Vide -> true
            |_ -> false

let rec insere: 'a -> int -> 'a fap -> 'a fap =
  fun x p fa -> match fa with
                |Vide -> Fap (x,p,Vide)
                |Fap(a,b,c) -> Fap(a,b,insere(x,p,c))

(*Exercice 4.5*)

(*Exercice 4.6*)
