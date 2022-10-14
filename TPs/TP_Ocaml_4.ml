(*4 File et file à priorités*)
(*4.1 Structure de file*)

type 'a file = 'a list

let est_file_vide : 'a file -> bool = fun f -> match f with
                                                 |[] -> true
                                                 |_ -> false

let file_vide = []

let enfile : 'a -> 'a file -> 'a file =
  fun a f ->
  match f with
  |[] -> a::[]
  |b::c -> a::b::c

let rec defile: 'a file -> ('a * 'a file) =
  fun f ->
  match f with
  |[] -> failwith "empty"
  |x::[] -> (x,[]) 
  |i::l -> let (x,y) = defile l in (x,i::y)

let test = [1;5;88;85;64] ;;

enfile 6 test;;

defile test;;
 let test2 = [];;
defile test2;;



