(* Analyse descendante récursive sur une liste avec des combinateurs *)

(* Utilitaire pour les tests *)

let list_of_string s =
  let n = String.length s in
  let rec boucle i =
    if i = n then [] else s.[i] :: boucle (i+1)
  in boucle 0

(* Le type des fonctions qui épluchent une liste de terminaux *)
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

(* a suivi de b *)
let (-->) (a : 'term analist) (b : 'term analist) : 'term analist =
  fun l -> let l = a l in b l

(* Choix entre a ou b *)
let (-|) (a : 'term analist) (b : 'term analist) : 'term analist =
  fun l -> try a l with Echec -> b l

(* Répétition (étoile de Kleene) *)
(* Grammaire :  A* ::=  A A* | ε *)
let rec star (a : 'term analist) : 'term analist = fun l -> l |>
  ( a --> star a ) -| epsilon

let _ = star (terminal 'x') (list_of_string "xxx-reste")

(* ---------------------------------- *)
(* Grammaire non récursive *)

(*
    S0  ::=  'x'
    S   ::=  '(' S0 ')'  |  'x'
*)

let p_S0 : char analist = terminal 'x'

let p_S : char analist =
    (terminal '('  -->  p_S0  -->  terminal ')')
 -| (terminal 'x')

(* Tests *)

let test s = p_S (list_of_string s)
let _ = test "(x)abc"
let _ = test "xabc"

(* ---------------------------------- *)
(* Grammaire récursive *)

(*
    S   ::=  '(' S ')'  |  'x'
*)


(*
   En OCaml, x |> f est une autre notation de f x.
   Le let rec impose l'explicitation d'au moins un argument,
   d'où le démarrage par fun l -> l |>
*)

let rec p_S : char analist = fun l ->  l |>
     (terminal '('  -->  p_S  -->  terminal ')')
  -| (terminal 'x')

let test s = p_S (list_of_string s)
let _ = test "(((x)))abc"
let _ = test "xabc"
let _ = test "((x))abc"
let _ = test "()abc"

(* Variante avec ε
    S   ::=  '(' S ')'  |  ε
*)


let rec p_S : char analist = fun l ->  l |>
     (terminal '('  -->  p_S  -->  terminal ')')
  -| epsilon

(* Il faut mettre epsilon en second pour effectuer l'analyse
   du plus grand préfixe correspondant à la grammaire *)

let test s = p_S (list_of_string s)
let _ = test "((()))abc"
let _ = test "abc"
let _ = test "((x))abc"
let _ = test "()abc"

(* ------------------------------------------------------------ *)
(* Combinateurs d'analyseurs
   avec calcul supplémentaire, ex. d'un AST *)
(* ------------------------------------------------------------ *)

(* Le type des fonctions qui épluchent une liste et rendent un résultat *)
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

(* a sans résultat suivi de b donnant un résultat *)
let ( -+>) (a : 'term analist) (b : ('res, 'term) ranalist) :
      ('res, 'term) ranalist =
  fun l -> let l = a l in b l

(* a rendant un résultat suivi de b rendant un résultat *)
let (++>) (a : ('resa, 'term) ranalist) (b : 'resa -> ('resb, 'term) ranalist) :
      ('resb, 'term) ranalist =
  fun l -> let (x, l) = a l in b x l

(* a rendant un résultat suivi de b sans résultat *)
let (+->) (a : ('res, 'term) ranalist) (b : 'res -> 'term analist) :
      'term analist =
  fun l -> let (x, l) = a l in b x l

(* Choix entre a ou b informatifs *)
let (+|) (a : ('res, 'term) ranalist) (b : ('res, 'term) ranalist) :
      ('res, 'term) ranalist =
  fun l -> try a l with Echec -> b l

(* Répétition (étoile de Kleene) *)
(* Grammaire :  A* ::=  A A* | ε *)
(* List.fold_right style *)
let star_res (f : 'r -> 's -> 's) (s0 : 's) (a : ('r, 'term) ranalist) : ('s, 'term) ranalist =
  let rec sa = fun l -> l |>
    ( a ++> fun r -> sa ++> fun rs -> epsilon_res (f r rs)) +| epsilon_res s0
  in sa

let _ = star_res (+) 0 (terminal 'x' -+> epsilon_res 1) (list_of_string "xxx-reste")

(* Critique (comme pour les fold de OCaml) :
  le code de star_res est simple, mais son utilisation est délicate
  - deux types 'r et 's
  - deux arguments f et s0 en plus du reste
  - deux arguments et un résultat dans f, avec quels types ?
 --> beaucoup d'occasions de se perdre
 *)

(* Adoptons des pipelines à la unix, c'est plus simple *)

let (<<) f g = fun x -> f (g x)
let (>>) f g = fun x -> g (f x)

(* Pipeline right to left*)
let star_pipe_R2L (a : ('r -> 'r, 'term) ranalist) : ('r -> 'r, 'term) ranalist =
  let rec a_star = fun l ->
    ( ( a ++> fun f -> a_star ++> fun f_star -> epsilon_res (f << f_star) )
      +|
        epsilon_res (fun x -> x)
    ) l
  in a_star

let star_R2L (a : ('r -> 'r, 'term) ranalist) (r0 : 'r) : ('r, 'term) ranalist =
  star_pipe_R2L a ++> fun f -> epsilon_res (f r0)

(* Special case: building lists *)
let star_list (a : ('a, 'term) ranalist) : ('a list, 'term) ranalist =
  star_R2L (a ++> fun x -> epsilon_res (fun l -> x :: l)) []

(* Pipeline left to right*)
let star_pipe_L2R (a : ('r -> 'r, 'term) ranalist) : ('r -> 'r, 'term) ranalist =
  let rec a_star = fun l ->
    ( ( a ++> fun f -> a_star ++> fun f_star -> epsilon_res (f >> f_star) )
      +|
        epsilon_res (fun x -> x)
    ) l
  in a_star

let star_L2R (r0 : 'r) (a : ('r -> 'r, 'term) ranalist) : ('r, 'term) ranalist =
  star_pipe_L2R a ++> fun f -> epsilon_res (r0 |> f)

(* Exemples *)

let chiffre : (int, char) ranalist =
  let valchiffre : char -> int option = fun c ->
    match c with
    | '0' .. '9' -> Some (Char.code c - Char.code '0')
    |_ -> None
  in terminal_res valchiffre

let lettre : (char, char) ranalist =
  let char_lettre : char -> char option = fun c ->
    match c with
    | 'a' .. 'z' -> Some c
    |_ -> None
  in terminal_res char_lettre

let rec lettres : (char list, char) ranalist = fun l -> l |>
  (lettre ++> fun x -> lettres ++> fun l -> epsilon_res (x :: l)) +|
  epsilon_res []

(*c Version avec combinateur *)
let lettres : (char list, char) ranalist = star_list lettre
let cons_lettre : (char list -> char list, char) ranalist = lettre ++> fun c -> epsilon_res (fun l -> c :: l)

let _ = star_list (terminal 'x' -+> epsilon_res 1) (list_of_string "xxx-reste")
let _ = (lettre ++> fun c -> terminal ',' -+> star_list lettre ++> fun l -> epsilon_res (c :: l))
        (list_of_string "a,bcd-reste")

(* ---------------------------------- *)
(*
    S   ::=  '(' S ')'  |  'x'
*)

type ast = Fin | Pa of ast

let rec p_S : (ast, char) ranalist = fun l ->  l |>
     (terminal '('  -+>  p_S  ++>  (fun a -> terminal ')'  -+>  epsilon_res (Pa (a))))
  +| (terminal 'x'  -+>  epsilon_res Fin)

let test s = p_S (list_of_string s)
let _ = test "(((x)))a(bc"
let _ = test "xabc"
let _ = test "()abc"

(* ---------------------------------- *)
(* Exemple avec récursion mutuelle

  B  ::=  (B)  |  C
  C  ::=  x    |  yC   |  zBC  |  ε

 *)

type boite = Emb of boite | Cont of contenu
and contenu = X | Y of contenu | Z of boite * contenu | Quedalle

let rec p_B : (boite, char) ranalist = fun l ->  l |>
    (terminal '('  -+>  p_B  ++>  fun b -> terminal ')'  -+>  epsilon_res (Emb (b)))
 +| (p_C  ++>  fun c -> epsilon_res (Cont (c)))

and p_C : (contenu, char) ranalist = fun l ->  l |>
    (terminal 'x'  -+>  epsilon_res X)
 +| (terminal 'y'  -+>  p_C  ++>  fun c -> epsilon_res (Y (c)))
 +| (terminal 'z'  -+>  p_B  ++>  fun b -> p_C  ++>  fun c -> epsilon_res (Z (b, c)))
 +| epsilon_res Quedalle

let _ = p_B (list_of_string "((yz(yyx)yx))a")
let _ = p_B (list_of_string "((yz(yyx)y))a")
let _ = p_B (list_of_string "(())a")

