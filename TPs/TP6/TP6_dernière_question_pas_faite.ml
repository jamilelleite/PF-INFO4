(* Fichier pouvant être fourni aux étudiants après leurs tentatives *)

(* ---------------------------------------------------------------- *)
(* Pour les tests *)

let list_of_string s =
  let n = String.length s in
  let rec boucle i =
    if i = n then [] else s.[i] :: boucle (i+1)
  in boucle 0

(* ------------------------------------------------------------ *)
(* Types et primitives de base *)

(* Le type des fonctions qui épluchent une liste de caractères. *)
type analist = char list -> char list

(* Le type des fonctions qui épluchent une liste de caractères et rendent un résultat. *)
type 'res ranalist = char list -> 'res * char list

(* Idem en plus général. *)
type ('token, 'res) ranalist_gen = 'token list -> 'res * 'token list

(* L'exception levée en cas de tentative d'analyse ratée. *)
exception Echec

(* Ne rien consommer *)
let epsilon : analist = fun l -> l
(* Un epsilon informatif *)
let epsilon_res (info : 'res) : 'res ranalist =
  fun l -> (info, l)

(* Terminaux *)
let terminal c : analist = fun l -> match l with
  | x :: l when x = c -> l
  | _ -> raise Echec

let terminal_cond (p : char -> bool) : analist = fun l -> match l with
  | x :: l when p x -> l
  | _ -> raise Echec

(* Le même avec résultat *)
let terminal_res (f : 'term -> 'res option) : 'res ranalist =
  fun l -> match l with
  | x :: l -> (match f x with Some y -> y, l | None -> raise Echec)
  | _ -> raise Echec


(* ------------------------------------------------------------ *)
(* Exercice sur les suites de chiffres *)


           
(* Grammaire (U pour un-chiffre, A pour au-moins-un, C pour chiffres) :

  U ::= '0' | ... | '9'

  C ::= U C | epsilon

Que l'on décompose en :

  C ::= A | epsilon

  A ::= U C

 *)

let est_chiffre c = '0' <= c && c <= '9'

(* Consommation de tous les chiffres en préfixe *)
let rec chiffres : analist =
  let un_chiffre : analist = terminal_cond est_chiffre in
  let au_moins_un : analist = fun l ->
    let l = un_chiffre l in
    let l = chiffres l in
    l
  and aucun : analist = epsilon
  in fun l ->
     try au_moins_un l with Echec -> aucun l

let val_chiffre : char -> int option = fun c ->
  match c with
  | '0' .. '9' -> Some (Char.code c - Char.code '0')
  |_ -> None
let un_chiffre : int ranalist =
    terminal_res val_chiffre

let rec sommechiffres : int ranalist =
  let rec au_moins_un : int ranalist = fun l ->
    let x, l = un_chiffre l in
    let n, l = sommechiffres l in
    x + n, l
  and aucun : int ranalist = epsilon_res 0
  in fun l ->
     try au_moins_un l with Echec -> aucun l

(*Exercice 8.1 part 4, horner with error*)
let rec horner : int -> int ranalist =
  let rec au_moins_un :int -> int ranalist = fun a l ->
                  let x, l = un_chiffre l in
                  let n, l = horner (a*10+x) l in (n, l)
             and aucun  : int ->  int ranalist = fun a -> epsilon_res a
             in fun a l->
                try au_moins_un a l with Echec -> aucun a l

(*Exercice 8.3*)

let readfile : string -> string = fun nomfic ->
  let ic = open_in nomfic in
  really_input_string ic (in_channel_length ic)


(* Le type des fonctions qui épluchent une liste de terminaux *)
type 'term analist = 'term list -> 'term list

(* ------------------------------------------------------------ *)
(* Combinateurs d'analyseurs purs *)
(* ------------------------------------------------------------ *)

(* a suivi de b *)
let (-->) (a : analist) (b : analist) : analist =
  fun l -> let l = a l in b l

(* Choix entre a ou b *)
let (-|) (a : analist) (b : analist) : analist =
  fun l -> try a l with Echec -> b l

(* Répétition (étoile de Kleene) *)
(* Grammaire :  A* ::=  A A* | ε *)
let rec star (a : analist) : analist = fun l -> l |>
  ( a --> star a ) -| epsilon

let _ = star (terminal 'x') (list_of_string "xxx-reste")

type coul = Noir | Blanc;;

type coup = char * coul * int * int * char;;

type partie = char * int * int * char * coup list;;

type token =
  |Noir
  |Blanc
  |Lparan
  |Rparan
  |Ent of int;;

(**fonction pour reconnaitre "blanc"**)
let p_blanc: analist = fun l -> let l' = terminal 'b' l in
                                    let l' = terminal 'l' l' in
                                    let l' = terminal 'a' l' in
                                    let l' = terminal 'n' l' in
                                    let l' = terminal 'c' l' in
                                    l';;
(**fonction pour reconnaitre "noir"**)
let p_noir: analist = fun l -> let l' = terminal 'n' l in
                               let l' = terminal 'o' l' in
                               let l' = terminal 'i' l' in
                               let l' = terminal 'r' l' in
                               l';;
(**fonction pour reconnaitre une paranthèse fermée**)
let p_rpara: analist = fun l ->
  match l with
  |x::l' when x = ')' -> l'
  |_ -> raise Echec

(**fonction pour reconnaitre une paranthèse ouverte**)
let p_lpara: analist = fun l ->
  match l with
  |x::l' when x = '(' -> l'
  |_ -> raise Echec

(**fonction pour reconnaitre un entier**)
let p_ent : analist = fun l -> let (x, l') = horner 0 l in l';;

let token_here: char list -> token = fun l -> match l with
                                              |x::l' when x = '(' -> Lparan
                                              |x::l' when x = ')' -> Rparan
                                              |x::l' when x = 'n' -> let _ = p_noir l in Noir
                                              |x::l' when x = 'b' -> let _ = p_blanc l in Blanc
                                              |_ -> let (x,l') = horner 0 l in Ent x;;

                                              
let rec espaces : analist = fun l ->
  match l with
  |x::l' when x = ' ' -> espaces l'
  |_ -> l

(**Rend le premier token d'une liste commençant éventuellement par plusieurs espaces**)
let next_token: char list -> token = fun l -> token_here (espaces l)

let _ = next_token (list_of_string "blanc 2 3")

let rec tokens: char list -> token list = fun l ->
  match l with
  |x::l' when espaces l = [] -> []
  |x::l' ->  let t = next_token l in(match t with
                                     |Noir -> Noir::(tokens (p_noir (espaces l)))
                                     |Blanc -> Blanc::(tokens (p_blanc (espaces l)))
                                     |Lparan -> Lparan::(tokens (p_lpara (espaces l)))
                                     |Rparan -> Rparan::(tokens (p_rpara (espaces l)))
                                     |Ent x-> (Ent x)::(tokens (p_ent (espaces l))))
  |[] -> [];;

let _ = tokens (list_of_string " ");;

(**Question 3 Analyse Syntaxique**)

(* Analyse du non terminal P *) 
let p_P : token list -> coul*token list = fun l ->
  match l with
  |x::l' when x = Noir -> (Noir, l')
  |x::l' when x = Blanc -> (Blanc, l')
  |_ -> raise Echec

let _ = p_P [Noir;Ent 5; Ent 8; Rparan]

let p_Pouv = fun l ->
  match l with
  |x::l' when x=Lparan -> ('(', l')
  | _ -> raise Echec

let p_Pferm = fun l ->
  match l with
  |x::l' when x=Rparan -> (')', l')
  |_ -> raise Echec

let p_E = fun l ->
  match l with
  |(Ent x)::l' -> (x,l')
  |_ -> raise Echec

(* Analyseur du non terminal C *)
let p_C:token list -> coup * token list = fun l ->
  let (p1,l') = p_Pouv l in
  let (c,l') = p_P l' in
  let(n1,l') = p_E l' in
  let(n2,l') = p_E l' in
  let (p2,l') = p_Pferm l' in ((p1,c,n1,n2,p2),l');;

let _ = p_C [Lparan; Blanc; Ent 7; Ent 9; Rparan]

(** Analyseur du non terminal Cl **)

let rec p_Cl = fun l ->
  if (l=[]) then [] else let (x,l') = p_C l in x::p_Cl l'

let _ = p_Cl [Lparan;Blanc;Ent 7;Ent 6;Rparan;Lparan;Noir;Ent 4;Ent 9;Rparan]

(* Analyseur du non terminal S *)

let lit_partie: token list -> int * int * coup list = fun l ->
  let (p1,l') = p_Pouv l in
  let (n1,l') = p_E l' in
  let (n2,l') = p_E l' in
  let (_,l') = p_Pferm l' in (n1,n2,p_Cl l')

let _ = lit_partie [Lparan;Ent 19;Ent 19;Rparan;Lparan;Noir;Ent 7;Ent 9;Rparan;Lparan;Blanc;Ent 2;Ent 3;Rparan]

(* Question 4: Définir le type plateau *)
(* le plateau pourra être représenté par deux entiers représentant les dimensions du plateau et une matrice (une liste de liste de pion), une ligne du du plateau correspond à une liste de notre liste de liste de pions. On utilisera un contructeur R pour représenté les cases vide *)
type pion = N|B|R;;
type plateau = int * int * (pion list) list;;

(** Question 5 **)

exception Foo of string;;

(*Fonction intermédiare pour update une liste de pion*)

let rec update: pion list -> coul -> int -> pion list = fun l c n ->
  match l with
  |x::l' when n>0 -> x::(update l' c (n-1))
  |x::l' -> if( x=N || x=B ) then raise (Foo "la case est déjà occupée") else if (c=Noir) then N::l' else B::l'
  |[] -> update (R::[]) c n

let _ = update [N;B;R] Noir 3

(**fonction intermédiare qui retourne la liste de liste de pion qui représente l'état du plateau**)
let rec joue_coup_inter : plateau -> coup -> pion list list = fun p c ->
  let (n1,n2,l) = p in let (p1,co,m1,m2,p2) = c in if (p1='(' && p2=')' && m1<n1 && m2<n2) then
                                                     (match l with
                                                      |x::l' when m1>0 -> x::(joue_coup_inter (n1,n2,l') (p1,co,(m1-1),m2,p2))
                                                      |x::l' -> (update x co m2)::l'
                                                      |[] -> joue_coup_inter (n1,n2,[[R]]) c)

    else raise (Foo "ce coup n'est pas valide");;
                                                      
(* Fonction joue_coup qui retourne l'état complet du plateau *)

let joue_coup: plateau -> coup -> plateau = fun p c -> let (n1,n2,l) = p in (n1,n2,(joue_coup_inter p c));;

let p: plateau = (19,19,[[N;B;R;B];[B;R;N]])
let c: coup = ('(',Noir,5,6,')')
let _ = joue_coup p c


(**Question 6: Fonction resultat**)

let rec align_V6 : pion list list -> int -> pion -> pion * bool = fun pl n p ->
  if(List.length pl >= n) then (match pl with
                                |x::l when (n>0 && ((List.length x) > j)) -> let p'=(List.nth x j) in if(p' = p) then align_V6 l (n-1) j p
                                                                                                      else align_V6 l 5 j p'
                                |x::l when n = 0 -> (p, true)
                                |[] when n = 0 -> (p, true)
                                |_ -> (p,false))
  else (R,false);;

let _ = align_V6 [[B];[N];[B];[B];[B];[B];[B];[B]] 6 0 B;;







 
