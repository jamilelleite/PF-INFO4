(* Analyse descendante récursive sur une liste avec des combinateurs *)
(* Version spécialisée à des terminaux qui sont des caractères,
   pour éviter d'encombrer la compréhension du mécanisme avec un
   typage plus général mais plus lourd.
   Dans toute la suite, les listes sont implicitement des
   listes de caractères. *)

(* Utilitaire pour les tests *)

let list_of_string s =
  let n = String.length s in
  let rec boucle i =
    if i = n then [] else s.[i] :: boucle (i+1)
  in boucle 0

(* ============================================================ *)
(* Échauffement : combinateurs d'analyseurs purs                *)
(* ------------------------------------------------------------ *)

(* Toutes les notions grammaticales (terminal, non-terminal,
   règle de grammaire) se traduisent par des fonctions
   d'analyse prenant en entrée une liste [l] de terminaux (ici des
   caractères) et rendant une sous-liste de [l], autrement dit
   [l] privée d'un préfixe, où ce dernier correspond à une séquence
   de terminaux et de non-terminaux.
 *)

(* Le type des aspirateurs de listes de caratères  *)
type analist = char list -> char list

exception Echec

(* terminal constant *)
let terminal c : analist = fun l -> match l with
  | x :: l when x = c -> l
  | _ -> raise Echec

(* terminal conditionnel *)
let terminal_cond (p : 'term -> bool) : analist = function
  | x :: l when p x -> l
  | _ -> raise Echec

(* non-terminal vide *)
let epsilon : analist = fun l -> l

(* Composition séquentielle : a suivi de b *)
let (-->) (a : analist) (b : analist) : analist =
  fun l -> let l = a l in b l

(* Choix entre a ou b *)
let (-|) (a : analist) (b : analist) : analist =
  fun l -> try a l with Echec -> b l

(* OBSERVATION CLÉ 0 :
   --> est le code déjà vu pour la composition séquentielle ;
   l'intérêt d'utiliser des combinateurs est d'éviter de 
   nommer les listes manipulées de façon sous-jacente,
   d'où une expression très concise.
 *)
                                              
(* ---------------------------------- *)
(* Grammaire non récursive *)

(*
    S0  ::=  'x'
    S   ::=  '(' S0 ')'  |  'x'
*)

let p_S0 : analist = terminal 'x'

let p_S : analist =
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

let rec p_S : analist = fun l ->  l |>
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


let rec p_S : analist = fun l ->  l |>
     (terminal '('  -->  p_S  -->  terminal ')')
  -| epsilon

(* Il faut mettre epsilon en second pour effectuer l'analyse
   du plus grand préfixe correspondant à la grammaire *)

let test s = p_S (list_of_string s)
let _ = test "((()))abc"
let _ = test "abc"
let _ = test "((x))abc"
let _ = try test "()abc" with Echec -> list_of_string "Echec"
       
(* ==================================================================== *)
(* Combinateurs d'analyseurs avec calcul supplémentaire (ex. un AST)    *)
(* -------------------------------------------------------------------- *)

(* On appelle fonction d'analyse, ou analyseur, ou de façon plus imagée
   "aspirateur", une fonction prenant en argument une liste et rendant
   un résultat comprenant une liste éventuellement accompagnée d'autres
   informations ;
   la liste en sortie est la liste en entrée privée d'un préfixe
   correspondant à une séquence constituée terminaux et de
   non-terminaux.
   Nous utiliserons deux types d'analyseurs :
   - analist, vu ci-dessus, le type des analyseurs non informatifs ;
   - 'res canalist, que nous présentons maintenant, le type des analyseurs
     rendant un contenu informatif supplémentaire.
 *)

(* Le type des aspirateurs de listes qui rendent un résultat de type 'res *)
type 'res ranalist = char list -> 'res * char list

(* Observer la similitude entre analist et 'res canalist :
   ce sont des fonctions ayant en entrée une liste de terminaux.
 *)
(*
   De même que pour l'échauffement, on s'arrange pour que toute la
   programmation s'effectue par combinaison d'analyseurs,
   ce qui va nécessiter :
   - des combinateurs entre analyseurs de type analist ou 'res ranalist,
     rendant un analyseur de type analist ou 'res ranalist ;
   - l'expression du retour d'un résultat de type 'res, sous forme
     d'un analyseur de type 'res ranalist.
 *)

(* Epsilon informatif, qui rend une fonction d'analyse informative avec comme
   information en sortie l'argument donné en entrée.
   La liste analysée est rendue inchangée ; d'un point de vue grammatical,
   cela correspond à la consommation d'un ε en préfixe.contents
 *)
let epsilon_res (info : 'res) : 'res ranalist =
  fun l -> (info, l)

(* Terminal conditionnel avec résultat *)
(* [f] ne retourne pas un booléen mais un résultat optionnel,
   pouvant être vu comme un booléen enrichi en cas de succès
   (Some y au lieu de true). *)
let terminal_res (f : char -> 'res option) : 'res ranalist =
  fun l -> match l with
  | x :: l -> (match f x with Some y -> y, l | None -> raise Echec)
  | _ -> raise Echec


(* Les combinateurs précédents --> et -| prenaient en argument
   des fonctions de type analist. On les adapte à ranalist en utilisant
   parfois un code identique. *)

(* Choix entre a ou b informatifs *)
let (+|) (a : 'res ranalist) (b : 'res ranalist) : 'res ranalist =
  fun l -> try a l with Echec -> b l

(* Composition séquentielle
   - d'un analyseur informatif a
   - avec b, une fonction à 2 arguments ;
     celle-ci est vue comme une fonction à 1 argument
     et qui rend un analyseur.
*)
(* a sans résultat suivi de b donnant un résultat *)
let ( -+>) (a : analist) (b : 'res ranalist) : 'res ranalist =
  fun l -> let l = a l in b l

(* a rendant un résultat suivi de b sans résultat *)
let (+->) (a : 'res ranalist) (b : analist) : analist =
  fun l -> let (x, l) = a l in b l

(* a rendant un résultat suivi de b rendant un résultat *)
let (++>) (a : 'resa ranalist) (b : 'resa -> 'resb ranalist) : 'resb ranalist =
  fun l -> let (x, l) = a l in b x l

(* OBSERVATION CLÉ 1 :
   c'est le code déjà vu pour la composition d'une fonction rendant un
   couple avec une fonction curryfiée prenant deux arguments. De même
   que pour la composition --> vue ci-dessus, on continue à ne pas nommer
   les listes manipulées de façon sous-jacente, mais on va nommer les 
   arguments supplémentaires dits informatifs.
*)
                             

(* ---------------------------------- *)

(* Exemples de combinaisons d'analyseurs *)

(* Considérons un simple terminal 'V', auquel on veut associer le booléen true *)
(* L'analyseur pur correspondant serait : *)

let exemple1_pur : analist = terminal 'V'

let _ = exemple1_pur ['V'; '.'; 'a'; 'b']

(* Comme ε est élément neutre, on peut aussi prendre le suivant : *)

let exemple1_pur_avec_epsilon : analist = terminal 'V' --> epsilon

(* Fonctionnement sur une liste l en entrée

        terminal 'V'            epsilon
   l  -------------->  l1 -------------------> l1

 *)

let _ = exemple1_pur_avec_epsilon ['V'; '.'; 'a'; 'b']

(* Pour rendre une valeur, on utilise simplement, à la place de epsilon, 
   sa version informative epsilon_res : *)

let exemple1 : bool ranalist = terminal 'V' -+> epsilon_res true

(* Fonctionnement sur une liste l en entrée

        terminal 'V'        epsilon_res true
   l  -------------->  l1 -------------------> (true, l1)

 *)

let _ = exemple1 ['V'; '.'; 'a'; 'b']
let _ = try exemple1 ['8'; '.'; 'a'; 'b'] with Echec -> false, list_of_string "Echec"

(* Similaire *)
let exemple2 : bool ranalist = terminal 'F' -+> epsilon_res false

(* Choix entre les deux précédents *)
let exemple3 : bool ranalist = exemple1 +| exemple2

let _ = exemple3 ['F'; '.'; 'a'; 'b']
let _ = try exemple3 ['8'; '.'; 'a'; 'b'] with Echec -> false, list_of_string "Echec"

(* On peut composer séquentiellement exemple3 avec un
   terminal non informatif, par exemple de ponctuation *)

let exemple4 : analist = exemple3 +-> terminal '.'

let _ = exemple4 ['F'; '.'; 'a'; 'b']
let _ = try exemple4 ['V'; 'a'; 'b'] with Echec ->  list_of_string "Echec"
let _ = try exemple4 ['8'; '.'; 'a'; 'b'] with Echec -> list_of_string "Echec"

(* Mais comment récupérer le booléen b qui a été calculé par exemple3 ?
   Le type de exemple4, analist, suggère que l'on est parti sur une mauvaise piste
   et que, parmi les combinateurs séquentiels précedents, il faudrait utiliser
    ++> plutôt que +->.

   On va tout d'abord compléter terminal '.' de façon à produire un ranalist,
   dans le même esprit que exemple1. Le plus simple est la production
   d'une information constante true ou false.
  *)
let exemple5 : bool ranalist = terminal '.' -+> epsilon_res true
let exemple5' : bool ranalist = terminal '.' -+> epsilon_res false

let _ = exemple5 ['.'; 'a'; 'b']
let _ = exemple5' ['.'; 'a'; 'b']

(* On pourrait alors enchaîner exemple3 avec le code précédent. *)

let exemple6_bof : bool ranalist = exemple3 +-> terminal '.' -+> epsilon_res true
let exemple6'_bof : bool ranalist = exemple3 +-> terminal '.' -+> epsilon_res false

(* Mais l'usage de +-> indique que l'information produite par exemple3 
   a encore été perdue. *)
                             
(* OBSERVATION CLÉ 2.0 : exemple5 ou exemple5' peuvent être généralisés en une 
   FONCTION paramétrée par b, la valeur à rendre : *)

let exemple5_fct : bool -> bool ranalist = fun b -> terminal '.' -+> epsilon_res b

let _ = exemple5_fct true  ['.'; 'a'; 'b']
let _ = exemple5_fct false ['.'; 'a'; 'b']

(* OBSERVATION CLÉ 2.1 : 
   exemple5_fct, c'est-à-dire l'expression
   fun b -> terminal '.' -+> epsilon_res b
   peut-être placée à droite de ++>,
   comme indiqué par le type de b dans la définition de ++>.
   On peut écrire l'enchaînement de exemple3 et de cette expression :
*)

let exemple6 : bool ranalist =
  exemple3 ++> (fun b -> terminal '.' -+> epsilon_res b)

let _ = exemple6 ['F'; '.'; 'a'; 'b']

(* On peut même l'écrire sans parenthèses ce qui allège l'ensemble. *)

let exemple7 : bool ranalist =
  exemple3 ++> fun b -> terminal '.' -+> epsilon_res b

let _ = exemple7 ['F'; '.'; 'a'; 'b']

(* OBSERVATION CLÉ 2.2 : 
   dans exemple7 la portée du paramètre b est l'expression représentée ici
                          ___________________________
                         /                           \
   exemple3 ++> fun b -> terminal '.' +> epsilon_res b

   D'une manière générale, Les résultats x capturés par un "fun x -> "
   placé immédiatement après une composition ++> sont visibles, et peuvent
   donc être utilisés, dans toute l'expression placée à droite, notamment
   dans un epsilon_res final.

   CONSÉQUENCE PRATIQUE :
   on obtient une écriture très concise et systématique des analyseurs.
   Une séquence d'analyseurs non informatifs (typiquement des terminaux)
   T1, T2...  d'analyseurs informatifs (typiquement des non-terminaux)
   NT1, NT2, ... rendant respectivement des résultats r1, r2...,
   le tout rendant un résultat (f r1 r2...), s'écrit donc simplement
     T1 -+> ... NT1 ++> fun r1 -> ... T2 -+> ... NT2 ++> fun r2 -> ...
        epsilon_res (f r1 r2...)

 *)

(* Résumé du fonctionnement de exemple7 sur une liste l0 en entrée

       exemple3
  l0 -----------> (true, l1)
  
                  b lié à  true
                  \___________/        terminal '.'       epsilon_res b
                       ++>       l1  --------------> l2 ---------------> (b, l3)
  

 *)

(* Déroulement du calcul
Rappel :       a ++> b =      fun l -> let (x, l) = a l in b x l

Donc
    exemple7  =  exemple3  ++>  (fun b -> terminal '.' -+> epsilon_res b)
              =  fun l -> let (x, l) = exemple3 l in
                          (fun b -> terminal '.' -+> epsilon_res b) x l

Calcul de  exemple7 ['F'; '.'; 'a'; 'b']

On calcule d'abord
           exemple3 ['F'; '.'; 'a'; 'b'] = (false, ['.'; 'a'; 'b'])
Donc let (x, l) = exemple3 ['F'; '.'; 'a'; 'b']
     lie x à false
      et l à ['.'; 'a'; 'b'])

Ensuite
                   (fun b -> terminal '.'  -+>  epsilon_res b) x l
   =               (fun b -> terminal '.'  -+>  epsilon_res b) false ['.'; 'a'; 'b']
   =                        (terminal '.'  -+>  epsilon_res false) ['.'; 'a'; 'b']
   =   ['.'; 'a'; 'b']  |>  (terminal '.'  -+>  epsilon_res false)
   =                          ['a'; 'b']   |>   epsilon_res false
   =                                            (false, ['a'; 'b']

*)

(* ---------------------------------- *)
(*
    S   ::=  '(' S ')'  |  'x'
*)

type ast = Fin | Pa of ast

let rec p_S : ast ranalist = fun l ->  l |>
     (terminal '('  -+>  p_S  ++>  (fun a -> (terminal ')'  -+>  epsilon_res (Pa (a)))))
  +| (terminal 'x'  -+>  epsilon_res Fin)

(* En enlevant les parenthèses *)
let rec p_S : ast ranalist = fun l ->  l |>
     (terminal '('  -+>  p_S  ++>  fun a -> terminal ')'  -+>  epsilon_res (Pa (a)))
  +| (terminal 'x'  -+>  epsilon_res Fin)

let test s = p_S (list_of_string s)
let _ = test "(((x)))a(bc"
let _ = test "xabc"
let _ = try test "()abc" with Echec -> Fin, list_of_string "Echec"

(* ----------------------------- *)
(* Exemple avec récursion mutuelle

  B  ::=  (B)  |  C
  C  ::=  x    |  yC   |  zBC  |  ε

 *)

type boite = Emb of boite | Cont of contenu
and contenu = X | Y of contenu | Z of boite * contenu | Quedalle

let rec p_B : boite ranalist = fun l ->  l |>
    (terminal '('  -+>  p_B  ++>  fun b -> terminal ')'  -+>  epsilon_res (Emb (b)))
 +| (p_C  ++>  fun c -> epsilon_res (Cont (c)))

and p_C : contenu ranalist = fun l ->  l |>
    (terminal 'x'  -+>  epsilon_res X)
 +| (terminal 'y'  -+>  p_C  ++>  fun c -> epsilon_res (Y (c)))
 +| (terminal 'z'  -+>  p_B  ++>  fun b -> p_C  ++>  fun c -> epsilon_res (Z (b, c)))
 +| epsilon_res Quedalle

(* Remarquer que dans la dernière ligne, le résultat rendu par p_B est capturé
   par b, puis le résultat rendu par p_C est capturé par c, ce qui permet de rendre
   Z (b, c) à la fin.  *)

let _ = p_B (list_of_string "((yz(yyx)yx))a")
let _ = p_B (list_of_string "((yz(yyx)y))a")
let _ = p_B (list_of_string "(())a")

(* ----------------------------- *)
(*

   OBSERVATION CLÉ 2.3 :
   dans une expression comme

     T1 -+> ... NT1 ++> fun r1 -> ... T2 -+> ... NT2 ++> fun r2 -> ...
                                  ************************************

   r1 est disponible dans toute la zone soulignée par des *, il peut donc
   éventuellement servir bien avant le epsilon_res final, dans des expressions
   passées en argument à NT2, NT3, etc. si besoin. 
   Exemple : calcul d'un entier par le schéma de Horner.

  *)
