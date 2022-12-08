(*LT*)



(*Exercice 2.4.2*)
(********* 1 *********)
Lemma SOS_Pcarre_2_1er_tour : SOS (Inter Pcarre_2 [0;0;1]) (Inter Pcarre_2 [1; 1; 3]).
Proof.
  eapply SOS_again. cbv.
  {eapply SOS_While.}
  eapply SOS_again.
  {eapply SOS_If_true. cbn. reflexivity.}
  eapply SOS_again.
  {cbv. apply SOS_Seqi. apply SOS_Seqf. apply SOS_Assign.}
  eapply SOS_again.
  {cbv. apply SOS_Seqi. apply SOS_Seqf. apply SOS_Assign.}
  eapply SOS_again.
  {cbv. apply SOS_Seqf. apply SOS_Assign.}
  cbn. cbv[Pcarre_2]. cbv[corps_carre].
  eapply SOS_stop.
Qed.

(* 2 Ceci signifie que en applicant une itération de la boucle While sur Pcarre_inf en allant d'un etat [0;0;1] nous arrivons à un état [1;1;3]*)
Theorem SOS_Pcarre_inf_1er_tour : SOS (Inter Pcarre_inf [0;0;1]) (Inter Pcarre_inf [1; 1; 3]).
Proof.
  cbv. eapply SOS_again.
  {apply SOS_While.}
  eapply SOS_again.
  {apply SOS_If_true. cbn. reflexivity.}
  eapply SOS_again.
  {apply SOS_Seqi. apply SOS_Seqf. eapply SOS_Assign.}
  eapply SOS_again.
  {eapply SOS_Seqi.  eapply SOS_Seqf. apply SOS_Assign.}
   eapply SOS_again.
  { eapply SOS_Seqf.  eapply SOS_Assign.}
   eapply SOS_stop.
Qed.

(*3 Ceci signifie  que en éffectuant une deuxième itération de la boucle While sur Pcarre_2, donc allant de l'état d'arrivé du premier tour [1;1;3], nous arrivons à un autre etat intermédiare [2;4;5]*)

(*4 Pour ce théorème, il nous montre que l'état d'arrivé de la deuxième itération sur Pcarre_2 est enfait son état d'arrivé, l'état finale d'après les conditions initiale*)
Theorem SOS_Pcarre_2_fini : SOS (Inter Pcarre_2 [2; 4; 5]) (Final [2; 4; 5]).
Proof.
  cbv. eapply SOS_again.
  {eapply SOS_While.}
  eapply SOS_again.
  {eapply SOS_If_false. cbn. reflexivity.}
  eapply SOS_again.
  {eapply SOS_Skip.}
  eapply SOS_stop.
Qed.
