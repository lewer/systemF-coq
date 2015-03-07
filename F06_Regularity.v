Require Import "F01_Defs".
Require Import "F03_Insert_kind".
Require Import "F04_Remove_var".
(** * VI. Regularité 
Dans cette partie, nousn nous attelons à prouver la propriété de régularité suivante : Si un terme est typable avec un type [T] dans un environnement, alors ce type est "kindable" dans ce même environnemnt.*)

(** Pour cela nous avons besoin d'un premier lemme, stipulant que la possibilité de l'extraction d'un type dand un environnement bien formé entraîne la kindabilité de ce type dans cet environnement. *)
Lemma get_type_wf : forall x e T,
                      wf e -> get_type x e = Some T -> kindable e T.
(**  *)
Proof.
  induction x; intros.
  + destruct e; try discriminate.
    inv H0. inv H. exists K.
    assert (wf (remove_var 0 (ConsT t e))). assumption.
    eapply kinding_remove_var. assumption. reflexivity.
    econstructor; eassumption.
  + destruct e; try discriminate; simpl in H0.
    - destruct (get_type x e) eqn:eq; try discriminate.
      inv H0. inv H. apply IHx in eq; [|assumption].
      inv eq. exists x0. eapply insert_kind_wf_kinding.
      eassumption. constructor.
    - destruct (get_type x e) eqn:eq; try discriminate.
      inv H0. inv H. apply IHx in eq; [|assumption].
      inv eq. exists x0.
    assert (wf (remove_var 0 (ConsT t e))). assumption.
    eapply kinding_remove_var. assumption. reflexivity.
    econstructor; eassumption.
Qed.
(**  *)


(** Nous avons également besoin de montrer que si l'on peut typer un terme dans un environnement alors cet environnement est nécessairement bien formé.  *)
Lemma typing_wf : forall e t T, typing e t T -> wf e.
(**  *)
Proof.
  intros e t T H. induction H; auto.
  now inv IHtyping.
  now inv IHtyping.
Qed.
(**  *)


(** Enfin, on prouve la propriété de régularité.  *)
Lemma regularity : forall e t T,
                     typing e t T -> kindable e T.
(**  *)
Proof.
  intros e t T H. induction H.
  + now apply (get_type_wf x).
  + specialize (typing_wf _ _ _ H). intros Ht; inv Ht.
    inv IHtyping. exists (max K x). constructor. assumption.
    specialize (remove_var_wf_kinding). intros. destruct H1.
    specialize (H4 _ _ _ H0 0). simpl in H4.
    rewrite tshift_minus_tshift in H4.
    eapply H4. reflexivity.
  + inv IHtyping1. inv H1. now exists q.
  + inv IHtyping. exists (S (max x K)). constructor. assumption.
  + inv IHtyping. inv H1. exists p. eapply tsubst_kinding.
    eassumption. constructor. reflexivity. assumption.
Qed.


(** #<script src="jquery.min.js"></script>#
    #<script src="coqjs.js"></script># *)