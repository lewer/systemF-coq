Require Import "F01_Defs".
Require Import "F03_Insert_kind".
Require Import "F05_Remove_var".


Lemma get_type_wf : forall x e T,
                      wf e -> get_type x e = Some T -> kindable e T.
Proof.
  induction x; intros.
  + destruct e; try discriminate.
    inv H0. inv H. exists K.
    replace e with (remove_var 0 (ConsT t e)) in H2; [|reflexivity].
    now apply kinding_remove_var.
  + destruct e; try discriminate; simpl in H0.
    - destruct (get_type x e) eqn:eq; try discriminate.
      inv H0. inv H. apply IHx in eq; [|assumption].
      inv eq. exists x0. eapply insert_kind_wf_kinding.
      eassumption. constructor.
    - destruct (get_type x e) eqn:eq; try discriminate.
      inv H0. inv H. apply IHx in eq; [|assumption].
      inv eq. exists x0.
      replace e with (remove_var 0 (ConsT t e)) in H; [|reflexivity].
      now apply kinding_remove_var.
Qed.


Lemma typing_wf : forall e t T, typing e t T -> wf e.
Proof.
  intros e t T H. induction H; auto.
  now inv IHtyping.
  now inv IHtyping.
Qed.

    
Lemma regularity : forall e t T,
                     typing e t T -> kindable e T.
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
 


(* apply left A/\B ??? *)