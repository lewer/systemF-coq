Require Import "F01_Defs".


Fixpoint tshift_minus (x : var) (T : typ) {struct T} : typ :=
  match T with
    | TyVar X => if leb x X then TyVar (X-1) else TyVar X
    | Arrow T1 T2 => Arrow (tshift_minus x T1) (tshift_minus x T2)
    | FAll K T0 => FAll K (tshift_minus (S x) T0)
  end.


Fixpoint remove_var x e {struct e} : env :=
  match e with
    | Nil => Nil
    | ConsK K e => match x with
                     | 0 => ConsK K e
                     | S x => ConsK K (remove_var x e)
                   end
    | ConsT T e => match x with
                     | 0 => e
                     | S x => ConsT (tshift_minus x T) (remove_var x e)
                   end
  end.


Lemma remove_var_get_kind_lt : forall X e x, X < x -> get_kind X e = get_kind X (remove_var x e).
Proof.
  induction X; intros.
  + destruct e.
    - reflexivity.
    - destruct x. inv H. reflexivity.
    - destruct x. inv H. reflexivity.
  + destruct e.
    - reflexivity.
    - destruct x. inv H. apply IHX. omega.
    - destruct x. inv H. apply IHX. omega.
Qed.


Lemma remove_var_get_kind_ge : forall X e x T, X >= x -> get_type x e = Some T -> get_kind (S X) e = get_kind X (remove_var x e).
Proof.
  induction X; intros.
  + destruct x. destruct e; try reflexivity.
    discriminate. inv H.
  + destruct e.
    - reflexivity.
    - destruct x. inv H0. simpl in H0.
      destruct (get_type x e) eqn:?. eapply IHX. omega.
      eassumption. discriminate.
    - destruct x. reflexivity.
      simpl in H0. destruct (get_type x e) eqn:?. eapply IHX. omega.
      eassumption. discriminate.
Qed.



Lemma get_get : forall X e x K T, get_kind X e = Some K -> get_type x e = Some T -> X<>x.
Proof.
  induction X; intros.
  + intros eq. subst x. destruct e; discriminate.
  + intros eq. subst x. destruct e; try discriminate.
    - simpl in H0. destruct (get_type X e) eqn:?; [|discriminate].
      eapply IHX. eassumption. eassumption. reflexivity.
    - simpl in H0. destruct (get_type X e) eqn:?; [|discriminate].
      eapply IHX. eassumption. eassumption. reflexivity.
Qed.



Lemma remove_var_wf_kinding : 
  (forall e, wf e -> forall x U, get_type x e = Some U -> wf (remove_var x e))
     /\
        (forall e T K, kinding e T K -> forall x U, get_type x e = Some U -> kinding (remove_var x e) (tshift_minus x T) K).
Proof.
  apply wf_kinding_ind_mut; intros; simpl.
  + constructor.
  + destruct x; constructor. assumption.
    simpl in H0. destruct (get_type x e) eqn:?; [|discriminate].
    inv H0. now apply (H _ t).
  + destruct x. assumption.
    simpl in H1. destruct (get_type x e) eqn:?; [|discriminate].
    inv H1. econstructor. now apply (H _ t).
    now apply (H0 _ t).
  + destruct (leb x X) eqn:?; econstructor; eauto.
    - rewrite leb_iff in Heqb.
      specialize (get_get _ _ _ _ _ e0 H0). intros.
      destruct X. inv Heqb. now contradiction H1. simpl.
      rewrite <- minus_n_O.
      erewrite <- remove_var_get_kind_ge; try eassumption.
      inv Heqb. now contradiction H1. omega.
    - erewrite <- remove_var_get_kind_lt. assumption.
      now rewrite leb_iff_conv in Heqb.
  + constructor; eauto.
  + constructor. eapply (H (S x)). simpl.
    rewrite H0. reflexivity.
Qed.
