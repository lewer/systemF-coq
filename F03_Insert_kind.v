Require Import "F01_Defs".


Inductive insert_kind : var -> env -> env -> Prop :=
| Top : forall e K, insert_kind 0 e (ConsK K e)
| BelowK : forall e e' X K, insert_kind X e e' ->
      insert_kind (S X) (ConsK K e) (ConsK K e')
| BelowT : forall e e' X T, insert_kind X e e' ->
      insert_kind (S X) (ConsT T e) (ConsT (tshift X T) e').



Lemma insert_kind_get_kind : forall X e e', insert_kind X e e' -> forall Y,
                  get_kind Y e = (get_kind (if leb X Y then S Y else Y) e').
Proof.
  intros X e e' H. induction H; intros.
  + easy.
  + destruct Y; simpl.
    reflexivity.
    rewrite IHinsert_kind.
    destruct (leb X Y) eqn:?.
    reflexivity. reflexivity.
  + destruct Y; simpl.
    reflexivity.
    rewrite IHinsert_kind.
    destruct (leb X Y) eqn:?.
    reflexivity. reflexivity.
Qed.



Lemma insert_kind_wf_kinding :
  (forall e, wf e -> forall X e', insert_kind X e e' -> wf e')
      /\
        (forall e T K, kinding e T K -> forall X e', insert_kind X e e' -> kinding e' (tshift X T) K).
Proof.
  apply wf_kinding_ind_mut.
  + intros X e' Hins. inv Hins. apply WfConsK. apply WfNil.
  + intros K e w IHHwf X e' Hins. inv Hins. apply WfConsK. now apply WfConsK.
    apply WfConsK. eapply IHHwf. eassumption.
  + intros T e K k IHHwf w IHHwf0 X e' Hins. inv Hins. apply WfConsK. eapply WfConsT; eassumption. eapply WfConsT. apply IHHwf. 
assumption. eapply IHHwf0. eassumption.
  + intros e Y p q w IHHwf H H' X e' Hins. specialize (insert_kind_get_kind _ _ _ Hins Y). intros. simpl. destruct (leb X Y); eapply KVar; eauto. congruence.
    congruence.
  + intros e T1 T2 p q k IHHwf Hk IHHwf0 X e' Hins. apply KArrow; auto.
  + intros e T p q k IHHwf X e' Hins. apply KFAll. apply IHHwf. now apply BelowK.
Qed.




Lemma insert_kind_get_type : forall X e e', insert_kind X e e' -> forall x, 
            get_type x e' = match nat_compare X x with
                              | Lt => option_map (tshift X) (get_type (x-1) e)
                              | Eq => None
                              | Gt => option_map (tshift (X)) (get_type x e) end.
Proof.
  intros X e e' H. induction H; intros.
  + destruct x; simpl. reflexivity. now rewrite <- minus_n_O.
  + destruct x; simpl. reflexivity.
    rewrite IHinsert_kind.
    destruct (nat_compare X x) eqn:?; try reflexivity.
    * apply nat_compare_Lt_lt in Heqc. destruct x. inv Heqc. rewrite <- minus_n_O. replace (S x - 1) with x. simpl.  destruct (get_type x e); [|reflexivity]. simpl. apply f_equal. specialize (tshift_tshift t 0 X). rewrite plus_O_n. easy. omega.
    * apply nat_compare_Gt_gt in Heqc. destruct (get_type x e) as [T|]; [|reflexivity]. simpl. apply f_equal.      specialize (tshift_tshift T 0 X). rewrite plus_O_n. easy.
  + destruct x; simpl. apply f_equal.  specialize (tshift_tshift T 0 X). rewrite plus_O_n. easy. 
    rewrite IHinsert_kind.
    destruct (nat_compare X x) eqn:?; try reflexivity.
    * apply nat_compare_Lt_lt in Heqc. destruct x. inv Heqc. rewrite <- minus_n_O. replace (S x - 1) with x.
      simpl.  destruct (get_type x e); [|reflexivity]. simpl. apply f_equal. specialize (tshift_tshift t 0 X). rewrite plus_O_n. easy. omega.
    * apply nat_compare_Gt_gt in Heqc. destruct (get_type x e); [|reflexivity]. simpl. apply f_equal.
      specialize (tshift_tshift t 0 X). rewrite plus_O_n. easy.
Qed.


                            
Lemma insert_kind_typing : forall e t T, typing e t T ->
       forall X e', insert_kind X e e' -> typing e' (shift X t) (tshift X T).
Proof.
  intros e t T Ht. induction Ht; intros X e' Hins.
  + simpl. destruct (leb X x) eqn:?.
    * constructor. eapply insert_kind_wf_kinding; eassumption.
      rewrite (insert_kind_get_type _ _ _ Hins (S x)).
      replace (nat_compare X (S x)) with Lt. simpl.
      rewrite <- minus_n_O. now rewrite H0. symmetry. 
      apply nat_compare_lt. apply leb_complete in Heqb. omega.
    * constructor. eapply insert_kind_wf_kinding; eassumption.
      rewrite (insert_kind_get_type _ _ _ Hins (x)).
      replace (nat_compare X (x)) with Gt. now rewrite H0. symmetry. 
      apply nat_compare_gt. apply leb_complete_conv in Heqb. omega.

  + simpl. constructor. specialize (IHHt (S X) (ConsT (tshift X T1) e')). specialize (tshift_tshift T2 0 X). intro Htt.
    rewrite plus_O_n in Htt. rewrite Htt. apply IHHt.
    now constructor.

  + econstructor. now apply IHHt1.
    now apply IHHt2.

  + constructor. apply IHHt. now constructor.

  + replace (tshift X (tsubst 0 T2 T1)) with (tsubst 0 (tshift X T2) (tshift (S X) T1)).
    apply (TAppT _ _ K). replace (FAll K (tshift (S X) T1)) with (tshift X (FAll K T1)).
    now apply IHHt. reflexivity.
    eapply insert_kind_wf_kinding; eassumption.
    specialize  (tsubst_tshift T1 0 X T2).
    now rewrite plus_O_n.
Qed.

Lemma kinding_wf : forall e T K, kinding e T K -> wf e.
Proof.
intros e T K H. induction H; auto.
now inv IHkinding.
Qed.

Lemma tsubst_kinding : forall T e' K, kinding e' T K -> (* todo *)
                                      forall X e L U, insert_kind X e e' -> get_kind X e' = Some L -> kinding e U L -> kinding e (tsubst X U T) K.
Proof.
  induction T as [Y|T1 IHT1 T2 IHT2|k T]; intros e' K HkT X e L U Hik Hgk HkU.
  - destruct (nat_compare X Y) eqn:H.
    + simpl. rewrite H. destruct (le_lt_dec K L) as [H1|H1].
      inversion HkT.
      (* comme X=Y, H3 et Hgk donnent p=L, donc HkU:kinding e U p
       et avec cumulativity et H5 c'est bon *)
      admit.
      apply cumulativity with L. omega. assumption.
    + simpl. rewrite H. inversion HkT. comp. apply KVar with p.
      apply (kinding_wf e U L HkU).
      rewrite (insert_kind_get_kind X e e'). replace (leb X (Y-1)) with true. 
      replace (S (Y-1)) with Y. assumption.
      admit.
      admit.
      assumption. assumption.
      (* comme les 2e et 3e + se ressemblent, 
         comment on les traite de la meme façon ? *)
    + simpl. rewrite H. inversion HkT. apply KVar with p.
      apply (kinding_wf e U L HkU).
      rewrite (insert_kind_get_kind X e e'). replace (leb X Y) with false. assumption.
      admit. assumption. 
      assumption.
  - simpl. inversion HkT. apply KArrow.
    + now apply IHT1 with e' L.
    + now apply IHT2 with e' L.
  - simpl. inversion HkT. apply KFAll.
    apply IHT with (ConsK k e') L. assumption.
    now constructor.
    assumption.
    apply (proj2 (insert_kind_wf_kinding)) with e. assumption.
    constructor.
Qed.