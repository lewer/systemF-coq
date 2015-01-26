
(* comment nommer seulement certaines hyp dans les inversion ? *)
(* un truc moins bourrin que inversion ? *)
(* beq_nat ou eq_nat_dec ? *)
(* pas grave le kind = nat ? *)


Require Export Utf8.
Require Export Arith.
Require Export Max.
Require Export Omega.


Ltac inv H := inversion H; try subst; clear H.


(** Formalisation du système F ! *)

(** * Définitions  *)

(**  On utilise des indices de de Bruinj pour repérsenter les termes.*)
(** [var] est les type des variable (l'indice en fait) et [kind] celui des sortes  *)
Definition var := nat.

Definition kind := nat.

(** On définit les types et les termes.  *)
Inductive typ :=
  | TyVar : var -> typ
  | Arrow : typ -> typ -> typ
  | FAll : kind -> typ -> typ.

Inductive term :=
  | Var : var -> term
  | Lam : typ -> term -> term
  | App : term -> term -> term
  | Abs : kind -> term -> term
  | AppT : term -> typ -> term.

(** Un environnement est une liste de déclarations de sortes et de types. *)
Inductive env :=
  | Nil : env
  | ConsK : kind -> env -> env
  | ConsT : typ -> env -> env.


(** [tshift c T] incrémente les variables [>= c] dans le type [T] *)
(* c=cutoff *)
Fixpoint tshift (c:var) (T:typ) : typ :=
  match T with
    | TyVar X => if leb c X then TyVar (S X) else TyVar X
    | Arrow T1 T2 => Arrow (tshift c T1) (tshift c T2)
    | FAll K T => FAll K (tshift (S c) T)
  end.

(** [shift c t] incrémente les variables [>= c] dans le terme [t] *)
Fixpoint shift (c:var) (t:term) : term :=
  match t with
    | Var x => if leb c x then Var (S x) else Var x
    | Lam T t => Lam (tshift c T) (shift (S c) t)
    | App t1 t2 => App (shift c t1) (shift c t2)
    | Abs K t => Abs K (shift (S c) t)
    | AppT t T => AppT (shift c t) (tshift c T)
  end.


(** [get_kind X e] renvoie la sorte de la variable d'indice [X] dans l'environnement [e].
Attention aux décalages d'indices. *)
Fixpoint get_kind (X:var) (e:env) : option kind :=
  match (X, e) with
    | (0, ConsK K _) => Some K
    | (S X, ConsK _ e) => get_kind X e
    | (S X, ConsT _ e) => get_kind X e
    | _ => None
  end.

Fixpoint get_type (x:var) (e:env) :=
  match (x, e) with
    | (0, ConsT T _) => Some (tshift 0 T)
    | (S x, ConsK _ e) => option_map (tshift 0) (get_type x e)
    | (S x, ConsT _ e) => option_map (tshift 0) (get_type x e)
    | _ => None
  end.


Inductive wf : env -> Prop :=
  | WfNil : wf Nil
  | WfConsK : forall K e, wf e -> wf (ConsK K e)
  | WfConsT : forall T e, forall K, kinding e T K -> wf e -> wf (ConsT T e)

with kinding : env -> typ -> kind -> Prop :=
  | KVar : forall e X p q, wf e -> get_kind X e = Some p -> (p <= q) -> kinding e (TyVar X) q
  | KArrow : forall e T1 T2 p q, kinding e T1 p -> kinding e T2 q -> kinding e (Arrow T1 T2) (max p q)
  | KFAll : forall e T p q, kinding (ConsK q e) T p -> kinding e (FAll q T) (S (max p q)).



(** Substitution de X par U dans T *)
Fixpoint tsubst (X:nat) (U:typ) (T:typ) :=
  match T with
    | TyVar Y => match nat_compare X Y with
                   | Eq => U
                   | Gt => TyVar Y
                   | Lt => TyVar (Y-1)
                 end
    | Arrow T1 T2 => Arrow (tsubst X U T1) (tsubst X U T2)
    | FAll K T => FAll K (tsubst (S X) (tshift 0 U) T)
  end.

Inductive typing : env -> term -> typ -> Prop :=
  | TVar : forall e x T, wf e -> get_type x e = Some T -> typing e (Var x) T
  | TLam : forall e t T1 T2, typing (ConsT T1 e) t (tshift 0 T2) -> typing e (Lam T1 t) (Arrow T1 T2)
  | TApp : forall e t1 t2 T1 T2, typing e t1 (Arrow T1 T2) -> typing e t2 T1 -> typing e (App t1 t2) T2
  | TAbs : forall e t K T, typing (ConsK K e) t T -> typing e (Abs K t) (FAll K T)
  | TAppT : forall e t K T1 T2, typing e t (FAll K T1) -> kinding e T2 K -> typing e (AppT t T2) (tsubst 0 T2 T1).


Example typing1 : typing Nil (Abs 12 (Lam (TyVar 0) (Var 0))) (FAll 12 (Arrow (TyVar 0) (TyVar 0))).
repeat econstructor.
Qed.

Example typing2 : typing   (ConsT (TyVar 0) (ConsK 5 Nil))   (AppT (Abs 12 (Lam (TyVar 0) (Var 0))) (TyVar 1))   (Arrow (TyVar 1) (TyVar 1)).
replace (Arrow (TyVar 1) (TyVar 1)) with (tsubst 0 (TyVar 1) (Arrow (TyVar 0) (TyVar 0))); [|reflexivity].
repeat econstructor.
Qed.

Example typing3 : typing   (ConsT (TyVar 0) (ConsK 5 Nil))   (App (AppT (Abs 12 (Lam (TyVar 0) (Var 0))) (TyVar 1)) (Var 0))   (TyVar 1).
apply TApp with (T1 := TyVar 1).
replace (Arrow (TyVar 1) (TyVar 1)) with (tsubst 0 (TyVar 1) (Arrow (TyVar 0) (TyVar 0))); [|reflexivity].
repeat econstructor.
repeat econstructor.
Qed.

Definition ex := ConsT (Arrow (TyVar 2) (TyVar 0))
                       (ConsK 15
                              (ConsT (TyVar 0)
                                     (ConsK 0 Nil))).

Example wf4 : wf ex.
repeat econstructor.
Qed.

Example typing4 : typing ex (App (Var 0) (Var 2)) (TyVar 1).
repeat econstructor.
Qed.

Definition ex' := ConsT (Arrow (TyVar 3) (TyVar 1))
                        (ConsK 17
                               (ConsK 15
                                      (ConsT (TyVar 0)
                                             (ConsK 0 Nil)))).

Example wf4' : wf ex'.
repeat econstructor.
Qed.

Example typing4' : typing ex' (App (Var 0) (Var 3)) (TyVar 2).
repeat econstructor.
Qed.


Lemma get_type_typing : forall x e T,
  wf e -> get_type x e = Some T -> typing e (Var x) T.
Proof.
  destruct x; intros; simpl; now constructor.
Qed.


Lemma tsubst_ok : forall v e K U K',
  kinding (ConsK K' e) (TyVar (S v)) K -> kinding e U K' -> kinding e (tsubst 0 U (TyVar (S v))) K.
Proof.
  intros. simpl.
  inv H. inv H2. econstructor; try eassumption.
  simpl in H3. now rewrite <- minus_n_O.
Qed.

  
(** * Cumulativité  *)

Lemma cumulativity : forall T e K1 K2, K1 <= K2 -> kinding e T K1 -> kinding e T K2.
Proof.
  induction T; intros e K1 K2 Hle H; inversion H; subst.
  + eapply KVar; try eassumption. omega.
  + replace K2 with (max K2 K2). apply KArrow.
    - apply (IHT1 _ p). apply (max_lub_l _ _ _ Hle). assumption.
    - apply (IHT2 _ q). apply (max_lub_r _ _ _ Hle). assumption.
    - apply max_idempotent.
  + destruct K2 as [|K2]. inversion Hle. apply le_S_n in Hle.
    replace K2 with (max K2 k). apply KFAll.
    - apply (IHT _ p). apply (max_lub_l _ _ _ Hle). assumption.
    - apply max_lub_r in Hle. now apply max_l.
Qed.


(** * Inférence *)
(** ** Inférence de kind  *)
Fixpoint infer_kind (e:env) (T:typ) : option kind :=
  match T with
    | TyVar X => get_kind X e
    | Arrow T1 T2 => match (infer_kind e T1, infer_kind e T2) with
                       | (Some p, Some q) => Some (max p q)
                       | _ => None
                     end
    | FAll q T => match infer_kind (ConsK q e) T with 
                    | Some p => Some (S (max p q))
                    | _ => None
                  end
  end.


Lemma infer_kind_correct : forall T e K,
  wf e -> infer_kind e T = Some K -> kinding e T K .
Proof.
  induction T.
  + intros e K Hwf H. simpl in H. eapply KVar. assumption. eassumption. reflexivity.
  + intros e K Hwf H. simpl in H.
    remember (infer_kind e T1) as opt1. destruct opt1.
    remember (infer_kind e T2) as opt2. destruct opt2.
    inversion H. apply KArrow.
    apply IHT1. assumption. now symmetry.
    apply IHT2. assumption. now symmetry.
    discriminate H. discriminate.
  + intros e K Hwf H. simpl in H.
    remember (infer_kind (ConsK k e) T) as opt. destruct opt; [|discriminate].
    inversion H. apply KFAll. apply IHT. apply WfConsK. assumption.
    now symmetry.
Qed.

(** ** Inférence de types  *)

(* On peut décider si deux kinds k et l sont égaux *)
Lemma eq_kind_dec : forall (k l :kind), {k=l} + {k<>l}.
Proof.
  exact eq_nat_dec.
Qed.

(* On peut décider si deux types T et U sont égaux *)
Lemma eq_typ_dec : forall (T U :typ), {T=U} + {T<>U}.
Proof.
  decide equality; decide equality.
Qed.


Fixpoint infer_type (e:env) (t:term) :=
  match t with 
    | Var x => get_type x e
    | Lam T t => match (infer_kind e T, infer_type (ConsT T e) t) with
                   | (Some _, Some T') => Some (Arrow T T')
                   | _ => None
                 end
    | App t1 t2 => match (infer_type e t1, infer_type e t2) with
                     | (Some (Arrow T1 T2), Some T1') => if eq_typ_dec T1 T1' then Some T2 else None
                     | _ => None
                   end
    | Abs K t => match infer_type (ConsK K e) t with
                   | Some T => Some (FAll K T)
                   | _ => None
                 end
    | AppT t T2 => match (infer_kind e T2, infer_type e t) with
                     | (Some K2, Some (FAll K1 T1)) => if leb K2 K1 then Some (tsubst 0 T2 T1) else None
                     | _ => None
                   end
  end.


(*Lemma infer_type_correct : forall t e T,
  wf e -> infer_type e t = Some T -> typing e t T.
Proof.
  induction t  as [v|T1 t|t1 IHt1 t2 IHt2|K t|t IHt T2].
  + intros e T Hwf H. simpl in H. now apply TVar.
  + intros e T' Hwf H. simpl in H.
    remember (infer_kind e T1) as opt1. destruct opt1 as [K|]; [|discriminate].
    remember (infer_type (ConsT T1 e) t) as opt2. destruct opt2 as [T2|]; [|discriminate]. inversion H. apply TLam. apply IHt; [|auto].
    apply (WfConsT _ _ K). now apply infer_kind_correct. assumption.
  + intros e T Hwf H. simpl in H.
    remember (infer_type e t1) as opt1. destruct opt1 as [T1|]; [|discriminate]. destruct T1 as [|T1 T2|]; try discriminate.
    remember (infer_type e t2) as opt2. destruct opt2 as [T1'|]; [|discriminate].
    destruct (eq_typ_dec T1 T1'); [|discriminate].
    inversion H. apply (TApp _ _ _ T1 T).
    - apply IHt1; auto. congruence.
    - apply IHt2; auto. congruence.
  + intros e T Hwf H. simpl in H.
    remember (infer_type (ConsK K e) t) as opt. destruct opt as [T1|]; [|discriminate].
    inversion H. apply TAbs.
    apply IHt. now apply WfConsK. congruence.
  +  intros e T Hwf H. simpl in H.
     remember (infer_kind e T2) as opt. destruct opt as [K2|]; [|discriminate].
     remember (infer_type e t) as opt. destruct opt as [T1|]; [|discriminate].
     destruct T1 as [| |K1 T1]; try discriminate.
     remember (leb K2 K1) as b. destruct b; [|discriminate].
     inversion H. apply (TAppT _ _ K1).
     - apply IHt; congruence.
     - apply (cumulativity _ _ K2). symmetry in Heqb. now apply leb_complete.
       apply infer_kind_correct; congruence.
Qed.



*)
(** * Weakening  et insert_kind *)
       
Inductive insert_kind : var -> env -> env -> Prop :=
| Top : forall e K, insert_kind 0 e (ConsK K e)
| BelowK : forall e e' X K, insert_kind X e e' ->
      insert_kind (S X) (ConsK K e) (ConsK K e')
| BelowT : forall e e' X T, insert_kind X e e' ->
      insert_kind (S X) (ConsT T e) (ConsT (tshift X T) e').


(** ** [insert_kind_wf] et [insert_kind_kinding]  *)
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

(** On a besoin de faire une induction mutuelle.  *)
Scheme kinding_ind_mut := Induction for kinding Sort Prop
with wf_ind_mut := Induction for wf Sort Prop.



Lemma insert_kind_wf : forall e, wf e -> forall X e',
       insert_kind X e e' -> wf e'.
Proof.
  intros e Hwf.
  induction Hwf as [e Y K K' Hwf HI H H'| | | | | ] using wf_ind_mut with (P := (fun e T K Hk => forall X e', insert_kind X e e' -> kinding e' (tshift X T) K)); intros X e' Hins; simpl.
  + specialize (insert_kind_get_kind _ _ _ Hins Y). intros.
    destruct (leb X Y); eapply KVar; eauto. congruence.
    congruence.
  + apply KArrow; auto.
  + apply KFAll. apply IHHwf. now apply BelowK.
  + inv Hins. apply WfConsK. apply WfNil.
  + inv Hins. apply WfConsK. now apply WfConsK.
    apply WfConsK. eapply IHHwf. eassumption.
  + inv Hins. apply WfConsK. eapply WfConsT; eassumption. eapply WfConsT. apply IHHwf. 
assumption. eapply IHHwf0. eassumption.
Qed.


Lemma insert_kind_kinding : forall e T K, kinding e T K ->
              forall X e', insert_kind X e e' -> kinding e' (tshift X T) K.
Proof.
  intros e T K Hk.
  induction Hk; simpl; intros X0 e' Hins.
  + rewrite (insert_kind_get_kind _ _ _ Hins X) in H0.
    destruct (leb X0 X).
    - apply (KVar _ _ p); try easy.
      eapply insert_kind_wf; eassumption.
    - apply (KVar _ _ p); try easy.
      eapply insert_kind_wf; eassumption.
  + apply KArrow; auto.
  + apply KFAll. apply IHHk. apply BelowK. assumption.
Qed.


(** ** [insert_kind_typing]  *)

Lemma tshift_tshift : forall T c d,
  tshift c (tshift (c+d) T) = tshift (S (c+d)) (tshift c T).
Proof.
  induction T; intros; simpl.
  + destruct (leb (c+d) v) eqn:?; simpl.
    * specialize (leb_complete _ _ Heqb); intros.
      replace (leb c v) with true. simpl.
      replace (leb c (S v)) with true.
      now rewrite Heqb. 
      symmetry. apply leb_correct. omega.
      symmetry. apply leb_correct. omega.
    * specialize (leb_complete_conv _ _ Heqb); intros.
      destruct (leb c v) eqn:?; simpl.
      now rewrite Heqb. 
      destruct v. easy.
      replace (leb (c+d) v) with false. easy.
      symmetry. apply leb_correct_conv. omega.
  + apply f_equal2; easy.
  + apply f_equal. specialize (IHT (S c) d). easy.
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



Lemma tsubst_tshift : forall T X Y U,
        tsubst X (tshift (X+Y) U) (tshift (S (X+Y)) T) = tshift (X+Y) (tsubst X U T).
Proof.
  induction T; intros; simpl.
  + destruct v. now destruct X.
  simpl. rewrite <- minus_n_O.
  destruct (nat_compare X (S v)) eqn:?; simpl.
    * apply nat_compare_eq in Heqc. subst X.
      destruct (leb (S v+Y) v) eqn:?; simpl.
      apply leb_complete in Heqb. omega.
      replace (nat_compare v v) with Eq.
      reflexivity.  symmetry. now apply nat_compare_eq_iff.
    * apply nat_compare_lt in Heqc.
      destruct (leb (X+Y) v) eqn:?; simpl.
      replace (nat_compare X (S(S v))) with Lt.
      reflexivity. symmetry. apply nat_compare_lt. omega.
      replace (nat_compare X (S v)) with Lt.
      now rewrite <- minus_n_O. symmetry. apply nat_compare_lt. omega.
    * destruct (leb (X+Y) v) eqn:?; simpl.
      apply nat_compare_gt in Heqc.
      apply leb_complete in Heqb. omega.
      rewrite Heqc.
      apply nat_compare_gt in Heqc.
      apply leb_complete_conv in Heqb. 
      destruct (leb (X+Y) (S v)) eqn:?; simpl.
      apply leb_complete in Heqb0. omega.
      reflexivity.
  + apply f_equal2; auto.
  + apply f_equal. replace (S (X + Y)) with ((S X)+Y); [|omega].
    rewrite <- IHT. apply f_equal2; [|reflexivity].
    replace (X + Y) with (0+(X+Y)); [|omega].
    replace (S X + Y) with (S (0+(X+Y))); [|omega].
    apply tshift_tshift.
Qed.

                            
Lemma insert_kind_typing : forall e t T, typing e t T ->
       forall X e', insert_kind X e e' -> typing e' (shift X t) (tshift X T).
Proof.
  intros e t T Ht. induction Ht; intros X e' Hins.
  + simpl. destruct (leb X x) eqn:?.
    * constructor. eapply insert_kind_wf; eassumption.
      rewrite (insert_kind_get_type _ _ _ Hins (S x)).
      replace (nat_compare X (S x)) with Lt. simpl.
      rewrite <- minus_n_O. now rewrite H0. symmetry. 
      apply nat_compare_lt. apply leb_complete in Heqb. omega.
    * constructor. eapply insert_kind_wf; eassumption.
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
    eapply insert_kind_kinding; eassumption.
    specialize  (tsubst_tshift T1 0 X T2).
    now rewrite plus_O_n.
Qed.




Inductive env_subst : var -> typ -> env -> env -> Prop :=
  |SubstNil : forall X T, env_subst X T Nil Nil
  |SubstSubst : forall X T e, env_subst X T (ConsT (TyVar X) e) (ConsT T e)
  |SubstConsK : forall X T e e', env_subst X T e e' -> 
                     forall K, env_subst X T (ConsK K e) (ConsK K e')
  |SubstConsT : forall X T e e', env_subst X T e e' ->
                     forall U, env_subst X T (ConsT U e) (ConsT (tsubst X T U) e').

