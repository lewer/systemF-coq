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



Definition kindable e T := exists K, kinding e T K.



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



(* * Cumulativité *)

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


(** * Induction mutuelle  *)

(** On a besoin de faire une induction mutuelle.  *)
Scheme wf_ind_mut := Induction for wf Sort Prop
with kinding_ind_mut := Induction for kinding Sort Prop.

Fact wf_kinding_ind_mut :
 ∀ (P : ∀ e : env, wf e → Prop) (P0 : ∀ (e : env) (t : typ) (k : kind), kinding e t k → Prop),
   P Nil WfNil
   → (∀ (K : kind) (e : env) (w : wf e), P e w →
                      P (ConsK K e) (WfConsK K e w))
   → (∀ (T : typ) (e : env) (K : kind) (k : kinding e T K), P0 e T K k → ∀ w : wf e, P e w →
                      P (ConsT T e) (WfConsT T e K k w))
   → (∀ (e : env) (X : var) (p : kind) (q : nat) (w : wf e), P e w → ∀ (e0 : get_kind X e = Some p) (l : p ≤ q),
                      P0 e (TyVar X) q (KVar e X p q w e0 l))
   → (∀ (e : env) (T1 T2 : typ) (p q : kind) (k : kinding e T1 p), P0 e T1 p k → ∀ k0 : kinding e T2 q, P0 e T2 q k0 →
                      P0 e (Arrow T1 T2) (max p q) (KArrow e T1 T2 p q k k0))
   → (∀ (e : env) (T : typ) (p q : kind) (k : kinding (ConsK q e) T p), P0 (ConsK q e) T p k →
                      P0 e (FAll q T) (S (max p q)) (KFAll e T p q k))
   → (∀ (e : env) (w : wf e), P e w) /\  (∀ (e : env) (t : typ) (k : kind) (k0 : kinding e t k), P0 e t k k0).
Proof.
  intros. split. 
  apply (wf_ind_mut P P0); assumption.
  apply (kinding_ind_mut P P0); assumption.
Qed.


(** * Propriétés de tshift et tsubst  *)

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
