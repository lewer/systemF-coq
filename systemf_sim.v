(* comment nommer seulement certaines hyp dans les inversion ? *)
(* un truc moins bourrin que inversion ? *)
(* beq_nat ou eq_nat_dec ? *)
(* pas grave le kind = nat ? *)

Require Export Arith.
Require Export Max.
Require Export Omega.

Definition var := nat.

Definition kind := nat.

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

Inductive env :=
  | Nil : env
  | ConsK : kind -> env -> env
  | ConsT : typ -> env -> env.


Fixpoint get_kind (X:var) (e:env) :=
  match (X, e) with
    | (0, ConsK K _) => Some K
    | (S X, ConsK _ e) => get_kind X e
    | (S X, ConsT _ e) => get_kind X e
    | _ => None
  end.

Fixpoint get_type (x:var) (e:env) :=
  match (x, e) with
    | (0, ConsT T _) => Some T
    | (S x, ConsK _ e) => get_type x e
    | (S x, ConsT _ e) => get_type x e
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


(* c=cutoff *)
Fixpoint tshift_aux (c:nat) (T:typ) :=
  match T with
    | TyVar X => if le_dec c X then TyVar (S X) else T
    | Arrow T1 T2 => Arrow (tshift_aux c T1) (tshift_aux c T2)
    | FAll K T => FAll K (tshift_aux (S c) T)
  end.

Definition tshift := tshift_aux 0.

(* substitution de X par U dans T *)
Fixpoint tsubst (X:nat) (U:typ) (T:typ) :=
  match T with
    | TyVar Y => if (eq_nat_dec X Y) then U else T
    | Arrow T1 T2 => Arrow (tsubst X U T1) (tsubst X U T2)
    | FAll K T => FAll K (tsubst (S X) (tshift U) T)
  end.

Inductive typing : env -> term -> typ -> Prop :=
  | TVar : forall e x T, wf e -> get_type x e = Some T -> typing e (Var x) T
  | TLam : forall e t T1 T2, typing (ConsT T1 e) t T2 -> typing e (Lam T1 t) (Arrow T1 T2)
  | TApp : forall e t1 t2 T1 T2, typing e t1 (Arrow T1 T2) -> typing e t2 T1 -> typing e (App t1 t2) T2
  | TAbs : forall e t K T, typing (ConsK K e) t T -> typing e (Abs K t) (FAll K T)
  | TAppT : forall e t K T1 T2, typing e t (FAll K T1) -> kinding e T2 K -> typing e (AppT t T2) (tsubst 0 T2 T1).


Lemma kinding_wf : forall e T K, kinding e T K -> wf e.
Proof.
  intros e T K H. induction H; try assumption.
  inversion IHkinding. assumption.
Qed.

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


(* Question 1.5 - Inférence *)
Fixpoint infer_kind (e:env) (T:typ) :=
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

(* Question 5 *)

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
                     | (Some K2, Some (FAll K1 T1)) => if le_dec K2 K1 then Some (tsubst 0 T2 T1) else None
                     | _ => None
                   end
  end.


Lemma infer_type_correct : forall t e T,
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
     destruct (le_dec K2 K1); [|discriminate].
     inversion H. apply (TAppT _ _ K1).
     - apply IHt; congruence.
     - apply (cumulativity _ _ K2). assumption.
       apply infer_kind_correct; congruence.
Qed.


(* Weakening *)
       
Inductive insert_kind : var -> env -> env -> Prop :=
| Top : forall e K, insert_kind 0 e (ConsK K e)
| BellowK : forall e e' X K, insert_kind X e e'
                        -> insert_kind (S X) (ConsK K e) (ConsK K e')
| BellowT : forall e e' X T, insert_kind X e e'
                        -> insert_kind (S X) (ConsT T e) (ConsT (tshift_aux X T) e').


Lemma insert_kind_get_kind : forall X e e', insert_kind X e e' -> forall Y,
                  get_kind Y e = (get_kind (if le_dec X Y then S Y else Y) e').
Proof.
  intros X e e' H. induction H; intros.
  + reflexivity.  
  + destruct Y; simpl.
    reflexivity.
    destruct (le_dec (S X) (S Y)).
    remember (S Y) as Y0. simpl.
    rewrite IHinsert_kind.
    assert ((if le_dec X Y then S Y else Y) = Y0).
    subst. apply le_S_n in l. destruct (le_dec X Y).
    reflexivity. intuition. rewrite <- H0.
    reflexivity.
    rewrite IHinsert_kind.
    assert ((if le_dec X Y then S Y else Y) = Y).
    destruct (le_dec X Y). apply le_n_S in l.
    intuition. reflexivity. simpl. rewrite <- H0 at 2.
    reflexivity.
  + destruct Y; simpl.
    reflexivity.
    destruct (le_dec (S X) (S Y)).
    remember (S Y) as Y0. simpl.
    rewrite IHinsert_kind.
    assert ((if le_dec X Y then S Y else Y) = Y0).
    subst. apply le_S_n in l. destruct (le_dec X Y).
    reflexivity. intuition. rewrite <- H0.
    reflexivity.
    rewrite IHinsert_kind.
    assert ((if le_dec X Y then S Y else Y) = Y).
    destruct (le_dec X Y). apply le_n_S in l.
    intuition. reflexivity. simpl. rewrite <- H0 at 2.
    reflexivity.
Qed.


Scheme popo := Induction for kinding Sort Prop
with opopo := Induction for wf Sort Prop.

Lemma insert_kind_wf : forall X e e',
                         insert_kind X e e' -> wf e -> wf e'.
Proof.
  intros X e e' Hins Hwf.
  eapply (opopo (fun e T K Hk => forall X e', insert_kind X e e' -> kinding e' (tshift_aux X T) K)
         (fun e Hwf => forall X e', insert_kind X e e' -> wf e')); intros; simpl. (*_ _ _ _ _ _ e Hwf X).??*)
  + specialize (insert_kind_get_kind _ _ _ H0 X0). intros.
    destruct (le_dec X1 X0); eapply KVar; eauto. congruence.
    congruence.
  + apply KArrow; auto.
  + apply KFAll. apply H. now apply BellowK.
  + inversion H. apply WfConsK. apply WfNil.
  + inversion H0; subst. apply WfConsK. now apply WfConsK.
    apply WfConsK. eapply H. eassumption.
  + inversion H1; subst. apply WfConsK. eapply WfConsT; eassumption. eapply WfConsT.apply H. assumption. eapply H0. eassumption.
  + eassumption.
  + eassumption.
Qed.


















opopo
     : forall
         (P : forall (e : env) (t : typ) (k : kind), kinding e t k -> Prop)
         (P0 : forall e : env, wf e -> Prop),
       (forall (e : env) (X : var) (p : kind) (q : nat) (w : wf e),
        P0 e w ->
        forall (e0 : get_kind X e = Some p) (l : p <= q),
        P e (TyVar X) q (KVar e X p q w e0 l)) ->
       (forall (e : env) (T1 T2 : typ) (p q : kind) (k : kinding e T1 p),
        P e T1 p k ->
        forall k0 : kinding e T2 q,
        P e T2 q k0 -> P e (Arrow T1 T2) (max p q) (KArrow e T1 T2 p q k k0)) ->
       (forall (e : env) (T : typ) (p q : kind) (k : kinding (ConsK q e) T p),
        P (ConsK q e) T p k -> P e (FAll q T) (S (max p q)) (KFAll e T p q k)) ->
       P0 Nil WfNil ->
       (forall (K : kind) (e : env) (w : wf e),
        P0 e w -> P0 (ConsK K e) (WfConsK K e w)) ->
       (forall (T : typ) (e : env) (K : kind) (k : kinding e T K),
        P e T K k ->
        forall w : wf e, P0 e w -> P0 (ConsT T e) (WfConsT T e K k w)) ->
       forall (e : env) (w : wf e), P0 e w

                                       
popo
     : forall
         (P : forall (e : env) (t : typ) (k : kind), kinding e t k -> Prop)
         (P0 : forall e : env, wf e -> Prop),
       (forall (e : env) (X : var) (p : kind) (q : nat) (w : wf e),
        P0 e w ->
        forall (e0 : get_kind X e = Some p) (l : p <= q),
        P e (TyVar X) q (KVar e X p q w e0 l)) ->
       (forall (e : env) (T1 T2 : typ) (p q : kind) (k : kinding e T1 p),
        P e T1 p k ->
        forall k0 : kinding e T2 q,
        P e T2 q k0 -> P e (Arrow T1 T2) (max p q) (KArrow e T1 T2 p q k k0)) ->
       (forall (e : env) (T : typ) (p q : kind) (k : kinding (ConsK q e) T p),
        P (ConsK q e) T p k -> P e (FAll q T) (S (max p q)) (KFAll e T p q k)) ->
       P0 Nil WfNil ->
       (forall (K : kind) (e : env) (w : wf e),
        P0 e w -> P0 (ConsK K e) (WfConsK K e w)) ->
       (forall (T : typ) (e : env) (K : kind) (k : kinding e T K),
        P e T K k ->
        forall w : wf e, P0 e w -> P0 (ConsT T e) (WfConsT T e K k w)) ->
       forall (e : env) (t : typ) (k : kind) (k0 : kinding e t k), P e t k k0


                                                                     
kinding_ind
     : forall P : env -> typ -> kind -> Prop,
       (forall (e : env) (X : var) (p : kind) (q : nat),
        wf e -> get_kind X e = Some p -> p <= q -> P e (TyVar X) q) ->
       (forall (e : env) (T1 T2 : typ) (p q : kind),
        kinding e T1 p ->
        P e T1 p -> kinding e T2 q -> P e T2 q -> P e (Arrow T1 T2) (max p q)) ->
       (forall (e : env) (T : typ) (p q : kind),
        kinding (ConsK q e) T p ->
        P (ConsK q e) T p -> P e (FAll q T) (S (max p q))) ->
       forall (e : env) (t : typ) (k : kind), kinding e t k -> P e t k


                                                                 
Lemma insert_kind_wf : forall X e e',
                         insert_kind X e e' -> (wf e -> wf e') /\ (forall T K, kinding e T K -> kinding e' (tshift_aux X T) K) /\ (forall X, get_kind (S X) e' = get_kind X e).
Proof.
