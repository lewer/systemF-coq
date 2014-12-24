(* comment nommer seulement certaines hyp dans les inversion ? *)
(* un truc moins bourrin que inversion ? *)
(* beq_nat ou eq_nat_dec ? *)
(* pas grave le kind = nat ? *)

Require Export Arith.

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
  | KFAll : forall e T p q, kinding (ConsK q e) T p -> kinding e (FAll p T) (S (max p q)).


(* c=cut, d=nb de fois à décaler *)
Fixpoint tshift_aux (c:nat) (d:nat) (T:typ) :=
  match T with
    | TyVar X => if le_dec c X then TyVar (X+d) else T
    | Arrow T1 T2 => Arrow (tshift_aux c d T1) (tshift_aux c d T2)
    | FAll K T => FAll K (tshift_aux (S c) d T)
  end.

Definition tshift := tshift_aux 0 1.

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


(* Question 1.5 - Inférence *)
Fixpoint infer_kind (e:env) (T:typ) :=
  match T with
    | TyVar X => get_kind X e
    | Arrow T1 T2 => match (infer_kind e T1, infer_kind e T2) with
                       | (Some p, Some q) => Some (max p q)
                       | _ => None
                     end
    | FAll q T => match infer_kind (ConsK q e) T with 
                    | Some p => Some (S (max q p))
                    | _ => None
                  end
  end.


Lemma kind_infer_correct : forall T e K,
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