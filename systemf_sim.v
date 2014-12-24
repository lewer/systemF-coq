Require Export Arith.


Inductive kind :=
  | Star : nat -> kind.

Inductive typ :=
  | TyVar : nat -> typ
  | Imp : typ -> typ -> typ
  | Forall : kind -> typ -> typ.

Inductive term :=
  | Var : nat -> term
  | Lam : typ -> term -> term
  | App : term -> term -> term
  | Abs : kind -> term -> term
  | AppT : term -> typ -> term.

Inductive env :=
  | Nil : env
  | ConsK : kind -> env -> env
  | ConsT : typ -> env -> env.


Fixpoint get_kind (X : nat) (e : env) :=
  match (X, e) with
    | (0, ConsK K _) => Some K
    | (S X, ConsK _ e) => get_kind X e
    | (S X, ConsT _ e) => get_kind X e
    | _ => None
  end.

Fixpoint get_type (x : nat) (e : env) :=
  match (x, e) with
    | (0, ConsT T _) => Some T
    | (S x, ConsK _ e) => get_type x e
    | (S x, ConsT _ e) => get_type x e
    | _ => None
  end.


Inductive wf : env -> Prop :=
  | WfNil : wf Nil
  | WfConK : forall K e, wf e -> wf (ConsK K e)
  | WfConT : forall T e, forall K, kinding e T K -> wf e -> wf (ConsT T e)

with kinding : env -> typ -> kind -> Prop :=
  | KVar : forall e X p q, wf e -> get_kind X e = Some (Star p) -> (p <= q) -> kinding e (TyVar X) (Star q)
  | KImp : forall e T1 T2 p q, kinding e T1 (Star p) -> kinding e T2 (Star q) -> kinding e (Imp T1 T2) (Star (max p q))
  | KForall : forall e T p q, kinding (ConsK (Star q) e) T (Star p) -> kinding e (Forall (Star p) T) (Star (S (max p q))).


(* c=cut, d=nb de fois à décaler *)
Fixpoint tshift_aux (c:nat) (d:nat) (T:typ) :=
  match T with
    | TyVar X => if le_dec c X then TyVar (X+d) else T
    | Imp T1 T2 => Imp (tshift_aux c d T1) (tshift_aux c d T2)
    | Forall K T => Forall K (tshift_aux (S c) d T)
  end.

Definition tshift := tshift_aux 0 1.

(* substitution de X par U dans T *)
Fixpoint tsubst (X:nat) (U:typ) (T:typ) :=
  match T with
    | TyVar Y => if (eq_nat_dec X Y) then U else T
    | Imp T1 T2 => Imp (tsubst X U T1) (tsubst X U T2)
    | Forall K T => Forall K (tsubst (S X) (tshift U) T)
  end.
(* ??? est-ce que c'est mieux eq_nat_dec ou beq_nat ? ??? *)


Inductive typing : env -> term -> typ -> Prop :=
  | TVar : forall e x T, wf e -> get_type x e = Some T -> typing e (Var x) T
  | TLam : forall e t T1 T2, typing (ConsT T1 e) t T2 -> typing e (Lam T1 t) (Imp T1 T2)
  | TApp : forall e t1 t2 T1 T2, typing e t1 (Imp T1 T2) -> typing e t2 T1 -> typing e (App t1 t2) T2
  | TAbs : forall e t K T, typing (ConsK K e) t T -> typing e (Abs K t) (Forall K T)
  | TAppT : forall e t K T1 T2, typing e t (Forall K T1) -> kinding e T2 K -> typing e (AppT t T2) (tsubst 0 T2 T1).


Lemma kinding_wf : forall e T K, kinding e T K -> wf e.
Proof.
  intros e T K H. induction H.
  assumption. assumption.
  inversion IHkinding. assumption. (* tu utiliserais quoi à la place d'inversion ? *)
Qed.