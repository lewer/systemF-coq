Require Import "F01_Defs".
(** * VII. Normalisation
*)

(**  *)
Inductive one_step_reduction : relation term :=
  |Lambda_reduction : forall K t T, 
                        one_step_reduction (AppT (Abs K t) T) (subst_typ 0 T t)
  |beta_reduction : forall T t t', 
                      one_step_reduction (App (Lam T t) t') (subst 0 t' t)
  |lambda_congruence : forall t t', one_step_reduction t t' →
         forall T, one_step_reduction (Lam T t) (Lam T t')
  |lapp_congruence : forall t t', one_step_reduction t t' →
         forall u, one_step_reduction (App u t) (App u t')
  |rapp_congruence : forall t t', one_step_reduction t t' →
         forall u, one_step_reduction (App t u) (App t' u)
  |abs_congruence : forall t t', one_step_reduction t t' →
         forall K, one_step_reduction (Abs K t) (Abs K t')
  |appt_congruence : forall t t', one_step_reduction t t' →
         forall T, one_step_reduction (AppT t T) (AppT t' T).
(**  *)

(** obligé de le redéfinir, celui de la bibliothèque
ne marche pas ??!!? *)
Inductive clos_refl_trans_n1 (x: term) : term -> Prop :=
    | rtn1_refl : clos_refl_trans_n1 x x
    | rtn1_trans (y z:term) :
        one_step_reduction y z -> clos_refl_trans_n1 x y -> clos_refl_trans_n1 x z.
(**  *)

(**  *)
Definition reduction := clos_refl_trans_n1. 
(**  *)

(**  *)
Lemma app_congruent : forall (t1 t2: term),
   reduction t1 t2 →  forall (u1 u2: term), reduction u1 u2 → reduction (App t1 u1) (App t2 u2).
(**  *)
Proof.
intros t1 t2 R1. induction R1 as [|t2 t3]; 
intros u1 u2 R2; induction R2 as [|u2 u3].
- constructor. 
- apply rtn1_trans with (App t1 u2).
  constructor. assumption. 
  assumption. 
- apply rtn1_trans with (App t2 u1).
  constructor. assumption. 
  apply IHR1. constructor.
- apply rtn1_trans with (App t2 u3).
  constructor. assumption.
  apply rtn1_trans with (App t2 u2).
  constructor. assumption.
  apply IHR1. assumption.
Qed.
(**  *)

(**  *)
Lemma lambda_congruent : forall (t1 t2: term) (T:typ),
   reduction t1 t2 -> reduction (Lam T t1) (Lam T t2).
(**  *)
Proof.
intros t1 t2 T H. induction H as [|t2 t3].
- constructor.
- apply rtn1_trans with (Lam T t2).
  now constructor.
  assumption.
Qed.
(**  *)

(**  *)
Lemma abs_congruent : forall (t1 t2: term) (K:kind),
   reduction t1 t2 -> reduction (Abs K t1) (Abs K t2).
(**  *)
Proof.
intros t1 t2 K H. induction H as [|t2 t3].
- constructor.
- apply rtn1_trans with (Abs K t2).
  now constructor.
  assumption.
Qed.
(**  *)

(**  *)
Lemma appt_congruent : forall (t1 t2: term) (T:typ),
   reduction t1 t2 -> reduction (AppT t1 T) (AppT t2 T).
(**  *)
Proof.
intros t1 t2 K H. induction H as [|t2 t3].
- constructor.
- apply rtn1_trans with (AppT t2 K).
  now constructor.
  assumption.
Qed.
(**  *)

(** #<script src="jquery.min.js"></script>#
    #<script src="coqjs.js"></script># *)