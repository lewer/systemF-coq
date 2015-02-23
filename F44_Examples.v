
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
