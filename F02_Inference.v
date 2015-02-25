Require Import "F01_Defs".

(** * Inférence de kind  *)
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
  induction T; intros e K Hwf H.
  + econstructor; try eassumption. omega.
  + simpl in H.
    destruct (infer_kind e T1) eqn:?; [|discriminate].
    destruct (infer_kind e T2) eqn:?; [|discriminate].
    inv H. constructor; auto.
  + simpl in H.
    destruct (infer_kind (ConsK k e) T) eqn:?; [|discriminate].
    inv H. constructor. apply IHT. now constructor. easy.
Qed.

(** * Inférence de types  *)

(* On peut décider si deux types T et U sont égaux *)
Lemma eq_typ_dec : forall (T U :typ), {T=U} + {T<>U}.
Proof.
  decide equality; decide equality.
Qed.


Fixpoint infer_type (e:env) (t:term) :=
  match t with 
    | Var x => get_type x e
    | Lam T t => match (infer_kind e T, infer_type (ConsT T e) t) with
                   | (Some _, Some T') => Some (Arrow T (tshift_minus 0 T'))
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


Lemma infer_type_correct : forall t e T,
  wf e -> infer_type e t = Some T -> typing e t T.
Proof.
  induction t as [v|T1 t|t1 IHt1 t2 IHt2|K t|t IHt T2]; intros e T Hwf H; simpl in H.
  + now apply TVar.
  + destruct (infer_kind e T1) eqn:?; [|discriminate].
    destruct (infer_type (ConsT T1 e) t) eqn:?; [|discriminate].
    inv H. apply TLam. apply IHt; [|auto].
    apply (WfConsT _ _ k). now apply infer_kind_correct. assumption.
    assert (tshift 0 (tshift_minus 0 t0) = t0). admit.
    rewrite H. assumption.
  + destruct (infer_type e t1) as [T1|] eqn:?; [|discriminate].
    destruct T1 as [|T1 T2|]; try discriminate.
    destruct (infer_type e t2) as [T1'|] eqn:?; [|discriminate].
    destruct (eq_typ_dec T1 T1'); [|discriminate].
    inversion H. apply (TApp _ _ _ T1 T).
    - apply IHt1; auto. congruence.
    - apply IHt2; auto. congruence.
  + destruct (infer_type (ConsK K e) t) as [T1|] eqn:?; [|discriminate].
    inversion H. apply TAbs.
    apply IHt. now apply WfConsK. congruence.
  +  destruct (infer_kind e T2) as [K2|] eqn:?; [|discriminate].
     destruct (infer_type e t) as [T1|] eqn:?; [|discriminate].
     destruct T1 as [| |K1 T1]; try discriminate.
     destruct (leb K2 K1) eqn:?; [|discriminate]; comp.
     inversion H. apply (TAppT _ _ K1).
     - apply IHt; congruence.
     - apply (cumulativity _ _ K2). assumption.
       apply infer_kind_correct; congruence.
Qed.