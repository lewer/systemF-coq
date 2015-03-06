(* begin hide *)
Require Import "F01_Defs".
Require Import "F06_Regularity".
(* end hide *)
(** * II. Inférences de types et de kinds
Dans cette partie du projet nous proposons des algorithmes d'inférence de sorte et de type, puis nous montrons qu'ils fonctionnent correctement eu égard aux prédicats [kinding] et [typing] définis dans la #<a href="F01_Defs.html">#première partie#</a>#.*)

(** ** Inférence de sorte *)

(** [infer_kind e T] recherche la sorte du type [T] dans l'environnement [e]. *) 
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
(** *)


(** Et le lemme qui va avec : la sorte calculée par [infer_kind] est correcte si l'environnement est bien formé. *)
Lemma infer_kind_correct : forall T e K,
  wf e -> infer_kind e T = Some K -> kinding e T K .
(** *)
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
(** *)



(** ** Inférence de types  *)

(** Un petit utilitaire: on peut décider si deux types [T] et [U] sont égaux. *)
Lemma eq_typ_dec : forall (T U :typ), {T=U} + {T<>U}.
(** *)
Proof.
  decide equality; decide equality.
Qed.
(** *)


(** Comme précédemment, voici la fonction d'inférence de type. *)
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
(** *)


(** Et sa correction. *)
Lemma infer_type_correct : forall t e T, wf e -> infer_type e t = Some T -> typing e t T.
(** *)
Proof.
  induction t as [v|T1 t|t1 IHt1 t2 IHt2|K t|t IHt T2]; intros e T Hwf H; simpl in H.
  + now apply TVar.
  + destruct (infer_kind e T1) eqn:?; [|discriminate].
    destruct (infer_type (ConsT T1 e) t) eqn:?; [|discriminate].
    inv H. apply TLam. apply IHt; [|auto].
    apply (WfConsT _ _ k). now apply infer_kind_correct. assumption.
    pose Heqo0. apply IHt in e0. apply regularity in e0.
    destruct e0.
    eapply tshift_tshift_minus in H. rewrite H. assumption. reflexivity.
    econstructor. apply infer_kind_correct in Heqo; eassumption.
    assumption.
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
  + destruct (infer_kind e T2) as [K2|] eqn:?; [|discriminate].
    destruct (infer_type e t) as [T1|] eqn:?; [|discriminate].
    destruct T1 as [| |K1 T1]; try discriminate.
    destruct (leb K2 K1) eqn:?; [|discriminate]; comp.
    inversion H. apply (TAppT _ _ K1).
    - apply IHt; congruence.
    - apply (cumulativity _ _ K2). assumption.
      apply infer_kind_correct; congruence.
Qed.

(** La preuve de ce dernier lemme recèle une petite subtilité : pour montrer que le [tshift_minus] (de l'inférence) et le [thsift] (du typing) s'annulent, on a besoin d'utiliser le lemme [tshift_tshift_minus]. Mais pour utliser ce lemme, on a besoin de montrer qu'un type est bien formé alors que l'on sait seulement que c'est la conclusion d'un jugement de typage. On utilise donc la régularité du système, cette propriété étant démontrée dans la partie VI ([regularity]). *)
(** C'est ici, que le choix de n'avoir qu'une numérotation pour les types et les sortes à un impact. En effet, si nous avions choisi deux numérotations distinctes, il n'y aurait pas de [tshift] dans la définition de [typing] ni de [tshift_minus] dans l'inférence ... *)

(** #<script src="jquery.min.js"></script>#
    #<script src="coqjs.js"></script># *)