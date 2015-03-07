(**  *)
Require Import "F01_Defs".
Require Import Coq.Program.Equality.  (* needed for dependent induction *)
(** * IV. Affaiblissement par déclaration d'un type
Dans cette partie, nous étudions une deuxième forme d'affaiblissement de l'environnement : l'affaiblissement par ajout d'une déclaration d'une variable de terme. Cette fois, nous n'utilisons pas un prédicat inductif mais une fonction qui enlève une telle déclaration dans un environnement. En effet, nous pouvons cette fois nous permettre une telle fonction car quand l'on enlève une variable de terme dans un environnement bien formé il reste bien formé (ce qui n'était pas vrai avec les variables de type). *)


(** [remove_var] est la fonction telle que [remove_var x e] est l'environnement [e] dans lequel on a supprimé la déclaration de la variable de terme [x]. Si [x] est en fait une variable de type, le résultat a peu de sens. *)
Fixpoint remove_var x e {struct e} : env :=
  match e with
    | Nil => Nil
    | ConsK K e => match x with
                     | 0 => ConsK K e
                     | S x => ConsK K (remove_var x e)
                   end
    | ConsT T e => match x with
                     | 0 => e
                     | S x => ConsT (tshift_minus x T) (remove_var x e)
                   end
  end.
(**  *)


(** ** Préservation du typage  *)

(** Pour cet affaiblissement, nous n'avons montré la préservation que d'un des jugement de typage : [kinding]. Par contre, l'on montre ensuite une réciproque (ce qui est plus intéressant). *)

(** Dans tous les lemmes qui suivent les hypothèses [get_type e x = Some _] servent à s'assurer que la variable que l'on supprime est bien une variable de terme. Nous n'aurions pas besoin d'une telle hypothèse si nous avions choisit deux numérotations différentes pour les types et les sortes. *)

(**  *)
Lemma remove_var_get_kind_lt : forall X e x, X < x -> get_kind X e = get_kind X (remove_var x e).
(**  *)
Proof.
  induction X; intros.
  + destruct e.
    - reflexivity.
    - destruct x. inv H. reflexivity.
    - destruct x. inv H. reflexivity.
  + destruct e.
    - reflexivity.
    - destruct x. inv H. apply IHX. omega.
    - destruct x. inv H. apply IHX. omega.
Qed.
(**  *)

(**  *)
Lemma remove_var_get_kind_ge : forall X e x T, X >= x -> get_type x e = Some T -> get_kind (S X) e = get_kind X (remove_var x e).
(**  *)
Proof.
  induction X; intros.
  + destruct x. destruct e; try reflexivity.
    discriminate. inv H.
  + destruct e.
    - reflexivity.
    - destruct x. inv H0. simpl in H0.
      destruct (get_type x e) eqn:?. eapply IHX. omega.
      eassumption. discriminate.
    - destruct x. reflexivity.
      simpl in H0. destruct (get_type x e) eqn:?. eapply IHX. omega.
      eassumption. discriminate.
Qed.
(**  *)

(**  *)
Lemma kinding_remove_var : forall e x T K,
   kinding (remove_var x e) T K -> forall U, get_type x e = Some U -> wf e -> kinding e (tshift x T) K.
(**  *)
Proof.
  intros e x T K H U HU Hwf. dependent induction H; simpl.
  * destruct (leb x X) eqn:?; comp; econstructor; try eassumption.
    + erewrite remove_var_get_kind_ge; try eassumption. 
    + erewrite remove_var_get_kind_lt; try eassumption.
  * constructor; eauto.
  * constructor. eapply IHkinding. reflexivity.
    simpl. rewrite HU. reflexivity. now constructor.
Qed.
(**  *)

(** ** Réciproque  *)

(** Ici, nous montrons donc une réciproque à l'affaiblissement : nous montrons que les jugements de typage [wf] et [kinding], qui n'utilisent que les variables de type, sont préservés par suppression des variables de terme. *)

(** Une fois de plus, le lemme est prouvé par induction mutuelle sur [wf] et [kinding]. *)
Lemma remove_var_wf_kinding : 
  (forall e, wf e -> forall x U, get_type x e = Some U -> wf (remove_var x e))
     /\
        (forall e T K, kinding e T K -> forall x U, get_type x e = Some U -> kinding (remove_var x e) (tshift_minus x T) K).
(**  *)
Proof.
  apply wf_kinding_ind_mut; intros; simpl.
  + constructor.
  + destruct x; constructor. assumption.
    simpl in H0. destruct (get_type x e) eqn:?; [|discriminate].
    inv H0. now apply (H _ t).
  + destruct x. assumption.
    simpl in H1. destruct (get_type x e) eqn:?; [|discriminate].
    inv H1. econstructor. now apply (H _ t).
    now apply (H0 _ t).
  + destruct (leb x X) eqn:?; econstructor; eauto.
    - rewrite leb_iff in Heqb.
      specialize (get_get _ _ _ _ _ e0 H0). intros.
      destruct X. inv Heqb. now contradiction H1. simpl.
      rewrite <- minus_n_O.
      erewrite <- remove_var_get_kind_ge; try eassumption.
      inv Heqb. now contradiction H1. omega.
    - erewrite <- remove_var_get_kind_lt. assumption.
      now rewrite leb_iff_conv in Heqb.
  + constructor; eauto.
  + constructor. eapply (H (S x)). simpl.
    rewrite H0. reflexivity.
Qed.
(**  *)


(** #<script src="jquery.min.js"></script>#
    #<script src="coqjs.js"></script># *)