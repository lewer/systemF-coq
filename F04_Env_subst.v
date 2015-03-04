(* begin hide *)
Require Import "F01_Defs".
Require Import "F03_Insert_kind".
Require Import "F05_Remove_var".
(* end hide *)
(** * IV. Substitutions dans l'environnement 
Cette partie rassemble un enesemble de lemmes utilitaires étudiant le comportement de l'environnement lors de substitutions de types. *)


(** [env_subst : var -> typ -> env -> env -> Prop] définit la subtitution d'une variable par un type dans un environnement. *)
Inductive env_subst : var -> typ -> env -> env -> Prop :=
  |SubstSubst : forall T e K, kinding e T K  -> env_subst 0 T (ConsK K e) e
  |SubstConsK : forall X T e e', env_subst X T e e' -> 
                     forall K, env_subst (S X) (tshift 0 T) (ConsK K e) (ConsK K e')
  |SubstConsT : forall X T e e', env_subst X T e e' ->
                     forall U, env_subst (S X) (tshift 0 T) (ConsT U e) (ConsT (tsubst X T U) e').
(** *)


(** On montre que les kinds précedemment accessibles le sont toujours après une substitution, d'abord pour ceux placés avant la subtitutions... *)
Lemma env_subst_get_kind_gt : forall e e' X T, env_subst X T e e' -> forall Y, X>Y -> get_kind Y e = get_kind Y e'.
(** *)
Proof.
  intros e e' X T H. induction H; intros Y HY.
  + omega.
  + destruct Y; [reflexivity | apply IHenv_subst]. omega.
  + destruct Y; [reflexivity | apply IHenv_subst]. omega.
Qed.
(** *)


(** Puis pour ceux placés après: *)
Lemma env_subst_get_kind_lt : forall e e' X T, env_subst X T e e' -> forall Y, X<Y -> get_kind Y e = get_kind (Y-1) e'. 
Proof.
  intros e e' X T H. induction H; intros Y HY.
  + destruct Y. omega. simpl. rewrite <- minus_n_O. reflexivity.
  + destruct Y; [omega |simpl]. rewrite <- minus_n_O. destruct Y; [omega |]. rewrite (IHenv_subst (S Y)). simpl. now rewrite <- minus_n_O. omega.
  + destruct Y; [omega | simpl].  rewrite <- minus_n_O. destruct Y; [omega |]. rewrite (IHenv_subst (S Y)). simpl. now rewrite <- minus_n_O. omega.
Qed.
(** *)


(** On montre maintenant que what ? Ça devient kindable par magie ?^^ *) 
Lemma env_subst_kindable : forall e e' X T K, env_subst X T e e' -> wf e -> wf e' -> get_kind X e = Some K -> kinding e' T K.
Proof.
  intros e e' X T K H Hwf Hwf' Heq. induction H.
  + now inv Heq.
  + eapply insert_kind_wf_kinding.
    eapply IHenv_subst. now inv Hwf. now inv Hwf'. assumption.
    constructor.
  + eapply kinding_remove_var. simpl.
    apply IHenv_subst. now inv Hwf. now inv Hwf'.
    assumption. reflexivity. assumption.
Qed.


(** Et enfin, un second prédicat prouvable par induction mutuelle: La substitution d'une variable par un type dans un environnment préserve sa bonne forme et il en va de même pour le kinding. *)
Lemma env_subst_wf_kinding :
  (forall e, wf e -> forall e' X T, env_subst X T e e' -> wf e')
   /\
    (forall e U K, kinding e U K -> forall e' X T, env_subst X T e e' -> kinding e' (tsubst X T U) K).
Proof.
  apply wf_kinding_ind_mut.
  + intros e' X T H. inv H.
  + intros K e Hwf IH e' X T H. inv H.
    - assumption.
    - constructor. eapply IH. eassumption.
  + intros U e K k IH Hwf IH0 e' X T H. inv H.
    econstructor. now apply IH. eapply IH0. eassumption.
  + intros e Y p q Hwf IH eq l e' X T H. simpl.
    destruct (nat_compare X Y) eqn:eq2.
    - comp; subst. eapply cumulativity. eassumption.
      eapply env_subst_kindable; try eassumption. eauto.
    - econstructor; try eassumption. eapply IH; eassumption.
      erewrite <- env_subst_get_kind_lt; try eassumption.
      now apply nat_compare_lt in eq2.
    - econstructor; try eassumption. eapply IH; eassumption.
      erewrite <- env_subst_get_kind_gt; try eassumption.
      now apply nat_compare_gt in eq2.
  + intros e U1 U2 p q Hk1 IH1 Hk2 IH2 e' X T H. simpl.
    constructor; auto.
  + intros e U p q Hk IH e' X T H. simpl.
    constructor. apply IH. now constructor.
Qed.


(** #<script src="jquery.min.js"></script>#
    #<script src="coqjs.js"></script># *)