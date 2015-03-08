Require Import "F01_Defs".
(** * VII. Normalisation
Dans cette dernière partie nous allons mettre en place les différents éléments nécessaire à la preuve de la normalisation. *)


(** ** Relation de réduction *)
(** Tout d'abord on définit une relation de réduction sur les termes du système F. Cela se fait en deux temps. D'abord on établit la définition d'un pas de réduction, puis on prend la clôture réflexive transitive de cette relation. Cependant un problème inattendu s'est posé à nous : il nous a été impossible d'utiliser directement la définiton [clos_refl_trans_n1] de la bibliothèque de Coq, et nous avons donc dû la redéfinir manuellement. Pour une raison inconnue, quand on veut appliquer le constructeur [rtn1_refl]
pour prouver [clos_refl_trans_n1], Coq produit une erreur d'unification. *)
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

(** La définition issue de la bibliothèque standard de Coq : *)
Inductive clos_refl_trans_n1 (x: term) : term -> Prop :=
    | rtn1_refl : clos_refl_trans_n1 x x
    | rtn1_trans (y z:term) :
        one_step_reduction y z -> clos_refl_trans_n1 x y -> clos_refl_trans_n1 x z.
(**  *)

(** Et donc notre relation de réduction : *)
Definition reduction := clos_refl_trans_n1. 
(**  *)

(** ** Proptiétés de congruence *)
(** Nous montrons maintenant que l'application et l'abstraction, de termes et de types, sont congruentes pour notre relation de réduction :  *)
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

(** Un terme est neutre si ce n'est ni une #&lambda;#-abstraction, ni une #&Lambda;#-abastraction : *)
Inductive neutral : term -> Prop :=
  |var_neutral : forall x, neutral (Var x)
  |app_neutral : forall t1 t2, neutral (App t1 t2)
  |appt_neutral : forall t T, neutral (AppT t T).
(** *)
                                     
(** On définit inductivement un prédicat [normal]. Dans le cas d'un terme appliqué à
un terme, ou d'un type appliqué à un terme, on s'assure que l'application ne
forme pas un redex. *)
Inductive normal : term -> Prop := 
  |var_normal : forall x, normal (Var x)
  |lam_normal : forall T t, normal t -> normal (Lam T t)
  |app_normal : forall t1 t2, normal t1 -> normal t2 -> 
                              neutral t1 -> normal (App t1 t2)
  |abs_normal : forall K t, normal t -> normal (Abs K t)
  |appt_normal : forall t T, normal t -> neutral t -> normal (AppT t T).
(** *)

(** *)
Lemma neutral_preserved_subst_typ : forall t X T, neutral t -> neutral (subst_typ X T t).
(**  *)
Proof.
intros t X T H.
induction t as [|U t|T1 H1 T2 H2|h|].
- assumption. 
- inversion H.  
- constructor.
- inversion H.
- constructor.
Qed. 
(** *)

Lemma normal_preserved_subst_typ : forall t X T, normal t -> normal (subst_typ X T t).
(**  *)
Proof.
intro t. induction t; intros X T H.
- assumption.
- simpl. constructor. apply IHt. inversion H; assumption.
- simpl. inversion H. constructor. 
    now apply IHt1.
    now apply IHt2.
    now apply neutral_preserved_subst_typ.
- simpl. constructor. apply IHt. inversion H; assumption.
- simpl. inversion H. constructor.
    now apply IHt.
    now apply neutral_preserved_subst_typ.
Qed.
(** *)

(** * Conclusion
Les indices de de Brujin permettent de raisonner sur des termes du #&Lambda;#-calcul 
sans se soucier des noms des variables et d'éventuels renommages.
Cependant, ils rendent parfois difficile la compréhension des énoncés de propositions,
ponctués de décalages d'indices. De plus, les démonstrations avec indices de de Bruijn ne
correspondent pas aux démonstrations faites sur papier, dans lesquelles on raisonne
informellement (mais rigoureusement) avec des arguments comme "quitte à renommer
les variables liées, on peut supposer la variable [x] libre dans [t]". 
D'autres approches existent pour représenter les termes du #&Lambda;#-calcul, 
comme par exemple les ensembles nominaux; le renommage des variables
s'exprime alors comme une permutation agissant sur un terme. Cette approche
permet des preuves machines similaires aux preuves papiers, mais n'est pas encore
formalisée dans Coq. Ceci sera l'objet de futurs travaux.
*) 

(** #<script src="jquery.min.js"></script>#
#<script src="coqjs.js"></script># *)