(* begin hide *)
Require Export Utf8.
Require Export Arith.
Require Export Max.
Require Export Omega.
Require Export Relations.
(* end hide *)
(** * I. Définitions et utilitaires *)
(** ** Quelques tactiques personnalisées *)
(** [inv], un utilitaire pour se débarrasser des cas d'inversion triviaux *)
Ltac inv H := inversion H; try subst; clear H.
(** [comp], pour transformer les tests d'égalité booléens en des propriétés *)
Ltac comp :=
  rewrite ?leb_iff in *; rewrite ?leb_iff_conv in *;
  rewrite <- ?nat_compare_lt in *; rewrite <- ?nat_compare_gt in *; rewrite ?nat_compare_eq_iff in *.
(** [mysimpl], une tactique simpl capable de calculer [n + 0] et [0 + n] *)
Ltac mysimpl :=
  simpl; rewrite <- ?minus_n_O; rewrite <- ?plus_n_O; simpl.
(** ** Définitions de base *)

(**  On utilise des indices de de Bruijn pour représenter les termes. Les variables liées sont dénotées par des nombres indiquant le nombre de lieurs les séparant du leur. L'intérêt de cette notation est de simplifier les problèmes d'α-conversion. *)


(** [var] est le type des variables (l'indice en fait) et [kind] celui des sortes  *)
Definition var := nat.

Definition kind := nat.
(** On définit les types et les termes. *)
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

(** Un environnement est une liste de déclarations de sortes et de types. Ces déclarations sont ordonnées dans la liste de manière à respecter les indices de de Bruijn. Nous avons choisi pour cela d'utiliser la même numérotation pour les types que pour les termes. *)
Inductive env :=
  | Nil : env
  | ConsK : kind -> env -> env
  | ConsT : typ -> env -> env.

(** ** Utilitaires de substitutions *)

(** En raison de l'utilisation de la notation de de Bruijn, il convient de correctement mettre à jour les indices des variables lors des différentes opérations de substitutions par des termes ou des types. *)


(** [tshift c T] incrémente les variables [>= c] dans le type [T] *)
(* c=cutoff *)
Fixpoint tshift (c:var) (T:typ) {struct T} : typ :=
  match T with
    | TyVar X => if leb c X then TyVar (S X) else TyVar X
    | Arrow T1 T2 => Arrow (tshift c T1) (tshift c T2)
    | FAll K T => FAll K (tshift (S c) T)
  end.

(** Idem mais décrémente les variables [<=x] *)
Fixpoint tshift_minus (x : var) (T : typ) {struct T} : typ :=
  match T with
    | TyVar X => if leb x X then TyVar (X-1) else TyVar X
    | Arrow T1 T2 => Arrow (tshift_minus x T1) (tshift_minus x T2)
    | FAll K T0 => FAll K (tshift_minus (S x) T0)
  end.

(** [shift c t] incrémente les variables [>= c] dans le terme [t] *)
Fixpoint shift (c:var) (t:term) : term :=
  match t with
    | Var x => if leb c x then Var (S x) else Var x
    | Lam T t => Lam (tshift c T) (shift (S c) t)
    | App t1 t2 => App (shift c t1) (shift c t2)
    | Abs K t => Abs K (shift (S c) t)
    | AppT t T => AppT (shift c t) (tshift c T)
  end.

(** [tsubst (X:nat) (U:typ) (T:typ)] substitue [X] par le type [U] dans le type [T]. Il faut penser à "shifter" lorsque l'on traverse un [FAll], en raison du choix d'utiliser un unique compteur pour les types et les kinds dans l'environnement. *)
Fixpoint tsubst (X:nat) (U:typ) (T:typ) :=
  match T with
    | TyVar Y => match nat_compare X Y with
                   | Eq => U
                   | Gt => TyVar Y
                   | Lt => TyVar (Y-1)
                 end
    | Arrow T1 T2 => Arrow (tsubst X U T1) (tsubst X U T2)
    | FAll K T => FAll K (tsubst (S X) (tshift 0 U) T)
  end.


(** De même, [subst_typ X U t] substitue [X] par le type [U] dans le terme [t]. *)
Fixpoint subst_typ X U t :=
         match t with
             |Var _ => t
             |Lam T t1 => Lam (tsubst X U T) (subst_typ (S X) (tshift 0 U) t1)
             |App t1 t2 => App (subst_typ X U t1) (subst_typ X U t2)
             |Abs k t1 => Abs k (subst_typ (S X) (tshift 0 U) t1)
             |AppT t1 T => AppT (subst_typ X U t1) (tsubst X U T)
         end.

(** Enfin, [subst (x : nat) (t' : term) (t : term)] substitue [x] par le terme [t'] dans le terme [t] *)
Fixpoint subst (x : nat) (t' : term) t {struct t} :=
  match t with
  | Var y =>
      match nat_compare x y with
      | Eq => t'
      | Gt => Var y
      | Lt => Var (y - 1)
      end
  | Lam T t  => Lam T (subst (S x) (shift 0 t') t)
  | App t1 t2  => App (subst x t' t1) (subst x t' t2)
  | Abs k t => Abs k (subst x (shift 0 t') t)
  | AppT t T => AppT (subst x t' t) T
  end.

(** ** Utilitaires d'environnements *)

(** [get_kind X e] renvoie la sorte de la variable d'indice [X] dans l'environnement [e].
Attention aux décalages d'indices. *)
Fixpoint get_kind (X:var) (e:env) : option kind :=
  match (X, e) with
    | (0, ConsK K _) => Some K
    | (S X, ConsK _ e) => get_kind X e
    | (S X, ConsT _ e) => get_kind X e
    | _ => None
  end.

(** [get_type x e] renvoie le type de la variable d'indice [x] dans l'environnement [e]. *)
Fixpoint get_type (x:var) (e:env) :=
  match (x, e) with
    | (0, ConsT T _) => Some (tshift 0 T)
    | (S x, ConsK _ e) => option_map (tshift 0) (get_type x e)
    | (S x, ConsT _ e) => option_map (tshift 0) (get_type x e)
    | _ => None
  end.

(** [wf : env -> Prop] explicite le fait pour un environnement d'être bien formé. Il s'agit de vérifier que l'environnement résulte bien d'un empilement de kinds et de types et que le [kind] de tout [typ] présent dans l'environnement y est également présent. Cette dernière vérification est représentée  par le prédicat [kinding: env -> typ -> kind -> Prop]. *)
Inductive wf : env -> Prop :=
  | WfNil : wf Nil
  | WfConsK : forall K e, wf e -> wf (ConsK K e)
  | WfConsT : forall T e, forall K, kinding e T K -> wf e -> wf (ConsT T e)

with kinding : env -> typ -> kind -> Prop :=
  | KVar : forall e X p q, wf e -> get_kind X e = Some p -> (p <= q) -> kinding e (TyVar X) q
  | KArrow : forall e T1 T2 p q, kinding e T1 p -> kinding e T2 q -> kinding e (Arrow T1 T2) (max p q)
  | KFAll : forall e T p q, kinding (ConsK q e) T p -> kinding e (FAll q T) (S (max p q)).

(** Un type est donc [kindable] si il existe un kind tel que l'on puisse associer ce kind à ce type dans l'environnement. *)
Definition kindable e T := exists K, kinding e T K.


(** Enfin, nous définissons le prédicat [typing e t T] qui décrit le fait pour un terme [t] d'avoir le type [T] dans l'environnement [e]. *)
Inductive typing : env -> term -> typ -> Prop :=
  | TVar : forall e x T, wf e -> get_type x e = Some T -> typing e (Var x) T
  | TLam : forall e t T1 T2, typing (ConsT T1 e) t (tshift 0 T2) -> typing e (Lam T1 t) (Arrow T1 T2)
  | TApp : forall e t1 t2 T1 T2, typing e t1 (Arrow T1 T2) -> typing e t2 T1 -> typing e (App t1 t2) T2
  | TAbs : forall e t K T, typing (ConsK K e) t T -> typing e (Abs K t) (FAll K T)
  | TAppT : forall e t K T1 T2, typing e t (FAll K T1) -> kinding e T2 K -> typing e (AppT t T2) (tsubst 0 T2 T1).

(** ** Propriétés de ces utilitaires  *)

(** Nous commençons par quelques propriétés de commutativité qui se révèleront utiles par la suite. En voici une première sur [tshift]: *)
Lemma tshift_tshift : forall T c d,
                        tshift c (tshift (c+d) T) = tshift (S (c+d)) (tshift c T).
(** *)
Proof.
  induction T; intros; simpl.
  + destruct (leb (c+d) v) eqn:?; simpl; comp.
    * destruct (leb c v) eqn:?; comp; [simpl|omega].
      destruct (leb c (S v)) eqn:?; comp; [simpl|omega].
      destruct (leb (c+d) v) eqn:?; comp; [reflexivity|omega].
    * destruct (leb c v) eqn:?; comp. simpl.
      destruct (leb (c+d) v) eqn:?; comp; [omega|reflexivity].
      unfold tshift.
      destruct (leb (S (c+d)) v) eqn:?; comp; [omega|reflexivity]. 
  + now apply f_equal2.
  + apply f_equal. now specialize (IHT (S c) d).
Qed.

(** Son équivalent sur [tsubst]: *)
Lemma tsubst_tshift : forall T X Y U,
        tsubst X (tshift (X+Y) U) (tshift (S (X+Y)) T) = tshift (X+Y) (tsubst X U T).
(** *)
Proof.
  induction T; intros; simpl.
  + destruct v. now destruct X.
    mysimpl. destruct (nat_compare X (S v)) eqn:?; comp; simpl.
    * subst X. destruct (leb (S v+Y) v) eqn:?; comp; try omega.
      simpl. destruct (nat_compare v v) eqn:?; comp; try omega.
      reflexivity.
    * destruct (leb (X+Y) v) eqn:?; comp; simpl.
      destruct (nat_compare X (S (S v))) eqn:?; comp; try omega.
      reflexivity.
      destruct (nat_compare X (S v)) eqn:?; comp; try omega.
      now mysimpl.
    * destruct (leb (X+Y) v) eqn:?; comp; simpl; try omega.
      destruct (nat_compare X (S v)) eqn:?; comp; try omega.
      destruct (leb (X+Y) (S v)) eqn:?; comp; try omega.
      reflexivity.
  + apply f_equal2; auto.
  + apply f_equal. replace (S (X + Y)) with ((S X)+Y); [|omega].
    rewrite <- IHT. apply f_equal2; [|reflexivity].
    replace (X + Y) with (0+(X+Y)); [|omega].
    replace (S X + Y) with (S (0+(X+Y))); [|omega].
    apply tshift_tshift.
Qed.

(** On montre maintenant que [tshift_minus] est bien l'opération inverse de [tshift], ce qui fonctionne très bien dans un sens... *)
Lemma tshift_minus_tshift : forall T x, tshift_minus x (tshift x T) = T.
(** *)
Proof.
  induction T; intros x; simpl.
  + destruct (leb x v) eqn:?; comp; simpl. 
    destruct (leb x (S v)) eqn:?; comp.
    now rewrite <- minus_n_O. omega.
    destruct (leb x v) eqn:?; comp; auto; omega.
  + apply f_equal2; auto.
  + apply f_equal; auto.
Qed.


(** ...mais pas tout à fait dans l'autre, un lemme intermédiaire, [get_get] est nécessaire. Celui-ci montre qu'un kind et un type ne peuvent avoir le même indice dans l'environnement:  *)

Lemma get_get : forall X e x K T, get_kind X e = Some K -> get_type x e = Some T -> X<>x.
(** *)
Proof.
  induction X; intros.
  + intros eq. subst x. destruct e; discriminate.
  + intros eq. subst x. destruct e; try discriminate.
    - simpl in H0. destruct (get_type X e) eqn:?; [|discriminate].
      eapply IHX. eassumption. eassumption. reflexivity.
    - simpl in H0. destruct (get_type X e) eqn:?; [|discriminate].
      eapply IHX. eassumption. eassumption. reflexivity.
Qed.


(** Et enfin: *)

Lemma tshift_tshift_minus : forall T e x U K,
                              get_type x e = Some U -> kinding e T K ->
                              tshift x (tshift_minus x T) = T.
(** *)
Proof.
  induction T; intros; simpl.
  + destruct v; mysimpl.
    - destruct x; simpl. inv H0.
      now contradiction (get_get _ _ _ _ _ H3 H). reflexivity.
    - destruct (leb x (S v)) eqn:?; comp; simpl.
      destruct (leb x v) eqn:?; comp; simpl.
      reflexivity.
      inv H0. contradiction (get_get _ _ _ _ _ H3 H).
      apply le_antisym; omega.
      destruct (leb x (S v)) eqn:?; comp; simpl.
      omega. reflexivity.
  + inv H. inv H0. apply f_equal2; eauto.
  + inv H. inv H0. apply f_equal. eapply IHT; try eassumption.
    simpl. rewrite H2. reflexivity.
Qed.

(** ** Une propriété du [kinding]: la cumulativité *)

Lemma cumulativity : forall T e K1 K2, K1 <= K2 -> kinding e T K1 -> kinding e T K2.
(** *)
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

(** ** Induction mutuelle  *)

(** On a besoin de faire une induction mutuelle.  *)
Scheme wf_ind_mut := Induction for wf Sort Prop
with kinding_ind_mut := Induction for kinding Sort Prop.

Fact wf_kinding_ind_mut :
 ∀ (P : ∀ e : env, wf e → Prop) (P0 : ∀ (e : env) (t : typ) (k : kind), kinding e t k → Prop),
   P Nil WfNil
   → (∀ (K : kind) (e : env) (w : wf e), P e w →
                      P (ConsK K e) (WfConsK K e w))
   → (∀ (T : typ) (e : env) (K : kind) (k : kinding e T K), P0 e T K k → ∀ w : wf e, P e w →
                      P (ConsT T e) (WfConsT T e K k w))
   → (∀ (e : env) (X : var) (p : kind) (q : nat) (w : wf e), P e w → ∀ (e0 : get_kind X e = Some p) (l : p ≤ q),
                      P0 e (TyVar X) q (KVar e X p q w e0 l))
   → (∀ (e : env) (T1 T2 : typ) (p q : kind) (k : kinding e T1 p), P0 e T1 p k → ∀ k0 : kinding e T2 q, P0 e T2 q k0 →
                      P0 e (Arrow T1 T2) (max p q) (KArrow e T1 T2 p q k k0))
   → (∀ (e : env) (T : typ) (p q : kind) (k : kinding (ConsK q e) T p), P0 (ConsK q e) T p k →
                      P0 e (FAll q T) (S (max p q)) (KFAll e T p q k))
   → (∀ (e : env) (w : wf e), P e w) /\  (∀ (e : env) (t : typ) (k : kind) (k0 : kinding e t k), P0 e t k k0).
(** *)
Proof.
  intros. split. 
  apply (wf_ind_mut P P0); assumption.
  apply (kinding_ind_mut P P0); assumption.
Qed.



        




(** #<script src="jquery.min.js"></script>
<script src="coqjs.js"></script># *)