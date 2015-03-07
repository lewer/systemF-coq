Require Export Utf8.
Require Export Arith.
Require Export Max.
Require Export Omega.
Require Export Relations.
(** * I. Définitions et premières propriétés

Dans cette première partie, nous définissons les objets (environnements, termes, types et sortes) sur lesquels nous allons travailler. Nous avons choisit de représenter les lieurs avec des indices de de Bruijn, nous y définissons également les fonctions auxilliaires (shift, subst, etc.) et prouvons les lemmes de commutation nécessaires.*)


(** ** Quelques tactiques personnalisées *)
(** Nous avons définit quelques tactiques qui ont principalement utilisées dans le fin du développement. *)

(** [inv] permet d'y voir plus clair après une inversion. C'est très pratique, l'inconvénient est que nous perdons définivement tout contrôle des noms introduits. *)
Ltac inv H := inversion H; try subst; clear H.
(** Dans les fonctions auxilliaires (shift, subst, etc.) nous avons souvent besoin de comparer des entiers. Après avoir essayé d'utiliser des lemmes comme [le_dec], [eq_dec_nat], ... nous avons finalement trouvé plus pratique d'utiliser des booléens. L'avantage est que les fonctions [leb] et [nat_compare] peuvent calculer (on peut simplifier certaines expressions avec [simpl]). L'inconvénient est que, lorsque l'on fait des distinctions de cas avec [destruct], les hypothèses introduites sont de la forme [leb x y = true], ce qui est difficilement utilisable (notamment par [omega]).
La tactique [comp] tente de remédier à ce problème en réécrivant systématique les égalités de ce type. *)
Ltac comp :=
  rewrite ?leb_iff in *; rewrite ?leb_iff_conv in *;
  rewrite <- ?nat_compare_lt in *; rewrite <- ?nat_compare_gt in *; rewrite ?nat_compare_eq_iff in *.
(** [mysimpl], permet de simplifier les expressions [n + 0] et [n - 0], ce qui se révèle pratique ... *)
Ltac mysimpl :=
  simpl; rewrite <- ?minus_n_O; rewrite <- ?plus_n_O; simpl.
(** *)



(** ** Définitions de base *)

(** On définit ici les sortes ([kind]), les types ([typ]), les termes ([term]) et les environnements ([env]). *)
(** On utilise des indices de de Bruijn pour représenter les lieurs. Les variables liées sont dénotées par des entiers indiquant le nombre de lieurs les séparant du leur (type [var]). *)
(** Un environnement est une liste de déclarations de sortes et de types. Ces déclarations sont ordonnées dans la liste de manière à respecter les indices de de Bruijn. Suivant la suggestion du sujet, nous utilisons un seul environnement pour les déclarations de sortes et de types. Nous trouvons que c'est effectivement plus élégant : cela permet de garder trace de l'entrelacement des déclarations. Nous avons aussi choisit de n'avoir qu'une seule numérotation pour les types et les sortes (par exemple [TVar 0] pointe vers la variable en tête qui n'est pas nécessairement une variable de terme), mais nous avons un peu regretté ce choix. En effet, l'utilisation deux numérotations distinctes nous aurait permis de simplifier certains problèmes : par exemple, dans la fonction [remove_var], que faire quand l'on est censé enlever le type qui est en tête mais que c'est une sorte ? et aussi dans l'inférence de type (cf. fin de la #<a href="F01_Defs.html">#partie II#</a>#).*)
Definition var := nat.
(**  *)
Definition kind := nat.
(** *)
Inductive typ :=
  | TyVar : var -> typ
  | Arrow : typ -> typ -> typ
  | FAll : kind -> typ -> typ.
(**  *)
Inductive term :=
  | Var : var -> term
  | Lam : typ -> term -> term
  | App : term -> term -> term
  | Abs : kind -> term -> term
  | AppT : term -> typ -> term.
(** *)
Inductive env :=
  | Nil : env
  | ConsK : kind -> env -> env
  | ConsT : typ -> env -> env.
(** *)



(** ** Utilitaires de substitutions *)

(** En raison de l'utilisation de la notation de de Bruijn, il convient de correctement mettre à jour les indices des variables lors des différentes opérations de substitutions par des termes ou des types. *)

(** [tshift x T] incrémente les variables [>= x] dans le type [T]. *)
Fixpoint tshift (x:var) (T:typ) {struct T} : typ :=
  match T with
    | TyVar X => if leb x X then TyVar (S X) else TyVar X
    | Arrow T1 T2 => Arrow (tshift x T1) (tshift x T2)
    | FAll K T => FAll K (tshift (S x) T)
  end.
(** *)


(** Idem mais décrémente les variables [>=x]. *)
Fixpoint tshift_minus (x : var) (T : typ) {struct T} : typ :=
  match T with
    | TyVar X => if leb x X then TyVar (X-1) else TyVar X
    | Arrow T1 T2 => Arrow (tshift_minus x T1) (tshift_minus x T2)
    | FAll K T0 => FAll K (tshift_minus (S x) T0)
  end.
(** *)


(** [shift x t] incrémente les variables [>= x] dans le terme [t]. *)
Fixpoint shift (x:var) (t:term) : term :=
  match t with
    | Var y => if leb x y then Var (S y) else Var y
    | Lam T t => Lam (tshift x T) (shift (S x) t)
    | App t1 t2 => App (shift x t1) (shift x t2)
    | Abs K t => Abs K (shift (S x) t)
    | AppT t T => AppT (shift x t) (tshift x T)
  end.
(** *)


(** [tsubst X U T] substitue [X] par le type [U] dans le type [T]. Il faut penser à "shifter" lorsque l'on traverse un [FAll], en raison du choix d'utiliser un unique compteur pour les types et les kinds dans l'environnement. *)
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
(** *)


(** De même, [subst_typ X U t] substitue [X] par le type [U] dans le terme [t]. *)
Fixpoint subst_typ X U t :=
         match t with
             |Var _ => t
             |Lam T t1 => Lam (tsubst X U T) (subst_typ (S X) (tshift 0 U) t1)
             |App t1 t2 => App (subst_typ X U t1) (subst_typ X U t2)
             |Abs k t1 => Abs k (subst_typ (S X) (tshift 0 U) t1)
             |AppT t1 T => AppT (subst_typ X U t1) (tsubst X U T)
         end.
(** *)


(** Enfin, [subst (x : nat) (t' : term) (t : term)] substitue [x] par le terme [t'] dans le terme [t]. *)
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
(** *)



(** ** Jugements de typage *)
(** Nous avons besoin de deux fonctions auxiliaires pour accéder à l'environnement avant de pouvoir définir les trois jugements de typage. *)

(** [get_kind X e] renvoie la sorte de la variable d'indice [X] dans l'environnement [e]. Les indice d'un type dans un environnement réfèrent aux variables qui sont après lui dans cet environnement. On fait donc attention à décaler les indices pour que ceux du type que l'on renvoie réfèrent à l'environnement global. *)
Fixpoint get_kind (X:var) (e:env) : option kind :=
  match (X, e) with
    | (0, ConsK K _) => Some K
    | (S X, ConsK _ e) => get_kind X e
    | (S X, ConsT _ e) => get_kind X e
    | _ => None
  end.
(** *)


(** [get_type x e] renvoie le type de la variable d'indice [x] dans l'environnement [e]. *)
Fixpoint get_type (x:var) (e:env) :=
  match (x, e) with
    | (0, ConsT T _) => Some (tshift 0 T)
    | (S x, ConsK _ e) => option_map (tshift 0) (get_type x e)
    | (S x, ConsT _ e) => option_map (tshift 0) (get_type x e)
    | _ => None
  end.
(** *)


(** Il y a trois jugements de typage distincts à formaliser : le fait pour un environnement d'être bien formé, le fait pour un type d'avoir une certaine sorte, et le fait pour un terme d'avoir un certain type. On utlise des prédicats inductifs pour formaliser ces trois notions. *)
(** Ainsi [wf e] est dérivable (prouvable) ssi l'environnement est bien formé, [kinding e T K] est prouvable ssi le type [T] a la sorte [K] dans l'environnement [e] et [typing e t T] est dérivable ssi le terme [t] a le type [T] dans l'environnement [e]. La structure des termes de preuve de ces inductifs reflète parfaitement la structure de l'arbre de dérivation du jugement correspondant. *)

(** Contrairement à ce qui était suggeré, nous avons ici choisi  de définir [wf] et [kinding] mutuellement. Cela permet de rester plus fidèle à l'article. Nous trouvons intéressante l'idée de formaliser un résultat précis (à savoir, les théorèmes de l'article) et non pas "ce qui nous arrange" (à savoir, les mêmes théorèmes mais avec une définition de [wf] légèrement différente). Bien entendu, les deux formalisations sont équivalentes. D'ailleurs une autre approche possible aurait été d'utiliser la version modifiée de [wf] et de formaliser l'équivalence entre les deux. *)

(** Bien sûr, ce choix a impliqué certaines complications (preuves à faire par induction mutuelle) mais nous avons réussi à les surmonter. *)
Inductive wf : env -> Prop :=
  | WfNil : wf Nil
  | WfConsK : forall K e, wf e -> wf (ConsK K e)
  | WfConsT : forall T e, forall K, kinding e T K -> wf e -> wf (ConsT T e)

with kinding : env -> typ -> kind -> Prop :=
  | KVar : forall e X p q, wf e -> get_kind X e = Some p -> (p <= q) -> kinding e (TyVar X) q
  | KArrow : forall e T1 T2 p q, kinding e T1 p -> kinding e T2 q -> kinding e (Arrow T1 T2) (max p q)
  | KFAll : forall e T p q, kinding (ConsK q e) T p -> kinding e (FAll q T) (S (max p q)).
(** *)
Inductive typing : env -> term -> typ -> Prop :=
  | TVar : forall e x T, wf e -> get_type x e = Some T -> typing e (Var x) T
  | TLam : forall e t T1 T2, typing (ConsT T1 e) t (tshift 0 T2) -> typing e (Lam T1 t) (Arrow T1 T2)
  | TApp : forall e t1 t2 T1 T2, typing e t1 (Arrow T1 T2) -> typing e t2 T1 -> typing e (App t1 t2) T2
  | TAbs : forall e t K T, typing (ConsK K e) t T -> typing e (Abs K t) (FAll K T)
  | TAppT : forall e t K T1 T2, typing e t (FAll K T1) -> kinding e T2 K -> typing e (AppT t T2) (tsubst 0 T2 T1).
(** *)


(** Un type est donc [kindable] s'il existe une sorte qui puisse être associée à ce type dans l'environnement. *)
Definition kindable e T := exists K, kinding e T K.



(** ** Lemmes de commutation *)

(** Dans cette partie, nous prouvons les lemmes de commutation qu'implique l'utilisation des indices de de Bruijn. *)

(** Commutation de deux [tshift]. *)
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


(** Commutation d'un [tsubst] et d'un [tshift]. *)
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
(** *)


(** On montre maintenant que [tshift_minus] est bien l'opération inverse de [tshift], ce qui fonctionne très bien dans un sens ... *)
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
(** *)


(** ...mais pas tout à fait dans l'autre, un lemme intermédiaire, [get_get] est nécessaire. Celui-ci montre qu'une sorte et un type ne peuvent avoir le même indice dans l'environnement. *)
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
(** *)

(** Les deux hypothèses de ce lemme permettent de suposer qu'il y a bien une variable de terme (et non de type) en [x] et donc qu'elle n'apparaît pas dans [T]. *)
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
(** *)



(** ** Cumulativité *)
(** Ici, nous démontrons la première propriété non triviale du système : la cumulativité. La preuve est une induction immédiate, la seule difficultée est la manipulation des [max] que [omega] ne connaît pas ...  *)
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
(** *)



(** ** Induction mutuelle  *)
(** Pour faire les preuves par induction mutuelle, nous avons besoin d'un principe d'induction qui le permet contrairement à celui qui est généré automatiquement par Coq. On l'obtient grace à la commande suivante : *)
Scheme wf_ind_mut := Induction for wf Sort Prop
with kinding_ind_mut := Induction for kinding Sort Prop.

(** Cette version derivée de [wf_ind_mut] et [kinding_ind_mut] permet de montrer deux lemmes à la fois (il y a une conjonction dans la conclusion) sans refaire deux fois la preuve. *)
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