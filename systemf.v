Require Import Arith.
Require Import Bool.
Require Import Omega.
Require Import NPeano.
Require Import Max.

(* -------------------- I---- Defining the Type System -------------------- *)

(* ---- I.2 --- Definitions ---*)

(* Question 1 *)

Definition kind := nat.

Inductive typ : Type := 
  |TyVar : nat -> typ
  |Arrow : typ -> typ -> typ
  |FAll : kind -> typ -> typ.

(* c=cut, d=nb de fois à décaler *)
Fixpoint ty_shift_ty_aux (c:nat) (d:nat) (T:typ) {struct T}:=
  match T with
    | TyVar X => if le_dec c X then TyVar (S X) else T
    | Arrow T1 T2 => Arrow (ty_shift_ty_aux c d T1) (ty_shift_ty_aux c d T2)
    | FAll K T => FAll K (ty_shift_ty_aux (S c) d T)
  end.

Definition ty_shift_ty := ty_shift_ty_aux 0 1.

(* substitution de X par U dans T *)
Fixpoint tsubst (X:nat) (U:typ) (T:typ) :=
  match T with
    |TyVar m => if (eq_nat_dec X m) then U else T 
    |Arrow T1 T2 => Arrow (tsubst X U T1) (tsubst X U T2)
    |FAll Y T1 => FAll Y (tsubst (X+1) (ty_shift_ty U) T1)
  end.


(* Question 2 *)

Inductive term : Set :=
  |Var : nat -> term
  |Lam : typ -> term -> term
  |App : term -> term -> term
  |Abs : kind -> term -> term
  |AppT : term -> typ -> term.

(* Décale vers la droite les variables libres de type dans un terme.
i.e : TyVar(n) => TyVar(n+1) *)
(* c=cut, d=nb de fois à décaler *)
Fixpoint ty_shift_t_aux (c:nat) (d:nat) t:term :=
  match t with
    |Var _ => t
    |Lam T t1 => Lam T (ty_shift_t_aux (c+1) d t1)
    |App t1 t2 => App (ty_shift_t_aux c d t1) (ty_shift_t_aux c d t2)
    |Abs k t1 => Abs k (ty_shift_t_aux (c+1) d t1)
    |AppT t1 T => AppT (ty_shift_t_aux c d t1) (ty_shift_ty_aux c d T)
    end.

Definition ty_shift_t := ty_shift_t_aux 0 1.

(* Décale vers la droite les variables libres de terme dans un terme.
i.e : Var(n) => Var(n+1) *)
(* c=cut, d=nb de fois à décaler *)
Fixpoint t_shift_t_aux (c:nat) (d:nat) t:term :=
  match t with
    |Var x => if le_dec c x then Var (x+d) else Var x 
    |Lam T t1 => Lam T (t_shift_t_aux (c+1) d t1)
    |App t1 t2 => App (t_shift_t_aux c d t1) (t_shift_t_aux c d t1)
    |Abs k t1 => Abs k (t_shift_t_aux (c+1) d t1)
    |AppT t1 T => AppT (t_shift_t_aux c d t1) T
    end.

Definition t_shift_t := t_shift_t_aux 0 1.

Fixpoint subst_typ (X:nat) (U:typ) (t:term) :=
  match t with
    |Var _ => t
    |Lam T t1 => Lam T (subst_typ (X-1) (ty_shift_ty U) t1)
    |App t1 t2 => App (subst_typ X U t1) (subst_typ X U t2)
    |Abs k t1 => Abs k (subst_typ (X-1) (ty_shift_ty U) t1)
    |AppT t1 T => AppT (subst_typ X U t1) (tsubst X U T)
    end.

(* Substitution de x libre par t1 dans t2 *)
Fixpoint subst (x:nat) (t1:term) (t2:term) :=
  match t2 with
    |Var m => match lt_eq_lt_dec x m with (* x<m \/ x=m \/ x>m *)
      |inleft(left _) => t2
      |inleft(right _) => t1
      |inright(_) => t2
      end
    |Lam T t3 => Lam T (subst (x-1) (t_shift_t t1) t3)
    |App t3 t4 => App (subst x t1 t3) (subst x t1 t4)
    |Abs k t3 => Abs k (subst (x-1) (t_shift_t t1) t3)
    |AppT t3 T => AppT (subst x t1 t3) T
    end.

(* Question 3 *)

Inductive env : Set :=
  |Nil: env
  |ConsK : kind -> env -> env
  |ConsT : typ -> env -> env.

(*Soit e un environnement et X une variable de type, la fonction qui suit renvoie le kind e(X) 
 si défini, None sinon *)
Fixpoint get_kind (X:nat) (e:env) {struct e}:=
  match (e, X) with 
    |(ConsK T e1, 0) => Some T
    |(ConsK T e1, S n) => get_kind n e1
    |(ConsT t e1, S n) => get_kind n e1
    |_ => None
    end.

(*Soit e un environnement et X une variable de terme, la fonction qui suit
 renvoie e(x) si défini, None sinon *)
Fixpoint get_type (x:nat) (e:env) :=
  match (e, x) with 
    |(Nil,x) => None
    |(ConsK T e1, 0) => None
    |(ConsK T e1, S n) => get_type n e1
    |(ConsT t e1, 0) => Some t
    |(ConsT t e1, S n) => get_type n e1
    end.

(* Question 4 *)

(*
Fixpoint wf_env (e:env) :=
  match e with
    |Nil=> True
    |ConsK k e1 => wf_env e1
    |ConsT T e1 => (wf_env e1) /\ (exists p, (kinding e1 T (star p) ))
    end

with kinding (e:env) (T:typ) (k:kind) :=
  match (T, k) with
    |(TyVar X, star(q)) => (exists p, (((get_kind X e) = Some(star p)) /\ (p <= q))) /\ wf_env e
    |(FAll (star q) T1, star(r)) => exists p, ((kinding (ConsK (star q) e) T1 (star p)) /\ (r = (max p q)+1))
    |(Arrow T1 T2, star(r)) => (exists p, exists q, (kinding e T1 (star p) /\ (kinding e T2 (star q) /\ (r = (max p q)))))
    end.

Fixpoint typing (e:env) (t:term) (T:typ) :=
  match (t, T) with
    |(Var x, T) => ((get_type x e) = Some(T)) /\ wf_env e
    |(Lam T1 t1, Arrow T3 T2) => (T3=T1) /\ typing (ConsT T1 e) t1 T2
    |(App t1 t2, T2) => exists T1, ((typing e t1 (Arrow T1 T2)) /\ (typing e t2 T1))
    |(Abs (star p) t1, FAll (star q) T1) => (p=q) /\ typing (ConsK (star p) e) t T1
    |(AppT t1 T2, T3) => exists l, exists T1, (kinding e T2 (star l)) /\ typing e t1 (FAll (star l) T1) /\ (exists X, T3 = tsubst X T2 T1)
    |_ => False
    end.
*)

Fixpoint wf_typ (e:env) (T:typ) : bool :=
  match T with
    |TyVar X => match get_kind X e with
      |None => false
      |_ => true
      end
    |Arrow T1 T2 => wf_typ e T1 && wf_typ e T2
    |FAll k T2 => wf_typ (ConsK k e) T2
    end.

Fixpoint wf_env (e:env) : bool :=
   match e with
     |Nil=> true
     |ConsT T e => wf_typ e T && wf_env e
     |ConsK k e => wf_env e
     end.

Inductive kinding : env -> typ -> kind -> Prop :=
  |kinding_var : forall (e:env) (X:nat) (p q : nat),
    get_kind X e = Some p -> p <= q -> (wf_env e = true) -> kinding e (TyVar X) q
  
  |kinding_pourtout : forall (e:env) (T:typ) (p q:nat),
    kinding (ConsK q e) T p -> kinding e (FAll q T) (max p q + 1)
    
  |kinding_fleche : forall (e:env) (T1 T2:typ) (p q:nat),
    kinding e T1 p -> kinding e T2 q -> kinding e (Arrow T1 T2) (max p q).


Inductive typing : env -> term -> typ -> Prop :=
  |typing_var : forall (e:env) (x:nat) (T:typ),
    get_type x e = Some T -> (wf_env e = true) -> typing e (Var x) T

  |typing_small_lambda : forall (e:env) (t:term) (T1 T2: typ),
    typing (ConsT T1 e) t T2 -> typing e (Lam T1 t) (Arrow T1 T2)

  |typing_app_term : forall (e:env) (t1 t2 :term) (T1 T2 :typ),
    typing e t1 (Arrow T1 T2) -> typing e t2 T1 -> typing e (App t1 t2) T2

  |typing_big_lambda : forall (e:env) (t: term) (T: typ) (p:nat),
    typing (ConsK p e) t T -> typing e (Abs p t) (FAll p T)

  |typing_app_typ : forall (e:env) (t:term) (T1 T2:typ) (l:nat),
    typing e t (FAll l T1) -> kinding e T2 l -> typing e (AppT t T2) (tsubst 0 T2 T1).

(* Remarque : chacune des règles conserve les indices de Bruijn : on n'a pas besoin de faire des décalages *)

(* Question 5 *)

(* On peut décider si deux kinds k et l sont égaux *)
Lemma kind_eq_dec : forall (k l :kind), {k=l} + {k<>l}.
Proof.
decide equality.
Qed.

(* On peut décider si deux types T et U sont égaux *)
Lemma typ_eq_dec : forall (T U :typ), {T=U} + {T<>U}.
Proof.
decide equality; decide equality.
Qed.


Fixpoint infer_kind (e:env) (T:typ) :=
  match T with
    |TyVar X => if wf_env e then get_kind X e else None
    |FAll q T1 => match infer_kind (ConsK q e) T1 with 
          |None => None 
          |Some p => Some (max p q + 1)
          end
    |Arrow T1 T2 => match (infer_kind e T1, infer_kind e T2) with
          |(Some p, Some q) => Some (max p q)
          |_ => None
          end
     end.

Fixpoint infer_type (e:env) (t:term) :=
  match t with
   |Var x => if wf_env e then get_type x e else None
   |Lam T t1 => match infer_type (ConsT T e) t1 with
     |Some(U) => Some (Arrow T U)
     |None => None
     end
   |App t1 t2 => match (infer_type e t1, infer_type e t2) with
     |(Some (Arrow T1 T2), Some T3) => match typ_eq_dec T1 T3 with
       | left(_) => Some T2 (* T1 = T3 *)
       |_ => None
       end
     |_ => None
     end
   |Abs k t1 => match infer_type (ConsK k e) t1 with
     |Some T => Some (FAll k T)
     |_ => None
     end
   |AppT t1 T2 => match (infer_type e t1, infer_kind e T2) with
     |(Some (FAll k1 T1), Some (k2)) => match kind_eq_dec k1 k2 with
       |left(_) => Some (tsubst 0 T2 T1) (* k1 = k2 *)
       |_ => None end
     |_ => None
     end
  end.


Lemma kinference_correct : forall (T:typ) (e:env), 
  forall r, infer_kind e T = Some r -> kinding e T r.
Proof.
induction T as [q|T1 IH1 T2 IH2| k T];intros e r infer; simpl in infer.
- remember (wf_env e) as wf eqn:Hwf. 
  destruct (wf);[apply (kinding_var) with r;[apply infer|omega|symmetry;apply Hwf]|discriminate].
- remember (infer_kind e T1) as infT1 eqn:Hinft1; remember (infer_kind e T2) as infT2 eqn:Hinft2.
  destruct infT1 as [k1|];[destruct infT2 as [k2|];[|discriminate] |discriminate].
  injection infer; intro H1; rewrite <- H1.
  apply (kinding_fleche);[apply IH1;symmetry; apply Hinft1 | apply IH2; symmetry; apply Hinft2].
- remember (infer_kind (ConsK k e) T) as infT eqn:Hint. destruct infT as [l|];[|discriminate].
  injection infer; intro H1; rewrite <- H1; apply kinding_pourtout; apply IHT; symmetry; apply Hint.
Qed.

Lemma tinference_correct : forall (t:term) (e:env) (T:typ), 
  infer_type e t = Some (T) -> typing e t T.
Proof.
induction t as [n|T1 t|t1 IH1 t2 IH2|p t|t IH T2]; intro e.
- intros T infer. simpl in infer.
  remember (wf_env e) as wf eqn:Hwf.
  destruct wf;[apply typing_var;
    [apply infer |
    symmetry; apply Hwf] |
    discriminate].

- intros T1T2 infer; simpl in infer.
  remember (infer_type (ConsT T1 e) t) as T2 eqn:Hinft; destruct T2 as [T2|];[|discriminate].
  injection infer; intro H1; rewrite <- H1.
  apply typing_small_lambda;
    apply IHt; symmetry; assumption.

- intros T2 infer. simpl in infer.
  remember (infer_type e t1) as T1T2 eqn:Hinft1; remember (infer_type e t2) as T1 eqn:Hinft2.
  destruct T1T2 as [T1T2|];[|discriminate]. destruct T1T2 as [ |T1' T2'| ]; [discriminate| |discriminate].
  destruct T1 as [T1|];[|discriminate].
  remember (typ_eq_dec T1' T1) as eq_dec; destruct eq_dec as [T1eqT1'|]; [|discriminate].
  injection infer; intro H1; rewrite <- H1.
  apply typing_app_term with T1';
    [apply IH1; symmetry; apply Hinft1 |
    apply IH2; symmetry; rewrite T1eqT1'; apply Hinft2].

- intros allpT infer; simpl in infer.
  remember (infer_type (ConsK p e) t) as T; destruct T as [T|]; [|discriminate].
  injection infer; intro H1; rewrite <- H1.
  apply typing_big_lambda;
    apply IHt; symmetry; apply HeqT.

- intros T3 infer; simpl in infer.
  remember (infer_type e t) as all_lT1 eqn:Hinft; remember (infer_kind e T2) as l eqn:HinfT2.
  destruct all_lT1 as [all_lT1|]; [|discriminate]; destruct all_lT1 as [ | | l' T1]; [discriminate | discriminate |].
  destruct l as [l|]; [|discriminate].
  remember (kind_eq_dec l' l) as eq_dec; destruct eq_dec as [l'eql|];[|discriminate].
  injection infer; intro H1; rewrite <- H1.
  apply typing_app_typ with l';
    [apply IH; symmetry; apply Hinft | 
     apply kinference_correct; symmetry; rewrite l'eql; apply HinfT2].
Qed.

(* ---- I.2 --- Basic Metatheory ---*)

(* Par rapport à l'énoncé, on change l'ordre de quantification
en mettant e après T, pour que l'hypothèse d'induction soit applicable
à tous les contextes, ce qui est important pour le cas où T est un
type "pour tout" *)
SearchAbout max.
Lemma cumulativity : forall (T:typ) (e:env) (k1 k2:kind),
  kinding e T k1 -> k1 <= k2 -> kinding e T k2.
Proof.
induction T as [X|T1 IH1 T2 IH2 |l T1 IH];intro e; intros q s H0 H; simpl.
- inversion H0; apply kinding_var with p; trivial; omega.

- inversion H0 as [| |e' T1' T2' p r H1 H2 H3 H4 H5].
  assert (max s s = s) as Hs by apply (max_idempotent); rewrite <-Hs.
  assert (p <= q) by (rewrite <- H5; apply (Nat.le_max_l p r)).
  assert (r <= q) by (rewrite <- H5; apply (Nat.le_max_r p r)).
  apply kinding_fleche;
    [apply IH1 with p; [apply H2 | omega] | 
    apply IH2 with r; [apply H6 | omega]].
  
- inversion H0 as [| e' T p l'|].
  assert (p <= max p l) by apply (le_max_l).
  assert (l <= max p l) by apply (le_max_r).
  assert (p <= s-1) by omega; assert (l <= s-1) by omega.
  (* comment on démontre max (s-1) l + 1 = s en une seule étape, sans
  tous ces assert moches ? *)
  assert (max (s-1) l = s-1) by now (apply max_l). assert (s >= 1) by omega;
  assert (max (s-1) l + 1 = s) by omega.
  rewrite <- H12.
  apply kinding_pourtout.
  apply IH with p; [apply H5 | omega].
Qed.

(* ------ Type substitution ------ *)

Inductive insert_kind : nat -> env -> env -> Prop :=
  |extend : forall (e:env) (k:kind), insert_kind 0 e (ConsK k e)
  |insert_k :  
    forall (e1 e2:env) (n:nat) (k:kind), insert_kind n e1 e2 -> insert_kind (S n) (ConsK k e1) (ConsK k e2)
  |insert_t : 
    forall (e1 e2:env) (n:nat) (T:typ), insert_kind n e1 e2 -> insert_kind (S n) (ConsT T e1) (ConsT (ty_shift_ty_aux n 1 T) e2).

Lemma wf_typ_preserved_extension : forall (T:typ) (e:env),
  wf_typ e T=true -> forall (k:kind), wf_typ (ConsK k e) (ty_shift_ty T)=true.
Proof.
induction T; intro e.
- intros H k. apply H.
- intros. simpl in H. assert (wf_typ e T1=true /\ wf_typ e T2 = true) as [H1 H2] by ( now apply (andb_true_iff)).
  simpl. apply andb_true_iff. split; [now apply IHT1 | now apply IHT2].
- intros H l. simpl. apply IHT.


Lemma insert_kind_wf_typ : forall (n:nat) (T:typ) (e e':env),
  insert_kind n e e' -> (wf_typ e T=true) -> (wf_typ e' (ty_shift_ty_aux n 1 T) =true).
induction T as [X|T1 IH1 T2 IH2 |l T].
- intros e e' H1 H2.
  induction H1.
  + apply H2.
  + destruct X. 
    * trivial.
    * simpl. simpl in H2. 
      case (le_dec (S n) (S X)). intro. simpl.
      
    
SearchAbout le.





simpl in H0. simpl. apply andb_true_intro.
    apply andb_true_iff. apply andb_true_intro.
    assert (wf_typ Nil T1=true /\ wf_typ Nil T2=true) by (now apply andb_true_iff).
    destruct H1.
    split; now auto.
  + simpl. simpl in H0.  *)
    

Lemma insert_kind_wf_env : forall (k:kind) (e e':env), 
  insert_kind k e e' -> wf_env e = true -> wf_env e' = true.
Proof.
intros k. induction e as [ |l|T]; intro e'.
- intro H. now inversion H.
- intros H1 H2. simpl in H2. inversion H1 as [ | e1 e2 H3 H4 H5 H6 H7|].
  + now simpl.
  + simpl; apply IHe;[apply H5 | apply H2].
- intros H1 H2. simpl in H2. inversion H1 as [ | e1 e2 H3 H4 H5|].
  + now simpl.
  + simpl.



