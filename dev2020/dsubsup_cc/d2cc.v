Require Import EqNat.
Require Import Equality.
Require Import List.
Require Import Lia.
Require Import PeanoNat.

Import Notations.

Declare Scope var_scope.
Declare Scope d_scope.
Declare Scope cc_scope.

(***************************************************************************
 * Variables and Contexts
 * ----------------------
 * We use a locally nameless style of representation. We use de Bruijn indices
 * for bound variables and de Bruijn levels for free variables.
 * [X] Free and bound variables
 * [X] Variable lookup *)

Definition fVar : Set := nat.
Definition bVar : Set := nat.

Inductive var : Set :=
  | varB : bVar -> var
  | varF : fVar -> var.

Notation "# i" := (varB i) (at level 0) : var_scope.
Notation "` x" := (varF x) (at level 0) : var_scope.
Notation "G ~ T" := (cons T G) (at level 50) : var_scope.
Notation "G +~ G'" := (G' ++ G) (at level 60) : var_scope.

Bind Scope var_scope with var.
Open Scope var_scope.

(* Lookup -- de Bruijn levels *)
Inductive lookup {ty} : list ty -> fVar -> ty -> Prop :=
  | last : forall G T, lookup (G ~ T) (length G) T
  | prev : forall G T U x, lookup G x T -> lookup (G ~ U) x T.

(****************************************************************************
 * Lemmas about lookup *)

(* If looking up de Bruijn level x in precontext G is valid, then 
x < length G. *)
Lemma lookup_lt : forall ty G x (T : ty), lookup G x T -> x < length G.
Proof.
  induction 1; simpl; lia.
Qed.

(* If x points to T in G, then x points to (f T) in (map f G). *)
Lemma lookup_map : forall {ty ty'} (f : ty -> ty') G x T,
  lookup G x T -> lookup (map f G) x (f T).
Proof.
  induction 1. 
  - simpl. replace (length G) with (length (map f G)).
    constructor. apply map_length. 
  - simpl. constructor. assumption.
Qed.

Lemma lookup_fail : forall ty G x (T : ty), 
  x >= length G -> ~ (lookup G x T).
Proof.
  unfold not. induction G.
  - inversion 2.
  - inversion 2; subst; simpl in H.
    + lia.
    + destruct (x =? length G) eqn:E.
      * apply beq_nat_true in E. lia.
      * apply beq_nat_false in E. eapply IHG with (x := x). lia. eassumption.
Qed.

Lemma lookup_drop_front : forall ty G G' x (T : ty),
  lookup G' x T <-> lookup (G +~ G') (x + length G)%nat T.
Proof.
  split.

  * induction G'.
    - inversion 1.
    - simpl. intros. destruct (x =? length G') eqn:E.
      + apply beq_nat_true in E. rewrite E. 
        replace (length G + length G')%nat with (length G' + length G)%nat.
        rewrite <- app_length.
        inversion H; subst.
        -- constructor.
        -- apply lookup_fail in H4. contradiction. lia.
        -- lia.
      + constructor. apply IHG'. inversion H; subst.
        -- rewrite <- beq_nat_refl in E. discriminate.
        -- assumption.

  * induction G.
    - rewrite app_nil_r. assert (x + 0 = x)%nat. lia. simpl. rewrite H. auto.
    - simpl. (* Needed for t_thin. *)
Qed.



Lemma length_elim_middle : forall ty G G' (T : ty), 
  length (G ~ T +~ G') = S (length (G +~ G')).
Proof.
  induction G'.
  - reflexivity.
  - simpl. intros. rewrite IHG'. reflexivity.
Qed.

Hint Resolve lookup_lt lookup_map length_elim_middle : core.  

Lemma split_nat : forall m n : nat, n <= m -> ((m - n) + n)%nat = m.
Proof. lia. Qed.
  

(***************************************************************************
 * System D<:>
 * -----------
 * [X] Presyntax
 * [X] Opening
 * [X] Context formation
 * [X] Type formation
 * [X] Typechecking
 * [X] Subtyping
 * [X] Splicing
 * [ ] Substitution
 * [ ] Evaluation
 * [ ] Optional: Locally closed predicate
 * - Required Lemmas (TBD) *)

Module D.

  (* Presyntax 
   * .........*)
  Inductive ty : Set :=
    | TBot : ty
    | TTop : ty
    | TAll : ty -> ty -> ty
    | TTyp : ty -> ty -> ty
    | TSel : var -> ty.

  Inductive tm : Set :=
    | tVar : var -> tm
    | tLam : ty -> tm -> tm
    | tApp : tm -> tm -> tm
    | tTyp : ty -> tm.

  Definition cx := list ty.

  Notation "\: T" := (tLam T) (at level 5) : d_scope.
  Notation "t $" := (tApp t) (at level 4) : d_scope.
  Coercion tVar : var >-> tm.

  Bind Scope d_scope with ty tm.
  Open Scope d_scope.

  (* Opening 
   * .......*)
  Reserved Notation "ty{ i :-> x }" (at level 50).
  Fixpoint openTy (i : bVar) (x : fVar) (T : ty) : ty :=
    match T with
    | TSel #j => TSel (if i =? j then `x else #j)
    | TBot | TTop | TSel `_ => T
    | TAll T1 T2 => TAll (ty{i :-> x} T1) (ty{S i :-> x} T2)
    | TTyp T1 T2 => TTyp (ty{i :-> x} T1) (ty{i :-> x} T2)
    end
    where "ty{ i :-> x }" := (openTy i x) : d_scope.

  Reserved Notation "tm{ i :-> x }" (at level 50).
  Fixpoint openTm (i : bVar) (x : fVar) (t : tm) : tm :=
    match t with
    | tVar #j => if i =? j then `x else #j
    | tVar `_ => t
    | \:T e => \:(ty{i :-> x} T) (tm{i :-> x} e)
    | e $ u => (tm{i :-> x} e) $ (tm{i :-> x} u)
    | tTyp T => tTyp (ty{i :-> x} T)
    end
    where "tm{ i :-> x }" := (openTm i x) : d_scope.

  Notation "T ^* x" := (openTy 0 x T) (at level 50).
  Notation "t ^^ x" := (openTm 0 x t) (at level 50).

  Reserved Notation "G |-d" (no associativity, at level 90).
  Reserved Notation "G |-ty T" (no associativity, at level 90).
  Reserved Notation "G |-tm t : T" (no associativity, at level 90,
                                    t at next level).
  Reserved Notation "G |-s T <: U" (no associativity, at level 90, 
                                    T at next level).

  (* Context Formation *)
  Inductive wfCx : cx -> Prop :=
    | wf_nil : nil |-d

    | wf_cons : forall G T,
        G |-d ->
        G |-ty T ->
        G ~ T |-d

    where "G |-d" := (wfCx G) : d_scope

  (* Type formation *)
  with wfTy : cx -> ty -> Prop :=
    | wf_bot : forall G, G |-d -> G |-ty TBot
    | wf_top : forall G, G |-d -> G |-ty TTop

    | wf_all : forall G T U,
        G |-ty T ->
        G ~ T |-ty U ^* (length G) ->
        G |-ty TAll T U

    | wf_typ : forall G T U,
        G |-ty T ->
        G |-ty U ->
        G |-ty TTyp T U

    | wf_sel : forall G x T U,
        G |-tm tVar x : TTyp T U ->
        G |-ty TSel x

    where "G |-ty T" := (wfTy G T) : d_scope

  (* Typechecking *)
  with hasType : cx -> tm -> ty -> Prop :=
    | t_var : forall G x T, 
        G |-d -> 
        lookup G x T -> 
        G |-tm `x : T

    | t_lam : forall G t T U,
        G |-ty T ->
        G ~ T |-tm t ^^ (length G) : U ^* (length G) ->
        G |-tm \:T t : TAll T U

    | t_app : forall G t u T U,
        G |-tm t : TAll T U ->
        G |-tm u : T ->
        G |-ty U ->
        G |-tm t $ u : U

    | t_dapp : forall G t x T U,
        G |-tm t : TAll T U ->
        G |-tm `x : T ->
        G |-tm t $ `x : U ^* x

    | t_typ : forall G T,
        G |-ty T ->
        G |-tm tTyp T : TTyp T T

    | t_sub : forall G t T U,
        G |-tm t : T ->
        G |-s T <: U ->
        G |-tm t : U

    where "G |-tm t : T" := (hasType G t T) : d_scope

  (* Subtyping *)
  with subtype : cx -> ty -> ty -> Prop :=
    | s_bot : forall G T, G |-ty T -> G |-s TBot <: T
    | s_top : forall G T, G |-ty T -> G |-s T <: TTop

    | s_all : forall G T U T' U',
        G |-s T' <: T ->
        G ~ T' |-s U ^* (length G) <: U' ^* (length G) ->
        G |-s TAll T U <: TAll T' U'

    | s_typ : forall G T U T' U',
        G |-s T' <: T ->
        G |-s U <: U' ->
        G |-s TTyp T U <: TTyp T' U'

    | s_sel1 : forall G x T U,
        G |-tm `x : TTyp T U ->
        G |-s T <: TSel `x

    | s_sel2 : forall G x T U,
        G |-tm `x : TTyp T U ->
        G |-s TSel `x <: U

    | s_refl : forall G T, G |-ty T -> G |-s T <: T
    
    | s_trans : forall G T U V,
        G |-s T <: U ->
        G |-s U <: V ->
        G |-s T <: V

    where "G |-s T <: U" := (subtype G T U) : d_scope.

  (* Splicing *)
  Reserved Notation "k +ty> T" (at level 45, right associativity).
  Fixpoint spliceTy (k : nat) (T : ty) : ty :=
    match T with
    | TSel `x => TSel (varF (if k <=? x then S x else x))
    | TBot | TTop | TSel #_ => T
    | TAll U V => TAll (k +ty> U) (k +ty> V)
    | TTyp U V => TTyp (k +ty> U) (k +ty> V)
    end
    where "k +ty> T" := (spliceTy k T) : d_scope.

  Reserved Notation "k +tm> t" (at level 45).
  Fixpoint spliceTm (k : nat) (t : tm) : tm :=
    match t with
    | tVar `x => varF (if k <=? x then S x else x)
    | tVar #_ => t
    | \:T e => \:(k +ty> T) (k +tm> e)
    | e $ u => (k +tm> e) $ (k +tm> u)
    | tTyp T => tTyp (k +ty> T)
    end
    where "k +tm> t" := (spliceTm k t).

End D.

(***************************************************************************
 * Calculus of Constructions
 * -------------------------
 * [X] Presyntax
 * [X] Opening
 * [X] Substitution
 * [X] Context formation
 * [X] Typechecking 
 * [X] Expression equality
 * [X] Splicing
 * [ ] Evaluation
 * [ ] Optional: Locally closed predicate
 * - Required Lemmas (TBD) 
 * Can you express expresssion equality in terms of beta reduction? Charguer
   does it here using locally nameless + cofinite quant, so we should be able
   to do the same. 
   https://github.com/charguer/formalmetacoq/blob/master/ln/CoC_Definitions.v
   However, it's not clear to me that this system can naively be extended with
   primite dependent tuples -- I'd have to prove that by hand. Pierce in 
   ATAPL states that CC can be extended with these, but his formulation of CC
   is weird, since he derives it by extending LF. 
   However, these lecture notes show that it can be done.
   http://www4.di.uminho.pt/~mjf/pub/PSVC-Lecture7.pdf
   TODO: Discuss this with Oliver and Tiark. *)

Module CC.

  (* Presyntax *)
  Inductive sort : Set := prop | type.

  Inductive expr : Set :=
    | TSort : sort -> expr
    | tVar : var -> expr
    | TAll : expr -> expr -> expr
    | tLam : expr -> expr -> expr
    | tApp : expr -> expr -> expr
    | TSig : expr -> expr -> expr
    | tPair : expr -> expr -> expr -> expr -> expr
    | tFst : expr -> expr
    | tSnd : expr -> expr.

  Definition cx := list expr.
  Definition env := list expr.

  Notation "\: T" := (tLam T) (at level 5) : cc_scope.
  Notation "t $" := (tApp t) (at level 4) : cc_scope.
  Notation "t & u :[ T ** U ]" := (tPair t u T U) (at level 4) : cc_scope.
  Coercion TSort : sort >-> expr.
  Coercion tVar : var >-> expr.

  Bind Scope cc_scope with expr.
  Open Scope cc_scope.

  (* Opening *)
  Reserved Notation "e{ i :-> x }" (at level 50).
  Fixpoint open (i : bVar) (e' e : expr) : expr :=
    match e with
    | tVar #j => if i =? j then e' else #j
    | TSort _ | tVar `_ => e
    | TAll T U => TAll (e{i :-> e'} T) (e{S i :-> e'} U)
    | \:T t => \:(e{i :-> e'} T) (e{S i :-> e'} t)
    | t $ u => (e{i :-> e'} t) $ (e{i :-> e'} u)
    | TSig T U => TSig (e{i :-> e'} T) (e{S i :-> e'} U)
    | t & u :[T ** U] => 
        (e{i :-> e'} t) & (e{i :-> e'} u) :[e{i :-> e'} T ** e{S i :-> e'} U]
    | tFst t => tFst (e{i :-> e'} t)
    | tSnd t => tSnd (e{i :-> e'} t)
    end
    where "e{ i :-> e' }" := (open i e') : cc_scope.

  Notation "e *^ u" := (open 0 u e) (at level 50).

  Reserved Notation "e ~~> u" (no associativity, at level 90).
  Reserved Notation "e == u" (no associativity, at level 90).
  Reserved Notation "G |-cc" (no associativity, at level 90).
  Reserved Notation "G |-e e : T" (no associativity, at level 90,
                                   e at next level).
  Reserved Notation "G |-q e == u : T" (no associativity, at level 90,
                                          u at next level).

  (* Closed expressions *)
  Inductive closed (b f : nat) : expr -> Prop :=
    | cl_sort : forall s : sort, closed b f s
    | cl_varF : forall x, x < f -> closed b f `x
    | cl_varB : forall i, i < f -> closed b f #i
    | cl_all : forall T U, 
        closed b f T -> closed (S b) f U -> closed b f (TAll T U)
    | cl_lam : forall T e,
        closed b f T -> closed (S b) f e -> closed b f (\:T e)
    | cl_app : forall t u,
        closed b f t -> closed b f u -> closed b f (t $ u)
    | cl_sig : forall T U,
        closed b f T -> closed (S b) f U -> closed b f (TSig T U)
    | cl_pair : forall t u T U,
        closed b f t -> closed b f u -> closed b f T -> closed (S b) f U ->
        closed b f (t & u :[T ** U])
    | cl_fst : forall t, closed b f t -> closed b f (tFst t)
    | cl_snd : forall t, closed b f t -> closed b f (tSnd t).

  (* Full beta-pi reduction *)
  (* TODO: Do we need eta equality? *)
  Inductive reduce : expr -> expr -> Prop :=
    | r_beta : forall T e u, (\:T e) $ u ~~> e *^ u
    | r_pi1 : forall e u T U, tFst (e & u :[T ** U]) ~~> e
    | r_pi2 : forall e u T U, tSnd (e & u :[T ** U]) ~~> u
    | r_all1 : forall T U T', T ~~> T' -> TAll T U ~~> TAll T' U
    | r_all2 : forall T U U', U ~~> U' -> TAll T U ~~> TAll T U'
    | r_lam1 : forall T e T', T ~~> T' -> \:T e ~~> \:T' e
    | r_lam2 : forall T e e', e ~~> e' -> \:T e ~~> \:T e'
    | r_app1 : forall e u e', e ~~> e' -> e $ u ~~> e' $ u
    | r_app2 : forall e u u', u ~~> u' -> e $ u ~~> e $ u'
    | r_sig1 : forall T U T', T ~~> T' -> TSig T U ~~> TSig T' U
    | r_sig2 : forall T U U', U ~~> U' -> TSig T U ~~> TSig T U'
    (* The lecture notes linked above don't mention adding these 
       substructural rules for pairs, but I think they're required, else
       we can't reduce inside tuples. *)
    | r_pair1 : forall t u T U t', 
        t ~~> t' -> (t & u :[T ** U]) ~~> (t' & u :[T ** U])
    | r_pair2 : forall t u T U u', 
        u ~~> u' -> (t & u :[T ** U]) ~~> (t & u' :[T ** U])
    | r_pair3 : forall t u T T' U, 
        T ~~> T' -> (t & u :[T ** U]) ~~> (t & u :[T' ** U])
    | r_pair4 : forall t u T U U',
        U ~~> U' -> (t & u :[T ** U]) ~~> (t & u :[T ** U'])
    | r_fst : forall t t', t ~~> t' -> tFst t ~~> tFst t'
    | r_snd : forall t t', t ~~> t' -> tSnd t ~~> tSnd t'
     where "e ~~> u" := (reduce e u) : cc_scope.
 
   (* Beta-pi equality *)
   Inductive equals : expr -> expr -> Prop :=
     | e_red : forall e u, e ~~> u -> e == u
     | e_refl : forall e, e == e
     | e_sym : forall e u, e == u -> u == e
     | e_trans : forall e u t, e == u -> u == t -> e == t
     where "e == u" := (equals e u) : cc_scope.
 
   (* Context formation *)
   Inductive wfCx : cx -> Prop :=
     | wf_nil : nil |-cc
 
     | wf_cons: forall G T s,
        G |-cc ->
        G |-e T : TSort s ->
        G ~ T |-cc

    where "G |-cc" := (wfCx G) : cc_scope

  (* Typechecking *)
  with hasType : cx -> expr -> expr -> Prop :=
    | t_ax : forall G, G |-cc -> G |-e prop : type

    | t_var : forall G x T,
        G |-cc ->
        lookup G x T ->
        G |-e `x : T

    | t_all : forall G T U sT sU,
        closed 1 (length G) U ->
        G |-e T : TSort sT ->
        G ~ T |-e U *^ varF (length G) : TSort sU ->
        G |-e TAll T U : TSort sU

    | t_lam : forall G T U e s,
        closed 0 (length G) (TAll T U) ->
        closed 1 (length G) e ->
        G |-e T : TSort s ->
        G ~ T |-e e *^ varF (length G) : U *^ varF (length G) ->
        G |-e \:T e : TAll T U

    | t_app : forall G T U t u,
        G |-e t : TAll T U ->
        G |-e u : T ->
        G |-e t $ u : U *^ u

    | t_sig : forall G T U sT sU,
        closed 1 (length G) U ->
        G |-e T : TSort sT ->
        G ~ T |-e U *^ varF (length G) : TSort sU ->
        G |-e TSig T U : TSort sU

    | t_pair : forall G T U s t u,
        G |-e TSig T U : TSort s ->
        G |-e t : T ->
        G |-e u : U *^ t ->
        G |-e t & u :[T ** U] : TSig T U

    | t_fst : forall G T U e,
        G |-e e : TSig T U ->
        G |-e tFst e : T

    | t_snd : forall G T U e,
        G |-e e : TSig T U ->
        G |-e tSnd e : U *^ (tFst e)

    | t_conv : forall G t T U,
        G |-e t : T ->
        T == U ->
        G |-e t : U
(*
    | t_weaken : forall G e T U,
        G |-e e : T ->
        G ~ U |-e e : T
 *)
    where "G |-e e : T" := (hasType G e T) : cc_scope.
  
  Hint Constructors wfCx hasType equals : Core.

  (* Size of an expression is the number of non-leaf nodes in the AST. *)
  Fixpoint esize_flat (e : expr) : nat :=
    match e with
    | TSort _ | tVar _ => 0
    | TAll T U | \:T U | T $ U | TSig T U => S (esize_flat T + esize_flat U)
    | t & u :[T ** U] => 
        S (esize_flat t + esize_flat u + esize_flat T + esize_flat U)
    | tFst t | tSnd t => S (esize_flat t)
    end.

  (* Opening an expression with a free variable does not change its size. *)
  Lemma esize_open : forall e x i, esize_flat e = esize_flat (e{i :-> `x} e).
  Proof.
    induction e; simpl; intros;
    try (rewrite <- IHe1; rewrite <- IHe2); 
    try (rewrite <- IHe3; rewrite <- IHe4);
    try rewrite <- IHe;
    try (destruct v; try destruct (i =? b)); reflexivity.
  Qed.

  (* A well-founded relation *)
  Inductive R : expr -> expr -> Prop :=
    | lt_all1 : forall T U, R T (TAll T U)
    | lt_all2 : forall T U (G : list expr), R (U *^ ` (length G)) (TAll T U)
    | lt_lam1 : forall T e, R T (\:T e)
    | lt_lam2 : forall T e (G : list expr), R (e *^ ` (length G)) (\:T e)
    | lt_app1 : forall t u, R t (t $ u)
    | lt_app2 : forall t u, R u (t $ u)
    | lt_sig1 : forall T U, R T (TSig T U)
    | lt_sig2 : forall T U (G : list expr), R (U *^ ` (length G)) (TSig T U)
    | lt_pair1 : forall t u T U, R t (t & u :[T ** U])
    | lt_pair2 : forall t u T U, R u (t & u :[T ** U])
    | lt_pairT : forall t u T U, R T (t & u :[T ** U])
    | lt_pairU : forall t u T U, R U (t & u :[T ** U])
    | lt_fst : forall t, R t (tFst t)
    | lt_snd : forall t, R t (tSnd t).

  (* Proof that R is well-founded. *)
  Lemma wfR' : forall n e, esize_flat e <= n -> Acc R e.
  Proof.
    induction n; destruct e; constructor; inversion 1; subst; simpl in *;
    try (apply IHn; try rewrite <- esize_open); lia.
  Qed.

  Lemma wfR : well_founded R.
  Proof.
    red. intros e. eapply wfR'. auto.
  Qed.

  (* Substitution *)
  Reserved Notation "e[ x :-> u ]" (at level 50).
  Fixpoint subst (x : fVar) (u e : expr) : expr :=
    match e with
    | tVar `y => if x =? y then u else `y
    | TSort _ | tVar #_ => e
    | TAll T U => TAll (e[x :-> u] T) (e[x :-> u] U)
    | \:T t => \:(e[x :-> u] T) (e[x:-> u] t)
    | t $ t' => (e[x :-> u] t) $ (e[x :-> u] t')
    | TSig T U => TSig (e[x :-> u] T) (e[x :-> u] U)
    | t & t' :[T ** U] => 
        (e[x :-> u] t) & (e[x :-> u] t') :[e[x :-> u] T ** e[x :-> u] U]
    | tFst t => tFst (e[x :-> u] t) 
    | tSnd t => tSnd (e[x :-> u] t)
    end
    where "e[ x :-> u ]" := (subst x u) : cc_scope.

  (* Splicing *)
  Reserved Notation "k +>" (at level 45, right associativity).
  Fixpoint splice (k : nat) (e : expr) : expr :=
    match e with
    | tVar `x => varF (if k <=? x then S x else x)
    | TSort _ | tVar #_ => e
    | TAll T U => TAll (k +> T) (k +> U)
    | \:T t => \:(k +> T) (k +> t)
    | t $ u => (k +> t) $ (k +> u)
    | TSig T U => TSig (k +> T) (k +> U)
    | t & u :[T ** U] => (k +> t) & (k +> u) :[k +> T ** k +> U]
    | tFst t => tFst (k +> t)
    | tSnd t => tSnd (k +> t)
    end
    where "k +>" := (splice k) : cc_scope.

  (* Unsplicing *)
  Reserved Notation "k -<" (at level 45, right associativity).
  Fixpoint unsplice (k : nat) (e : expr) : expr :=
    match e with
    | tVar `x => varF (if k <=? x then x - 1 else x)
    | TSort _ | tVar #_ => e
    | TAll T U => TAll (k -< T) (k -< U)
    | \:T t => \:(k -< T) (k -< t)
    | t $ u => (k -< t) $ (k -< u)
    | TSig T U => TSig (k -< T) (k -< U)
    | t & u :[T ** U] => (k -< t) & (k -< u) :[k -< T ** k -< U]
    | tFst t => tFst (k -< t)
    | tSnd t => tSnd (k -< t)
    end
    where "k -<" := (unsplice k) : cc_scope.
  (***************************************************************************
   * Lemmas about splicing and closedness *)

  (* Splicing distributes on opening. *)
  Lemma splice_open : forall e t k i, 
    k +> (e{i :-> t} e) = e{i :-> k +> t} (k +> e).
  Proof.
    induction e; simpl; intros; 
    try (rewrite IHe1; rewrite IHe2; try (rewrite IHe3; rewrite IHe4)); 
    try rewrite IHe;
    try reflexivity.
    - destruct v; simpl. 
      + destruct (i =? b) eqn:E; reflexivity.
      + reflexivity.
  Qed.

  (* Splicing at position f does not mutate an expression closed under f free
     variables. *)
  Lemma splice_closed : forall f e b, closed b f e -> f +> e = e.
  Proof.
    induction 1; simpl; 
    try (rewrite IHclosed1; rewrite IHclosed2);
    try (rewrite IHclosed3; rewrite IHclosed4);
    try rewrite IHclosed; try reflexivity.
    destruct (f <=? x) eqn:E.
    - apply Nat.leb_le in E. lia.
    - reflexivity.
  Qed.

  (* Splicing a sort does not change the sort. *)
  Lemma splice_sort : forall s k, TSort s = k +> s.
  Proof. reflexivity. Qed.

  Hint Resolve splice_open splice_closed splice_sort : core.

  (* Closedness is monotonic in b and f. *)
  Lemma closed_monotonic : forall e b f,
    closed b f e ->
    forall b' f', b <= b' -> f <= f' ->
    closed b' f' e.
  Proof.
    induction 1; try constructor; try lia; eauto; try apply IHclosed2; 
    try apply IHclosed4; lia.
  Qed.

  Hint Resolve closed_monotonic : core.

  (* Opening the outermost bound variable *)
  Lemma closed_open : forall e b f,
    closed (S b) f e ->
    forall u, closed b f u ->
    closed b f (e{b :-> u} e).
  Proof.
    induction e; simpl; inversion 1; subst; try constructor; eauto.
    destruct (b =? i) eqn:E. auto. apply beq_nat_false in E. constructor. lia.
  Qed.

  Hint Resolve closed_open : core.


  (**************************************************************************
   * Properties of full beta-pi reduction and equality *)

  Lemma e_sig1 : forall T1 T2, 
    T1 == T2 ->
    forall U, TSig T1 U == TSig T2 U.
  Proof.
    induction 1; intros.
    - eapply e_trans. apply e_red. apply r_sig1. eassumption. apply e_refl.
    - apply e_refl.
    - apply e_sym. apply IHequals.
    - eapply e_trans; auto.
  Qed.

  Hint Resolve e_sig1 : core.

  (* Splicing preserves reduction *)
  Lemma r_splice : forall e u,
    e ~~> u ->
    forall k, k +> e ~~> k +> u.
  Proof.
    induction 1; simpl; intros; try rewrite splice_open; constructor; auto.
  Qed.

  Hint Resolve r_splice : core.

  (* Splicing preserves equality *)
  Lemma e_splice : forall e u,
    e == u ->
    forall k, k +> e == k +> u.
  Proof.
    induction 1.
    - auto using e_red.
    - auto using e_refl.
    - auto using e_sym.
    - eauto using e_trans.
  Qed.


  (**************************************************************************
   * Inversion Lemmas *)
  Lemma hasType_inversion_sort : forall (s : sort) G T,
    G |-e s : T -> s = prop /\ (T == type).
  Proof.
    intros. remember (TSort s) as e. induction H; subst; try discriminate.
    - inversion Heqe. split. reflexivity. apply e_refl.
    - assert (TSort s = s) by reflexivity. apply IHhasType in H1. split.
      apply H1. eapply e_trans. apply e_sym. eassumption. apply H1.
  Qed.
  
  Lemma hasType_inversion_varB : forall i G T, ~ (G |-e #i : T).
  Proof.
    unfold not. intros. remember (tVar #i) as v. 
    induction H; try discriminate.
    apply IHhasType. assumption.
  Qed.

  Lemma hasType_inversion_varF : forall x G T,
    G |-e `x : T -> lookup G x T \/ exists U, lookup G x U /\ (U == T).
  Proof.
    intros x. remember (tVar `x) as v. induction 1; try discriminate; subst.
    - inversion Heqv. subst. left. assumption.
    - right. assert (tVar `x = `x). reflexivity. apply IHhasType in H1.
      destruct H1.
      + exists T. split; assumption.
      + do 2 destruct H1. exists x0. split. assumption. eapply e_trans.
        eassumption. assumption.
  Qed.

  Lemma hasType_inversion_all : forall T U G V,
    G |-e TAll T U : V -> 
    closed 1 (length G) U /\
    (exists sT : sort, G |-e T : sT) /\
    (exists sU : sort, (V == sU) /\ (G ~ T |-e U *^ ` (length G) : sU)).
  Proof.
    intros. remember (TAll T U) as e. induction H; subst; try discriminate.
    - inversion Heqe. subst. split. assumption. split. exists sT. assumption. 
      exists sU. split. apply e_refl. assumption.
    - intuition. destruct H1. destruct H4. destruct H3. exists x0. split.
      eapply e_trans. apply e_sym. eassumption. assumption. assumption.
  Qed.

  Lemma hasType_inversion_lam : forall T e G V,
    G |-e \:T e : V ->
    closed 1 (length G) e /\
    (exists sT : sort, G |-e T : sT) /\
    exists U, (V == TAll T U) /\
    (closed 0 (length G) (TAll T U)) /\
    (G ~ T |-e e *^ ` (length G) : U *^ ` (length G)).
  Proof.
    intros. remember (\:T e) as t. induction H; subst; try discriminate.
    - inversion Heqt. subst. split. assumption. split. exists s. assumption.
      exists U. split. apply e_refl. split; assumption.
    - intuition. destruct H1. destruct H4. destruct H3. destruct H4. 
      exists x0. split. eapply e_trans. apply e_sym. eassumption. assumption. 
      split; assumption.
  Qed.

  Lemma hasType_inversion_app : forall e u G V,
    G |-e e $ u : V ->
    exists U, (V == U *^ u) /\ 
    exists T, (G |-e e : TAll T U) /\ (G |-e u : T).
  Proof.
    intros. remember (e $ u) as t. induction H; subst; try discriminate.
    - inversion Heqt. subst. exists U. split. apply e_refl. exists T.
      split; assumption.
    - assert (e $ u = e $ u) by reflexivity. apply IHhasType in H1.
      do 2 destruct H1. do 2 destruct H2. exists x. split.
      + eapply e_trans. apply e_sym. eassumption. assumption.
      + exists x0. split; assumption.
  Qed.

  Lemma hasType_inversion_sig : forall T U G V,
    G |-e TSig T U : V -> 
    closed 1 (length G) U /\
    (exists sT : sort, G |-e T : sT) /\
    (exists sU : sort, (V == sU) /\ (G ~ T |-e U *^ ` (length G) : sU)).
  Proof.
    intros. remember (TSig T U) as e. induction H; subst; try discriminate.
    - inversion Heqe. subst. split. assumption. split. exists sT. assumption.
      exists sU. split. apply e_refl. assumption.
    - intuition. destruct H1. destruct H4. destruct H3. exists x0. split. 
      eapply e_trans. apply e_sym. eassumption. assumption. assumption.
  Qed.

  Lemma hasType_inversion_pair : forall t u T G U V,
    G |-e (t & u :[T ** U]) : V ->
    (V == TSig T U) /\
    (G |-e t : T) /\
    (G |-e u : U *^ t) /\
    exists s : sort, G |-e TSig T U : s.
  Proof.
    intros. remember (t & u :[T ** U]) as e. 
    induction H; subst; try discriminate.
    - inversion Heqe. subst. split. apply e_refl. split. assumption.
      split. assumption. exists s. assumption.
    - intuition. eapply e_trans. apply e_sym. eassumption. assumption.
  Qed.

  Lemma hasType_inversion_fst : forall t G T,
    G |-e tFst t : T ->
    exists U, G |-e t : TSig T U.
  Proof.
    intros. remember (tFst t) as e. induction H; subst; try discriminate.
    - inversion Heqe. subst. exists U. assumption.
    - assert (tFst t = tFst t) by reflexivity. apply IHhasType in H1.
      destruct H1. exists x. eapply t_conv. eassumption. apply e_sig1.
      assumption.
  Qed.

  Lemma hasType_inversion_snd : forall t G V,
    G |-e tSnd t : V ->
    exists U, (V == U *^ tFst t) /\
    exists T, G |-e t : TSig T U.
  Proof.
    intros. remember (tSnd t) as e. induction H; subst; try discriminate.
    - inversion Heqe. subst. exists U. split. apply e_refl. exists T.
      assumption.
    - assert (tSnd t = tSnd t) by reflexivity. apply IHhasType in H1.
      do 2 destruct H1. destruct H2. exists x. split. eapply e_trans.
      apply e_sym. eassumption. assumption. exists x0. assumption.
  Qed.

  (***************************************************************************
   * Properties of expressions and types *)

  (* If an expression is well-typed under G, then G is a context. *)
  Theorem hasType_wfCx : forall G e T, G |-e e : T -> G |-cc.
  Proof.
    induction 1; try assumption.
  Qed.

  Hint Resolve hasType_wfCx : core.

  (* If an expression is well-typed under G, then the expression is closed
     under 0 bound variables and (length G) free variables. *)
  Theorem hasType_closed : forall G e T, G |-e e : T -> closed 0 (length G) e.
  Proof.
    induction 1; try constructor; try inversion IHhasType1; subst; eauto.
  Qed.

  Hint Resolve hasType_closed : core.

  (* Any pretype in a context is a type. *)
  Fixpoint wfCx_wfTy {G}
    (wfG : G |-cc)
    : forall T, In T G -> exists s : sort, G |-e T : s

  (* Splicing preserves well-typedness. *)
  with t_thin {G G' e T}
    (eT : G +~ G' |-e e : T)
        {U} (wfGUG' : G ~ U +~ map (length G +>) G' |-cc)
    : G ~ U +~ map (length G +>) G' |-e length G +> e : length G +> T.
  Proof.
    * induction wfG.
      - inversion 1.
      - intros.
        assert (G ~ T = G ~ T +~ map (length G +>) nil) by reflexivity.
        inversion H0; subst.
        + exists s. assert (T0 = length G +> T0). symmetry. eauto. 
          rewrite H1. rewrite H2. erewrite splice_sort. apply t_thin.
          assumption. econstructor. assumption. rewrite <- H2. eassumption.
        + assert (exists s : sort, G |-e T0 : s) by eauto. destruct H3.
          exists x. assert (T0 = length G +> T0). symmetry. eauto.
          rewrite H1. rewrite H4. erewrite splice_sort. apply t_thin.
          assumption. econstructor; eassumption.

    * remember (G +~ G') as GG'. destruct eT; subst.
      - constructor. assumption.
      - simpl. destruct (length G <=? x) eqn:E.
        + constructor. assumption. 
          assert (S x = (S x - length (G ~ U)) + length (G ~ U))%nat.
          { symmetry. eapply split_nat. apply Nat.leb_le in E. simpl. lia. }
          rewrite H1. apply lookup_drop_front. 
          assert (x = (x - length G) + length G)%nat.
          { simpl in H1. lia. }
          rewrite H2 in H0. 
          


  (* Any pretype in a context is a type. *)
  Theorem wfCx_lookup : forall G,
    G |-cc ->
    forall T, In T G ->
    exists s : sort, G |-e T : s

  (* Splicing preserves well-typedness. *)
  with t_thin : forall e G G' T,
    G +~ G' |-e e : T ->
    forall U, G ~ U +~ map (length G +>) G' |-cc ->
    G ~ U +~ map (length G +>) G' |-e length G +> e : length G +> T

  (* Splicing preserves beta-pi equivalence. *)
  with eq_splice : forall e u,
    e == u ->
    forall k, k +> e == k +> u

  (* Splicing preserves lookups on context. *)
  with lookup_splice : forall G' G,
    G +~ G' |-cc ->
    forall x T, lookup (G +~ G') x T ->
    forall U, G ~ U +~ map (length G +>) G' |-cc ->
    lookup (G ~ U +~ map (length G +>) G') 
      (if length G <=? x then S x else x) (length G +> T)

  (* Weakening rule *)
  with t_weak : forall G e T,
    G |-e e : T ->
    forall U, G ~ U |-cc ->
    G ~ U |-e e : T.
  Proof.
    * induction 1; inversion 1; subst. 
      - exists s0. apply t_weak. assumption. econstructor; eassumption. 
      - apply IHwfCx in H2 as H3. destruct H3. exists x. apply t_weak. 
        assumption. econstructor; eassumption.
    
    * induction e using (well_founded_induction wfR); intros; 
      apply hasType_wfCx in H0 as wfGG'; destruct e.
      - simpl. apply hasType_inversion_sort in H0. destruct H0.
        rewrite H0. econstructor. constructor. assumption.
        replace (TSort type) with (length G +> type). apply eq_splice. 
        apply e_sym. assumption. reflexivity.
      - destruct v.
        + apply hasType_inversion_varB in H0. contradiction.
        + apply hasType_inversion_varF in H0. destruct H0.
          -- constructor. assumption. apply lookup_splice. assumption.
             assumption. assumption.
          -- destruct H0. destruct H0. remember (length G +> T) as T'.
             eapply t_conv. constructor. assumption. apply lookup_splice.
             assumption. eassumption. assumption. subst. apply eq_splice.
             assumption.
      - simpl. apply hasType_inversion_all in H0. destruct H0.
        do 2 destruct H2. do 2 destruct H3. remember (length G +> T) as T'. 
        eapply t_conv. econstructor. admit (* Some lemma on closed splicing *).
        erewrite splice_sort. apply H. constructor. eassumption. assumption.
        assert (tVar ` (length (G ~ U +~ map (length G +>) G')) = 
                length G +> ` (length (G +~ G'))).
        { rewrite length_elim_middle. simpl. 
          replace (length G <=? length (G +~ G')) with true. 
          repeat rewrite app_length. rewrite map_length. reflexivity. 
          symmetry. rewrite Nat.leb_le. rewrite app_length. lia. }
        rewrite H4. rewrite <- splice_open. 
        assert ((G ~ U +~ map (length G +>) G') ~ length G +> e1 = 
                G ~ U +~ map (length G +>) (G' ~ e1)) by reflexivity.
        rewrite H5.
        assert (G ~ U +~ map (length G +>) (G' ~ e1)
                |-e length G +> (s0 *^ ` (length (G +~ G')))
                : length G +> x).
        { apply H. constructor. assumption. simpl. econstructor.
          assumption. erewrite splice_sort. apply H. constructor. eassumption.
          assumption. }
      - simpl. apply hasType_inversion_lam in H0. do 2 destruct H0.
        do 2 destruct H2. remember (length G +> T) as T'. econstructor.
        econstructor. erewrite splice_sort. apply H. constructor.
        eassumption. assumption. 
        assert (tVar ` (length (G ~ U +~ map (length G +>) G'))
                = length G +> ` (length (G +~ G'))).
        { rewrite length_elim_middle. repeat rewrite app_length. 
          rewrite map_length. simpl. 
          replace (length G <=? length G' + length G) with true. reflexivity.
          symmetry. apply Nat.leb_le. lia. }
        rewrite H4. 
        assert (G ~ U +~ map (length G +>) (G' ~ e1) 
                |-e length G +> (e2 *^ ` (length (G +~ G'))) 
                    : length G +> (x0 *^ ` (length (G +~ G')))).
        { apply H. constructor. simpl. eassumption. simpl. econstructor.
          assumption. erewrite splice_sort. apply H. constructor. eassumption.
          assumption. }
        assert (map (length G +>) G' ~ length G +> e1 
                = map (length G +>) (G' ~ e1)) by reflexivity.
        rewrite app_comm_cons. rewrite H6. repeat rewrite splice_open in H5.
        exact H5. subst. 
        replace (TAll (length G +> e1) (length G +> x0)) 
          with (length G +> (TAll e1 x0)). apply eq_splice. apply e_sym.
        assumption. reflexivity.
      - simpl. apply hasType_inversion_app in H0. do 2 destruct H0. 
        do 2 destruct H2. remember (length G +> T) as T'. econstructor.
        econstructor. 
        assert (G ~ U +~ map (length G +>) G' 
                |-e length G +> e1 
                : length G +> (TAll x0 x)).
        { apply H. constructor. assumption. assumption. }
        simpl in H4. exact H4. apply H. constructor. assumption. assumption.
        rewrite <- splice_open. subst. apply eq_splice. apply e_sym.
        assumption.
      - simpl. apply hasType_inversion_sig in H0. do 2 destruct H0.
        do 2 destruct H2. remember (length G +> T) as T'. 
        apply t_conv with (T := length G +> x0). econstructor.
        assert (forall s : sort, TSort s = length G +> s) by reflexivity.
        rewrite H4. apply H. constructor. eassumption. assumption.
        assert (tVar ` (length (G ~ U +~ map (length G +>) G')) = 
                length G +> ` (length (G +~ G'))).
        { rewrite length_elim_middle. simpl. 
          replace (length G <=? length (G +~ G')) with true. 
          repeat rewrite app_length. rewrite map_length. reflexivity. 
          symmetry. rewrite Nat.leb_le. rewrite app_length. lia. }
        rewrite H4. rewrite <- splice_open.
        assert ((G ~ U +~ map (length G +>) G') ~ length G +> e1 = 
                G ~ U +~ map (length G +>) (G' ~ e1)) by reflexivity.
        rewrite H5. assert (forall s, TSort s = length G +> s) by reflexivity.
        rewrite H6. apply H. constructor. apply H3. simpl. econstructor.
        assumption. rewrite H6. apply H. constructor. eassumption. assumption.
        subst. apply eq_splice. apply e_sym. assumption.
      - simpl. apply hasType_inversion_pair in H0. destruct H0. 
        do 2 destruct H2. do 2 destruct H3. destruct H4. destruct H5. subst.
        remember (length G +> T) as T'. simpl. econstructor. econstructor.
        econstructor. erewrite splice_sort. apply H. 
      - admit.
      - admit.
    

        
        

  (*************************************************************************
   * Embedding of System D<:> 
   * --------------------------------*)

  Definition tId (T : expr) := \:T #0.

  (* Presyntax *)
  Definition TBot := TAll prop #0.
  Definition TTop := TSig prop #0.
  
  Definition TTyp (T U : expr) := 
    TSig prop (TSig (TAll T #1) (TAll #1 U)).

  Definition TSel (x : var) := tFst x.

  Definition tTyp (T : expr) := 
    (T & 
      ((tId T) & (tId T) :[TSig (TAll T T) (TAll T T)])
    :[TSig prop (TSig (TAll #0 #1) (TAll #1 #2))]).
    { econstructor. eauto. simpl. repeat constructor. econstructor; eauto. }
    econstructor.
    - constructor. eauto.
    - simpl. econstructor.
      + rewrite H1. econstructor.
        * eassumption.
        * simpl. repeat constructor. econstructor; eauto.
      + simpl. econstructor.
        * repeat constructor. econstructor. eauto. rewrite H1. eassumption.
        * simpl. repeat rewrite H3. apply H4.
  Admitted.

  Lemma wf_sel : forall G x T U,
    G |-e tVar x : TTyp T U ->
    G |-* TSel x.
  Proof.
    econstructor. eassumption.
  Qed.

  (* Typechecking *)
  Lemma d_app' : forall G t u T U,
    G |-e t : TAll T U ->
    G |-e u : T ->
    G |-* U ->
    G |-e t $ u : U.
  Proof.
    econstructor.
    - econstructor; eassumption.
    - assert (U *^ u = U). admit (* TODO: From G |-* U *).
      rewrite H2. apply e_refl.
  Admitted.

  Lemma d_dapp : forall G t x T U,
    G |-e t : TAll T U ->
    G |-e `x : T ->
    G |-e t $ `x : U *^ `x.
  Proof.
    econstructor; eassumption.
  Qed.

  Lemma d_typ : forall G T,
    G |-* T ->
    G |-e tTyp T : TTyp T T.
  Proof.
    econstructor. econstructor.
    assert (G ~ TSort prop |-cc). { econstructor. eauto. constructor. eauto. }
    assert (G ~ TSort prop |-* ` (length G)). 
    { repeat constructor. assumption. }
    assert (forall T, 
      G ~ TSort prop |-* T -> G ~ TSort prop ~ T |-* ` (length G)).
    { repeat constructor. econstructor; eassumption. }
    assert (G ~ TSort prop |-* TAll ` (length G) ` (length G)).
    { econstructor. eassumption. simpl. apply H2. assumption. }
    assert (forall T,
      G ~ TSort prop |-* T ->
      G ~ TSort prop ~ T |-* TAll ` (length G) ` (length G)).
    { econstructor. apply H2. assumption. simpl. repeat constructor.
      econstructor. econstructor. assumption. eassumption. apply H2. 
      assumption. }
    econstructor. constructor. eauto. simpl. econstructor. eassumption.
    simpl. apply H4. assumption. assumption. simpl. eapply t_pair.
    econstructor. econstructor. eassumption. 
    assert (T *^ ` (length G) = T). admit (*TODO: H*). rewrite H0.
    admit (* TODO: weaken H *).
  Admitted.

  (* Subtyping *)
  Definition subtype G T U := exists e, G |-e e : TAll T U.
  Notation "G |-s' T <: U" := (subtype G T U) (no associativity, at level 90,
                                               T at next level).

  Lemma s_bot : forall G T, G |-* T -> G |-s' TBot <: T.
  Proof.
    intros. exists (\:TBot (#0 $ T)). econstructor. apply wf_bot. eauto.
    simpl. econstructor. econstructor. constructor. econstructor. eauto.
    econstructor. constructor. eauto. simpl. econstructor. econstructor.
    eauto. constructor. eauto. constructor. constructor. 
    admit (* Weaken H *). simpl. apply e_refl.
  Admitted.

  Lemma s_top : forall G T, G |-* T -> G |-s' T <: TTop.
  Proof.
    intros. exists (\:T (T & #0 :[TTop])). econstructor. eassumption.
    simpl.
  Admitted.

  (* TODO: Other subtyping rules. *)
 
End CC.

(***************************************************************************
 * Translation
 * -----------
 * [ ] Presyntax
 * -----------
 * [ ] Presyntax
 * [ ] Types
 * [ ] Contexts
 * [ ] Terms
 * [ ] Reduction preservation *)

Open Scope d_scope.
Open Scope cc_scope.Z
