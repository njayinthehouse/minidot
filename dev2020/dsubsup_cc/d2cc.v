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

Lemma lookup_app_front : forall ty G G' x (T : ty),
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

  * induction G'.
    - simpl. intros. assert (~ (lookup G (x + length G)%nat T)).
      { apply lookup_fail. lia. }
      contradiction.
    - inversion 1; subst.
      + assert (x = length G'). rewrite app_length in H3. lia. subst.
        constructor.
      + constructor. eauto.
Qed.

Lemma lookup_app_back : forall ty G x (T : ty),
  lookup G x T <-> forall G', lookup (G +~ G') x T.
Proof.
  split. 
  * induction G'. assumption. constructor. assumption.
  * intros. pose (H nil). assumption.
Qed.

Lemma lookup_app_back' : forall ty G' G x (T : ty),
  lookup G x T <-> x < length G /\ lookup (G +~ G') x T.
Proof.
  split.
  * split. eapply lookup_lt. eassumption.
    rewrite lookup_app_back in H. auto.
  * intuition. induction G'.
    - assumption.
    - apply IHG'. inversion H1; subst.
      + rewrite app_length in H0. lia.
      + assumption.
Qed.

Lemma length_elim_middle : forall ty G G' (T : ty), 
  length (G ~ T +~ G') = S (length (G +~ G')).
Proof.
  induction G'.
  - reflexivity.
  - simpl. intros. rewrite IHG'. reflexivity.
Qed.

Lemma lookup_in : forall ty G x (T : ty), lookup G x T -> In T G.
Proof.
  induction 1. 
  - simpl. left. reflexivity.
  - simpl. right. assumption.
Qed.

Hint Resolve lookup_lt lookup_map length_elim_middle lookup_in
             lookup_app_front lookup_app_back lookup_app_back' : core.  

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
        (* closedTy 1 (length G) U ->*)
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
        (* closedTm 0 (length G) (TAll T U) ->
           closedTm 1 (length G) t -> *)
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


  (* [TTop, TBot, TMem TBot TTop] |- TSel (varF 2)  *)

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
 * - Required Lemmas (TBD) *)

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
    | cl_varB : forall i, i < b -> closed b f #i
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

  (* For beta reduction, we need a way to decrement bound variables in the
     body of the abstraction. This is pretty upsetting, because what was the
     point of going with locally nameless representation if at the end I
     still need this operation, and all the lemmas that come with it? *)
  Fixpoint decrB' (i : nat) (e : expr) : expr :=
    match e with
    | tVar #j => if i <=? j then # (j - 1) else #j
    | TSort _ | tVar `_ => e
    | TAll T U => TAll (decrB' i T) (decrB' (S i) U)
    | \:T t => \:(decrB' i T) (decrB' (S i) t)
    | t $ t' => (decrB' i t) $ (decrB' i t')
    | TSig T U => TSig (decrB' i T) (decrB' (S i) U)
    | t & t' :[T ** U] =>
        (decrB' i t) & (decrB' i t')
        :[(decrB' i T) ** (decrB' (S i) U)]
    | tFst t => tFst (decrB' i t)
    | tSnd t => tSnd (decrB' i t)
    end.
  Definition decrB := decrB' 0.
  Notation "e ^$ u" := (decrB (e *^ u)) (at level 50).

  Hint Unfold decrB : core.

  (* Full beta-pi reduction *)
  (* Do we need eta equality? *)
  Inductive reduce : expr -> expr -> Prop :=
    | r_beta : forall T e u, (\:T e) $ u ~~> e ^$ u
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
        G ~ T |-e U *^ ` (length G) : TSort sU ->
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
        S (esize_flat t + esize_flat u + S (esize_flat T + esize_flat U))
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
    | lt_pair_sig : forall t u T U, R (TSig T U) (t & u :[T ** U])
    | lt_fst : forall t, R t (tFst t)
    | lt_snd : forall t, R t (tSnd t).

  (* Proof that R is well-founded. *)
  Lemma wfR' : forall n e, esize_flat e <= n -> Acc R e.
  Proof.
    induction n; destruct e; constructor; inversion 1; subst; simpl in *;
    try (apply IHn; try rewrite <- esize_open); simpl; lia.
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

  (* Splicing the domain and codomain of a dependent function type is the
     same as splicing the dependent function type. *)
  Lemma splice_all : forall T U k, TAll (k +> T) (k +> U) = k +> (TAll T U).
  Proof. reflexivity. Qed.

  (* Splicing the components of a sigma type is the same as splicing the
     sigma type. *)
  Lemma splice_sig : forall T U k, TSig (k +> T) (k +> U) = k +> (TSig T U).
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

  (* Opening the bth bound variable of a preterm that is closed under b 
     bound variables does not change the preterm. *)
  Lemma open_closed : forall e b f, 
    closed b f e -> 
    forall i, i >= b ->
    forall u, e{i :-> u} e = e.
  Proof.
    induction e; inversion 1; subst; simpl; intros;
    try erewrite IHe1; try erewrite IHe2;
    try erewrite IHe3; try erewrite IHe4;
    try erewrite IHe; eauto; try lia.
    - destruct (i0 =? i) eqn:E.
      + assert (i0 <> i) by lia. apply beq_nat_true in E. contradiction.
      + reflexivity.
  Qed.

  (* Splicing distributes on beta-opening *)
  Lemma splice_decrB : forall e k i, k +> (decrB' i e) = decrB' i (k +> e).
  Proof.
    induction e; simpl; intros; 
    try rewrite IHe1; try rewrite IHe2;
    try rewrite IHe3; try rewrite IHe4;
    try rewrite IHe; try reflexivity.
    destruct v; simpl.
    destruct (i <=? b); reflexivity.
    reflexivity.
  Qed.

  Fixpoint closed_open_front (e : expr) : forall be fe,
    closed (S be) fe e ->
    forall bt ft t, closed bt ft t ->
    forall b, be <= b -> bt <= b ->
    forall f, fe <= f -> ft <= f ->
    closed b f (e{b :-> t} e).
  Proof.
    destruct e; simpl; inversion 1; subst; intros;
    try constructor; try eapply closed_open_front; eauto; try lia.
    destruct (b =? i) eqn:E. eauto. constructor. apply beq_nat_false in E. 
    lia.
  Qed.

  Fixpoint closed_open_middle (e : expr) : forall be fe,
    closed be fe e ->
    forall bt ft t, closed bt ft t ->
    forall b, be <= b -> bt <= b ->
    forall f, fe <= f -> ft <= f ->
    forall i, i < b ->
    closed b f (e{i :-> t} e).
  Proof.
    destruct e; simpl; inversion 1; subst; intros;
    try constructor; try eapply closed_open_middle; eauto; try lia.
    destruct (i0 =? i) eqn:E. eauto. apply beq_nat_false in E. 
    constructor. lia.
  Qed.

  Lemma closed_decrB_id : forall e b f,
    closed b f e -> forall i, i >= b -> closed b f (decrB' i e).
  Proof.
    induction e; inversion 1; subst; simpl; 
    try constructor; eauto;
    try apply IHe2; try apply IHe4; try lia; eauto.
    intros j. destruct (j <=? i) eqn:E.
    - constructor. lia.
    - constructor. assert (i < j) by admit (* E *). lia.
  Admitted.

  Lemma closed_decrB : forall e b f,
    closed (S b) f e -> forall i, i < b -> closed b f (decrB' i e).
  Proof.
    induction e; inversion 1; subst; simpl;
    try constructor; auto;
    try apply IHe2; try apply IHe4; try lia; auto.
    simpl. intros j. destruct (j <=? i) eqn:E.
    - constructor. destruct b. lia. lia.
    - assert (i < j). admit (*E*). constructor.
      destruct (i =? b) eqn:E'. 
      + apply beq_nat_true in E'. subst. lia.
      + apply beq_nat_false in E'. lia.
  Admitted.

  Hint Rewrite splice_decrB : core.
  Hint Resolve closed_open_front closed_open_middle : core.

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
    induction 1; simpl; intros; try rewrite splice_open; try constructor; auto.
    unfold decrB. rewrite splice_decrB. rewrite splice_open. constructor.
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

  (* Closedness is preserved on reduction *)

  (**************************************************************************
   * Typing inversion Lemmas *)
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
    intros. remember (TAll T U) as T'. induction H; subst; try discriminate.
    - inversion HeqT'. subst. split. assumption. split. exists sT. assumption.
      exists sU. split. apply e_refl. assumption.
    - intuition. destruct H1, H4. exists x0. intuition. eapply e_trans.
      apply e_sym. eassumption. assumption.
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

  (* Any pretype in a context is closed under that context. *)
  Theorem wfCx_closed : forall G, 
    G |-cc -> forall T, In T G -> closed 0 (length G) T.
  Proof.
    induction 1. inversion 1. intros. destruct H1; subst.
    1: apply hasType_closed in H0. 
    1,2: eapply closed_monotonic. eassumption. lia.
         simpl. lia. apply IHwfCx. assumption. lia. simpl. lia.
  Qed.

  (* The prefix of any context is a context. *)
  Theorem wfCx_drop_back : forall G' G,
    G +~ G' |-cc -> G |-cc.
  Proof.
    induction G'. auto. inversion 1. subst. auto.
  Qed.

  Hint Resolve wfCx_closed wfCx_drop_back : core.

  (* Splicing preserves lookups on contexts. *)
  Corollary lookup_splice_wfCx : forall G' G,
    G +~ G' |-cc ->
    forall x T, lookup (G +~ G') x T ->
    forall U, G ~ U +~ map (length G +>) G' |-cc ->
    lookup (G ~ U +~ map (length G +>) G') (if length G <=? x then S x else x)
           (length G +> T).
  Proof.
    intros. destruct (length G <=? x) eqn:E.
    - apply Nat.leb_le in E. apply split_nat in E as E'. 
      assert (S x = S x - length (G ~ U) + length (G ~ U))%nat.
      { simpl. lia. }
      rewrite H2. apply lookup_app_front. simpl. apply lookup_map.
      rewrite lookup_app_front. rewrite <- E' in H0. eassumption.
    - assert (x < length G). admit (*E*). 
      assert (forall G0, G ~ U +~ G0 = G +~ (nil ~ U +~ G0)).
      { intros. rewrite <- app_assoc. reflexivity. }
      rewrite H3. apply lookup_app_back'.
      assert (lookup G x T). 
      { eapply lookup_app_back'. split. lia. eassumption. }
      assert (closed 0 (length G) T). apply lookup_in in H4. eauto. 
      assert (length G +> T = T). eauto.
      rewrite H6. assumption.
  Admitted.

  (* Splicing preserves closedness under contexts. *)
  Corollary closed_splice_wfCx : forall G' G,
    G +~ G' |-cc ->
    forall e b, closed b (length (G +~ G')) e ->
    forall U, closed b (length (G ~ U +~ map (length G +>) G'))
                (length G +> e).
  Proof.
    induction e; inversion 1; subst; simpl; constructor; eauto;
    try destruct (length G <=? x); rewrite length_elim_middle;
    rewrite app_length in *; rewrite map_length; lia.
  Qed.

  Hint Resolve lookup_splice_wfCx closed_splice_wfCx : core.

  (* Splicing preserves well-typedness. *)
  Lemma t_thin : forall e G G' T,
    G +~ G' |-e e : T ->
    forall U, G ~ U +~ map (length G +>) G' |-cc ->
    G ~ U +~ map (length G +>) G' |-e length G +> e : length G +> T.
  Proof.
    induction e using (well_founded_induction wfR). destruct e;
    intros G G' T eT U wfGUG'.
    - apply hasType_inversion_sort in eT. intuition. subst. econstructor.
      constructor. assumption. erewrite splice_sort. apply e_splice.
      apply e_sym. assumption.
    - destruct v.
      + apply hasType_inversion_varB in eT. contradiction.
      + apply hasType_inversion_varF in eT as fT. destruct fT.
        * constructor; eauto.
        * destruct H0. intuition. eapply t_conv. constructor; eauto.
          apply e_splice. assumption.
    - apply hasType_inversion_all in eT. intuition. destruct H2, H3.
      intuition. 
      assert (G ~ U +~ map (length G +>) G' |-e length G +> e1 : x).
      { erewrite splice_sort. apply H; eauto. constructor. }
      econstructor. simpl. apply t_all with (sT := x); eauto. 
      assert (tVar ` (length (G ~ U +~ map (length G +>) G'))
              = length G +> ` (length (G +~ G'))).
      { repeat rewrite app_length. rewrite map_length. simpl.
        assert (length G <= length G' + length G) by lia.
        apply Nat.leb_le in H5. rewrite H5. 
        rewrite plus_n_Sm. reflexivity. }
      rewrite H5. rewrite <- splice_open. erewrite splice_sort.
      assert (forall f T,
        (G ~ U +~ map f G') ~ f T = G ~ U +~ map f (G' ~ T))
        by reflexivity.
      rewrite H6. apply H; eauto. constructor. econstructor; eauto.
      erewrite splice_sort. apply e_splice. apply e_sym. assumption.
    - apply hasType_inversion_lam in eT. intuition. destruct H2, H3.
      intuition.
      assert (G ~ U +~ map (length G +>) G' |-e length G +> e1 : x).
      { erewrite splice_sort. apply H; eauto. constructor. }
      apply t_conv with (T := length G +> (TAll e1 x0)). 
      simpl. econstructor; eauto. inversion H2; subst. constructor; eauto.
      assert (tVar ` (length (G ~ U +~ map (length G +>) G'))
              = length G +> ` (length (G +~ G'))).
      { repeat rewrite app_length. rewrite map_length. simpl.
        assert (length G <= length G' + length G) by lia.
        apply Nat.leb_le in H6. rewrite H6. 
        rewrite plus_n_Sm. reflexivity. }
      rewrite H6. repeat rewrite <- splice_open.
      assert (forall f T,
        (G ~ U +~ map f G') ~ f T = G ~ U +~ map f (G' ~ T))
        by reflexivity.
      rewrite H7. apply H; eauto. constructor. econstructor; eauto.
      apply e_splice. apply e_sym. assumption.
    - apply hasType_inversion_app in eT. destruct eT. intuition. destruct H2.
      intuition. 
      simpl. apply t_conv with (T := length G +> (x *^ e2)).
      rewrite splice_open. apply t_app with (T := length G +> x0).
      rewrite splice_all. apply H; eauto. constructor. apply H; eauto. 
      constructor. apply e_splice. apply e_sym. assumption.
    - apply hasType_inversion_sig in eT. intuition. destruct H2, H3.
      intuition. 
      assert (G ~ U +~ map (length G +>) G' |-e length G +> e1 : x).
      { erewrite splice_sort. apply H; eauto. constructor. }
      econstructor. simpl. apply t_sig with (sT := x); eauto. 
      assert (tVar ` (length (G ~ U +~ map (length G +>) G'))
              = length G +> ` (length (G +~ G'))).
      { repeat rewrite app_length. rewrite map_length. simpl.
        assert (length G <= length G' + length G) by lia.
        apply Nat.leb_le in H5. rewrite H5. 
        rewrite plus_n_Sm. reflexivity. }
      rewrite H5. rewrite <- splice_open. erewrite splice_sort.
      assert (forall f T,
        (G ~ U +~ map f G') ~ f T = G ~ U +~ map f (G' ~ T))
        by reflexivity.
      rewrite H6. apply H; eauto. constructor. econstructor; eauto.
      erewrite splice_sort. apply e_splice. apply e_sym. assumption.
    - apply hasType_inversion_pair in eT. intuition. destruct H4.
      apply t_conv with (T := length G +> (TSig e3 e4)).
      simpl. econstructor. erewrite splice_sort. rewrite splice_sig.
      apply H; eauto. constructor. apply H; eauto. constructor.
      rewrite <- splice_open. apply H; eauto. constructor.
      apply e_splice. apply e_sym. assumption.
    - apply hasType_inversion_fst in eT. destruct eT.
      simpl. apply t_fst with (U := length G +> x). rewrite splice_sig.
      apply H; eauto. constructor.
    - apply hasType_inversion_snd in eT. destruct eT. intuition. destruct H2.
      simpl. apply t_conv with (T := length G +> (x *^ tFst e)).
      rewrite splice_open. apply t_snd with (T := length G +> x0).
      rewrite splice_sig. apply H; eauto. constructor. apply e_splice.
      apply e_sym. assumption.
  Qed.

  (* TODO: Mutual with e_closed variant *)
  Lemma hasType_closed' : forall G e T, G |-e e : T -> closed 0 (length G) T.
  Proof.
    induction 1.
    - constructor.
    - apply lookup_in in H0. eauto.
    - constructor.
    - assumption.
    - inversion IHhasType1; subst. eauto.
    - constructor.
    - eapply hasType_closed. eassumption.
    - inversion IHhasType. subst. assumption.
    - inversion IHhasType. subst. apply closed_open. assumption.
      constructor. eauto.
    - clear H. induction H0.
      + induction H.
        * intros. eapply closed_decrB_id; auto. 
          inversion IHhasType. inversion H1. subst. 
          apply closed_open; auto.
        * inversion IHhasType.
        * inversion 2. inversion H1. subst. auto.
        * inversion H0
  Qed.

  Hint Resolve hasType_closed' : core.

  Theorem t_weak : forall G e T, 
    G |-e e : T ->
    forall U, G ~ U |-cc ->
    G ~ U |-e e : T.
  Proof.
    intros. 
    assert (G ~ U = G ~ U +~ map (length G +>) nil) by reflexivity.
    assert (e = length G +> e). symmetry. eauto.
    assert (T = length G +> T). symmetry. eauto.
    rewrite H1. rewrite H2. rewrite H3. apply t_thin; assumption.
  Qed.

  Theorem wfCx_wfTy : forall G T,
    G |-cc ->
    In T G ->
    exists s : sort, G |-e T : s.
  Proof.
    induction G; inversion 2; inversion H; subst.
    - exists s. apply t_weak; eauto.
    - pose (IHG T H4 H1) as H'. destruct H'. exists x. apply t_weak; eauto.
  Qed.

  Hint Resolve t_weak wfCx_wfTy : core.
          
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
    ((tId T) & (tId T) :[TAll T T ** TAll T T])
    :[prop ** TSig (TAll T #1) (TAll #1 T)]).

  (* Coercions for subtyping *)
  Definition SBot (T : expr) := \:TBot (#0 $ T).
  Definition STop (T : expr) := \:T (T & #0 :[prop ** #0]).

  Definition SAll (T U T' U' : expr) (T'2T U2U' : expr) :=
    \:(TAll T U) (\:T' (U2U' $ (#1 $ (T'2T $ #0)))).

  Definition SSel1 (T U : expr) (x : var) := \:T ((tFst (tSnd x)) $ #0).
  Definition SSel2 (T U : expr) (x : var) := 
    \:(TSel x) ((tSnd (tSnd x)) $ #0).

  Definition STyp (T U T' U' T'2T U2U' : expr) :=
    \:(TTyp T U) ((tFst #0) & 
                  ((\:T' ((tFst (tSnd #1)) $ (T'2T $ #0))) &
                   (\:(tFst #0) (U2U' $ ((tSnd (tSnd #1)) $ #0)))
                   :[TAll T' (tFst #0) ** TAll (tFst #0) U'])
                   :[prop ** (TSig (TAll T' #0) (TAll #0 U'))]).

  (* Type formation *)
  Notation "G |-* T" := (hasType G T prop) (no associativity, at level 90).

  Corollary wf_bot : forall G, G |-cc -> G |-* TBot.
  Proof.
    repeat (constructor || assumption || econstructor).
  Qed.

  Corollary wf_top : forall G, G |-cc -> G |-* TTop.
  Proof.
    repeat (constructor || assumption || econstructor).
  Qed.

  Corollary wf_all : forall G T U, 
    closed 1 (length G) U ->
    G |-* T ->
    G ~ T |-* U *^ ` (length G) ->
    G |-* TAll T U.
  Proof.
    econstructor; eauto.
  Qed.

  Corollary wf_typ : forall G T U,
    G |-* T ->
    G |-* U ->
    G |-* TTyp T U.
  Proof.
    econstructor; simpl; repeat erewrite open_closed.
    3: econstructor; simpl; repeat erewrite open_closed.
    5: apply t_weak.
    6: econstructor.
    4,5,7: econstructor; simpl; repeat erewrite open_closed.
    6,14: apply t_weak.
    7,9: econstructor.
    5,8,10,14,18: repeat apply t_weak.
    13: econstructor.
    14,17,20,22: constructor.
    15,17,19,21: constructor.
    6,8,10,12-17,19-21,26: econstructor.
    1: constructor.
    1,2,4: constructor.
    1-49: try constructor; try lia; eauto 10.
  Qed.
  
  Corollary wf_sel : forall G T U x,
    G |-e tVar x : TTyp T U ->
    G |-* TSel x.
  Proof.
    econstructor. eassumption.
  Qed.

  (* Typechecking *)
  Corollary d_app : forall G t u T U,
    G |-e t : TAll T U ->
    G |-e u : T ->
    G |-* U ->
    G |-e t $ u : U.
  Proof.
    econstructor. econstructor; eassumption. erewrite open_closed. 
    apply e_refl. eauto. lia.
  Qed.

  Corollary d_dapp : forall G t x T U,
    G |-e t : TAll T U ->
    G |-e `x : T ->
    G |-e t $ `x : U *^ `x.
  Proof.
    econstructor; eauto.
  Qed.

  Corollary d_typ : forall G T,
    G |-* T ->
    G |-e tTyp T : TTyp T T.
  Proof.
    econstructor; simpl; repeat erewrite open_closed; eauto;
    econstructor; simpl; repeat erewrite open_closed; eauto;
    econstructor; simpl; repeat erewrite open_closed; eauto.
    1-3,6,9,10,12,13: constructor; eauto; try constructor; try constructor;
    eauto 10; try lia.
    2,4: apply t_weak; eauto.
    3,5: econstructor; eauto.
    1,2,4-9: econstructor; simpl; repeat erewrite open_closed; eauto 10.
    1,6: constructor; lia.
    11,13: constructor.
    1,2,4-9: apply t_weak; eauto.
    4: apply t_weak; eauto.
    12: constructor; try constructor; eauto.
    1-15: econstructor; eauto.
    3,11: constructor.
    7: constructor; try constructor.
    11: apply t_weak; eauto.
    4: apply t_weak; eauto.
    1-13: econstructor; eauto; econstructor; eauto.
  Qed.

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
Open Scope cc_scope.

Fixpoint d2ccTy (T : D.ty) : CC.expr :=
  match T with
  | D.TBot => CC.TBot
  | D.TTop => CC.TTop
  | D.TAll T U => CC.TAll (d2ccTy T) (d2ccTy U)
  | D.TTyp T U => CC.TTyp (d2ccTy T) (d2ccTy U)
  | D.TSel x => CC.TSel x
  end.

Fixpoint d2ccTm (t : D.tm) : CC.expr :=
  match t with
  | D.tVar v => CC.tVar v
  | D.tLam T e => CC.tLam (d2ccTy T) (d2ccTm e)
  | D.tApp t u => CC.tApp (d2ccTm t) (d2ccTm u)
  | D.tTyp T => CC.tTyp (d2ccTy T)
  end.

Definition d2ccCx (G : D.cx) : CC.cx := map d2ccTy G.

Coercion d2ccTy : D.ty >-> CC.expr.
Coercion d2ccTm : D.tm >-> CC.expr.
Coercion d2ccCx : D.cx >-> CC.cx.

(* TODO: 
 * 1. Teach Coq to translate over opening. 
 * 2. Teach Coq to translate closedness predicates? Might not be necessary.
 * 3. Find the right signature for translating hasType relations. *)
Fail Fixpoint d2ccWfCx {G} (wfG : D.wfCx G) : CC.wfCx G
with d2ccWfTy {G T} (wfT : D.wfTy G T) : CC.hasType G T (CC.TSort CC.prop)
with d2ccHasType {G e T} (eT : D.hasType G e T) 
  : _.
Proof.
  * destruct wfG.
    - constructor.
    - simpl. econstructor. 
      + apply d2ccWfCx. assumption. 
      + apply d2ccWfTy. assumption.

  * destruct wfT; simpl.
    - apply CC.wf_bot. apply d2ccWfCx. assumption.
    - apply CC.wf_top. apply d2ccWfCx. assumption.
    - apply CC.wf_all. 
      + apply d2ccWfTy. assumption.
      + admit (* TODO: Reason about opening *).
    - apply CC.wf_typ.
      + apply d2ccWfTy. assumption.
      + apply d2ccWfTy. assumption.
    - 
Abort.
(* Questions:
 * 1. What's wrong with r_closed and e_closed? How do I prove them? 
 * 2. The return type for the translation of hasType isn't very useful. Can
 *    we do better? *)
