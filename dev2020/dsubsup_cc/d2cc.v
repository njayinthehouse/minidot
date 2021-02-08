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
    | tLam T t => tLam (e{i :-> e'} T) (e{S i :-> e'} t)
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
  Reserved Notation "G |-cc e : T" (no associativity, at level 90,
                                   e at next level).

  (* Closed expressions *)
  Inductive closed (b f : nat) : expr -> Prop :=
    | cl_sort : forall s : sort, closed b f s
    | cl_varF : forall x, x < f -> closed b f `x
    | cl_varB : forall i, i < b -> closed b f #i
    | cl_all : forall T U, 
        closed b f T -> closed (S b) f U -> closed b f (TAll T U)
    | cl_lam : forall T e,
        closed b f T -> closed (S b) f e -> closed b f (tLam T e)
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
    | tLam T t => tLam (decrB' i T) (decrB' (S i) t)
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

  (* Full beta-eta-pi reduction *)
  (* Do we need eta equality? *)
  Inductive reduce : expr -> expr -> Prop :=
    | r_beta : forall T e u, (tLam T e) $ u ~~> e ^$ u
    | r_pi1 : forall e u T U, tFst (e & u :[T ** U]) ~~> e
    | r_pi2 : forall e u T U, tSnd (e & u :[T ** U]) ~~> u
    | r_all1 : forall T U T', T ~~> T' -> TAll T U ~~> TAll T' U
    | r_all2 : forall T U U', U ~~> U' -> TAll T U ~~> TAll T U'
    | r_lam1 : forall T e T', T ~~> T' -> tLam T e ~~> tLam T' e
    | r_lam2 : forall T e e', e ~~> e' -> tLam T e ~~> tLam T e'
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
 
     | wf_snoc : forall G T s,
        G |-cc ->
        G |-cc T : TSort s ->
        G ~ T |-cc

    where "G |-cc" := (wfCx G) : cc_scope

  (* Typechecking *)
  with hasType : cx -> expr -> expr -> Prop :=
    | t_ax : forall G, G |-cc -> G |-cc prop : type

    | t_var : forall G x T,
        G |-cc ->
        lookup G x T ->
        G |-cc `x : T

    | t_all : forall G T U sT sU,
        closed 1 (length G) U ->
        G |-cc T : TSort sT ->
        G ~ T |-cc U *^ varF (length G) : TSort sU ->
        G |-cc TAll T U : TSort sU

    | t_lam : forall G T U e s,
        closed 0 (length G) (TAll T U) ->
        closed 1 (length G) e ->
        G |-cc T : TSort s ->
        G ~ T |-cc e *^ varF (length G) : U *^ varF (length G) ->
        G |-cc tLam T e : TAll T U

    | t_app : forall G T U t u,
        G |-cc t : TAll T U ->
        G |-cc u : T ->
        G |-cc t $ u : U *^ u

    | t_sig : forall G T U sT sU,
        closed 1 (length G) U ->
        G |-cc T : TSort sT ->
        G ~ T |-cc U *^ ` (length G) : TSort sU ->
        G |-cc TSig T U : TSort sU

    | t_pair : forall G T U s t u,
        G |-cc TSig T U : TSort s ->
        G |-cc t : T ->
        G |-cc u : U *^ t ->
        G |-cc t & u :[T ** U] : TSig T U

    | t_fst : forall G T U e,
        G |-cc e : TSig T U ->
        G |-cc tFst e : T

    | t_snd : forall G T U e,
        G |-cc e : TSig T U ->
        G |-cc tSnd e : U *^ (tFst e)

    | t_conv : forall G t T U (s : sort),
        G |-cc t : T ->
        G |-cc U : s ->
        T == U ->
        G |-cc t : U
    
    where "G |-cc e : T" := (hasType G e T) : cc_scope.
  
  Hint Constructors wfCx hasType equals : core.

  (* Size of an expression is the number of non-leaf nodes in the AST. *)
  Fixpoint esize_flat (e : expr) : nat :=
    match e with
    | TSort _ | tVar _ => 0
    | TAll T U | tLam T U | T $ U | TSig T U => S (esize_flat T + esize_flat U)
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
    | lt_lam1 : forall T e, R T (tLam T e)
    | lt_lam2 : forall T e (G : list expr), R (e *^ ` (length G)) (tLam T e)
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
    | tLam T t => tLam (e[x :-> u] T) (e[x:-> u] t)
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
    | tLam T t => tLam (k +> T) (k +> t)
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
    | tLam T t => tLam (k -< T) (k -< t)
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
    G |-cc s : T -> s = prop /\ (T == type).
  Proof.
    intros. remember (TSort s) as e. induction H; subst; try discriminate.
    - inversion Heqe. split. reflexivity. apply e_refl.
    - intuition. eapply e_trans. eapply e_sym. eassumption. eassumption.
  Qed.
  
  Lemma hasType_inversion_varB : forall i G T, ~ (G |-cc #i : T).
  Proof.
    unfold not. intros. remember (tVar #i) as v. 
    induction H; try discriminate; intuition.
  Qed.

  Lemma hasType_inversion_varF : forall x G T,
    G |-cc `x : T -> lookup G x T \/ exists U, lookup G x U /\ (U == T).
  Proof.
    intros. remember (tVar `x) as e. induction H; subst; try discriminate.
    - inversion Heqe. subst. intuition.
    - intuition. right. exists T. split; assumption. right. destruct H3.
      exists x0. destruct H2. split. auto. eapply e_trans; eassumption.
  Qed.

  Lemma hasType_inversion_all : forall T U G V,
    G |-cc TAll T U : V -> 
    closed 1 (length G) U /\
    (exists sT : sort, G |-cc T : sT) /\
    (exists sU : sort, (V == sU) /\ (G ~ T |-cc U *^ ` (length G) : sU)).
  Proof.
    intros. remember (TAll T U) as T'. induction H; subst; try discriminate.
    - inversion HeqT'. subst. split. assumption. split. exists sT. assumption.
      exists sU. split. apply e_refl. assumption.
    - intuition. destruct H5. exists x. split. eapply e_trans. apply e_sym.
      eassumption. intuition. intuition.
  Qed.

  Lemma hasType_inversion_lam : forall T e G V,
    G |-cc tLam T e : V ->
    closed 1 (length G) e /\
    (exists sT : sort, G |-cc T : sT) /\
    exists U, (V == TAll T U) /\
    (closed 0 (length G) (TAll T U)) /\
    (G ~ T |-cc e *^ ` (length G) : U *^ ` (length G)).
  Proof.
    intros. remember (tLam T e) as t. induction H; subst; try discriminate.
    - inversion Heqt. subst. split. assumption. split. exists s. assumption.
      exists U. split. apply e_refl. split; assumption.
    - intuition. destruct H5. exists x. intuition. eapply e_trans. 
      apply e_sym. eassumption. assumption.
  Qed.

  Lemma hasType_inversion_app : forall e u G V,
    G |-cc e $ u : V ->
    exists U, (V == U *^ u) /\ 
    exists T, (G |-cc e : TAll T U) /\ (G |-cc u : T).
  Proof.
    intros. remember (e $ u) as t. induction H; subst; try discriminate.
    - inversion Heqt. subst. exists U. split. apply e_refl. exists T.
      split; assumption.
    - intuition. destruct H2. exists x. intuition. eapply e_trans. 
      apply e_sym. eassumption. assumption.
  Qed.

  Lemma hasType_inversion_sig : forall T U G V,
    G |-cc TSig T U : V -> 
    closed 1 (length G) U /\
    (exists sT : sort, G |-cc T : sT) /\
    (exists sU : sort, (V == sU) /\ (G ~ T |-cc U *^ ` (length G) : sU)).
  Proof.
    intros. remember (TSig T U) as e. induction H; subst; try discriminate.
    - inversion Heqe. subst. split. assumption. split. exists sT. assumption.
      exists sU. split. apply e_refl. assumption.
    - intuition. destruct H5. exists x. intuition. eapply e_trans.
      apply e_sym. eassumption. assumption.
  Qed.

  Lemma hasType_inversion_pair : forall t u T G U V,
    G |-cc (t & u :[T ** U]) : V ->
    (V == TSig T U) /\
    (G |-cc t : T) /\
    (G |-cc u : U *^ t) /\
    exists s : sort, G |-cc TSig T U : s.
  Proof.
    intros. remember (t & u :[T ** U]) as e. 
    induction H; subst; try discriminate.
    - inversion Heqe. subst. split. apply e_refl. split. assumption.
      split. assumption. exists s. assumption.
    - intuition. eapply e_trans. apply e_sym. eassumption. assumption.
  Qed.

  (* TODO: Fix this. :( *)
  Lemma hasType_inversion_fst : forall t G T,
    G |-cc tFst t : T ->
    exists U, G |-cc t : TSig T U.
  Proof.
    intros. remember (tFst t) as e. induction H; subst; try discriminate.
    - inversion Heqe. subst. exists U. assumption.
    - intuition. destruct H2. exists x. econstructor. eassumption.
      econstructor.  eassumption. admit. apply e_sig1. assumption.
  Admitted.

  Lemma hasType_inversion_snd : forall t G V,
    G |-cc tSnd t : V ->
    exists U, (V == U *^ tFst t) /\
    exists T, G |-cc t : TSig T U.
  Proof.
    intros. remember (tSnd t) as e. induction H; subst; try discriminate.
    - inversion Heqe. subst. exists U. split. apply e_refl. exists T.
      assumption.
    - intuition. destruct H2. exists x. intuition. eapply e_trans; eauto.
  Qed.

  (***************************************************************************
   * Properties of expressions and types *)

  (* If an expression is well-typed under G, then G is a context. *)
  Theorem hasType_wfCx : forall G e T, G |-cc e : T -> G |-cc.
  Proof.
    induction 1; try assumption.
  Qed.

  Hint Resolve hasType_wfCx : core.

  (* If an expression is well-typed under G, then the expression is closed
     under 0 bound variables and (length G) free variables. *)
  Theorem hasType_closed : forall G e T, G |-cc e : T -> closed 0 (length G) e.
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
    G +~ G' |-cc e : T ->
    forall U, G ~ U +~ map (length G +>) G' |-cc ->
    G ~ U +~ map (length G +>) G' |-cc length G +> e : length G +> T.
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
      assert (G ~ U +~ map (length G +>) G' |-cc length G +> e1 : x).
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
      assert (G ~ U +~ map (length G +>) G' |-cc length G +> e1 : x).
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
      assert (G ~ U +~ map (length G +>) G' |-cc length G +> e1 : x).
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

  Theorem t_weak : forall G e T, 
    G |-cc e : T ->
    forall U, G ~ U |-cc ->
    G ~ U |-cc e : T.
  Proof.
    intros. 
    assert (length G +> e = e). eauto.
    assert (length G +> T = T).
    apply splice_closed with (b := 0). 
    admit (* T is closed.
           * Attempt 1: Prove that G |-cc e : T -> closed 0 (length G) T
           * Difficult because it's har
    *).
    replace (G ~ U) with (G ~ U +~ map (length G +>) nil) by reflexivity.
    rewrite <- H1. rewrite <- H2. apply t_thin; assumption.
  Admitted.

  Theorem wfCx_wfTy : forall G T,
    G |-cc ->
    In T G ->
    exists s : sort, G |-cc T : s.
  Proof.
    induction G; inversion 2; inversion H; subst.
    - exists s. apply t_weak; eauto.
    - pose (IHG T H4 H1) as H'. destruct H'. exists x. apply t_weak; eauto.
  Qed.

  Hint Resolve t_weak wfCx_wfTy : core.
          
  (*************************************************************************
   * Embedding of System D<:> 
   * --------------------------------*)

  Definition tId (T : expr) := tLam T #0.

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
  Definition SBot (T : expr) := tLam TBot (#0 $ T).
  Definition STop (T : expr) := tLam T (T & #0 :[prop ** #0]).

  Definition SAll (T U T' U' : expr) (T'2T U2U' : expr) :=
    tLam (TAll T U) (tLam T' (U2U' $ (#1 $ (T'2T $ #0)))).

  Definition SSel1 (T U : expr) (x : var) := tLam T ((tFst (tSnd x)) $ #0).
  Definition SSel2 (T U : expr) (x : var) := 
    tLam (TSel x) ((tSnd (tSnd x)) $ #0).

  Definition STyp (T U T' U' T'2T U2U' : expr) :=
    tLam (TTyp T U) ((tFst #0) & 
                  ((tLam T' ((tFst (tSnd #1)) $ (T'2T $ #0))) &
                   (tLam (tFst #0) (U2U' $ ((tSnd (tSnd #1)) $ #0)))
                   :[TAll T' (tFst #0) ** TAll (tFst #0) U'])
                   :[prop ** (TSig (TAll T' #0) (TAll #0 U'))]).

  Corollary wf_bot : forall G, G |-cc -> G |-cc TBot : prop.
  Proof.
    repeat (constructor || assumption || econstructor).
  Qed.

  Corollary wf_top : forall G, G |-cc -> G |-cc TTop : prop.
  Proof.
    repeat (constructor || assumption || econstructor).
  Qed.

  Corollary wf_all : forall G T U, 
    closed 1 (length G) U ->
    G |-cc T : prop ->
    G ~ T |-cc U *^ ` (length G) : prop ->
    G |-cc TAll T U : prop.
  Proof.
    econstructor; eauto.
  Qed.

  Corollary wf_typ : forall G T U,
    G |-cc T : prop ->
    G |-cc U : prop ->
    G |-cc TTyp T U : prop.
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
    G |-cc tVar x : TTyp T U ->
    G |-cc TSel x : prop.
  Proof.
    econstructor. eassumption.
  Qed.

  (* Typechecking *)
  Corollary d_app : forall G t u T U,
    G |-cc t : TAll T U ->
    G |-cc u : T ->
    G |-cc U : prop ->
    G |-cc t $ u : U.
  Proof.
    econstructor. econstructor; eassumption. erewrite open_closed. 
    apply e_refl. eauto. lia.
  Qed.

  Corollary d_dapp : forall G t x T U,
    G |-cc t : TAll T U ->
    G |-cc `x : T ->
    G |-cc t $ `x : U *^ `x.
  Proof.
    econstructor; eauto.
  Qed.

  Corollary d_typ : forall G T,
    G |-cc T : prop ->
    G |-cc tTyp T : TTyp T T.
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

Module D.

  Inductive expr : Type :=
    | TBot : expr
    | TTop : expr
    | tVar : var -> expr
    | TAll : expr -> expr -> expr
    | tLam : expr -> expr -> expr
    | tApp : expr -> expr -> expr
    | TTyp : expr -> expr -> expr
    | tTyp : expr -> expr
    | TSel : var -> expr.

  Definition cx := list expr.

  Coercion tVar : var >-> expr.
  Infix "$" := tApp (at level 5, left associativity) : d_scope.
  Coercion CC.TSort : CC.sort >-> CC.expr.
  Coercion CC.tVar : var >-> CC.expr.

  Open Scope d_scope.
  Open Scope cc_scope.

  Fixpoint open (i : bVar) (x : fVar) (e : expr) : expr :=
    match e with
    | tVar #j => tVar (if i =? j then `x else #j)
    | TSel #j => TSel (if i =? j then `x else #j)
    | TBot | TTop | tVar `_ | TSel `_ => e
    | TAll T U => TAll (open i x T) (open (S i) x U)
    | tLam T t => tLam (open i x T) (open (S i) x t)
    | t $ u => (open i x t) $ (open i x u)
    | TTyp T U => TTyp (open i x T) (open i x U)
    | tTyp T => tTyp (open i x T)
    end.

  Notation "{ i :-> x }" := (open i x) : d_scope.
  Notation "e ^^ x" := (open 0 x e) (at level 10) : d_scope.

  Inductive closed (b f : nat) : expr -> Prop :=
    | cl_bot : closed b f TBot
    | cl_top : closed b f TTop
    | cl_varB : forall i, i < b -> closed b f #i
    | cl_varF : forall x, x < f -> closed b f `x
    | cl_all : forall T U, 
        closed b f T -> closed (S b) f U -> closed b f (TAll T U)
    | cl_lam : forall T e,
        closed b f T -> closed (S b) f e -> closed b f (tLam T e)
    | cl_app : forall e u, 
        closed b f e -> closed b f u -> closed b f (e $ u)
    | cl_typT : forall T U,
        closed b f T -> closed b f U -> closed b f (TTyp T U)
    | cl_typ : forall T, closed b f T -> closed b f (tTyp T)
    | cl_selB : forall i, i < b -> closed b f (TSel #i)
    | cl_selF : forall x, x < f -> closed b f (TSel `x).

  Reserved Notation "G |-d" (at level 90, no associativity).
  Reserved Notation "G |-d T" (at level 90, no associativity).
  Reserved Notation "G |-d e : T" 
      (at level 90, e at next level, no associativity).
  Reserved Notation "G |-d T <: U" 
      (at level 90, T at next level, no associativity).

  Inductive wfCx : cx -> Type :=
    | wf_nil : nil |-d

    | wf_snoc : forall G T, 
        G |-d -> 
        G |-d T -> 
        G ~ T |-d

    where "G |-d" := (wfCx G) : d_scope

    with wfTy : cx -> expr -> Type :=
    | wf_bot : forall G, 
        G |-d -> 
        G |-d TBot

    | wf_top : forall G,
        G |-d ->
        G |-d TTop

    | wf_all : forall G T U,
        closed 1 (length G) U ->
        G |-d T ->
        G ~ T |-d U ^^ (length G) ->
        G |-d TAll T U

    | wf_typ : forall G T U,
        G |-d T ->
        G |-d U ->
        G |-d TTyp T U

    | wf_sel : forall G x T U,
        G |-d `x : TTyp T U ->
        G |-d TSel `x

    where "G |-d T" := (wfTy G T) : d_scope

    with hasType : cx -> expr -> expr -> Type :=
    | t_var : forall G x T,
        G |-d ->
        lookup G x T ->
        G |-d `x : T

    | t_lam : forall G T e U,
        closed 1 (length G) e ->
        closed 0 (length G) (TAll T U) ->
        G |-d T ->
        G ~ T |-d e ^^ (length G) : U ^^ (length G) ->
        G |-d tLam T e : TAll T U 

    | t_app : forall G t u T U,
        G |-d t : TAll T U ->
        G |-d u : T ->
        G |-d U ->
        G |-d t $ u : U

    | t_dapp : forall G t x T U,
        G |-d t : TAll T U -> 
        G |-d `x : T ->
        G |-d t $ `x : U ^^ x

    | t_typ : forall G T,
        G |-d T ->
        G |-d tTyp T : TTyp T T

    | t_sub : forall G e T U,
        G |-d e : T ->
        G |-d T <: U ->
        G |-d e : U
          
    where "G |-d e : T" := (hasType G e T) : d_scope

    with subtype : cx -> expr -> expr -> Type :=
    | s_bot : forall G T, 
        G |-d T ->
        G |-d TBot <: T

    | s_top : forall G T,
        G |-d T ->
        G |-d T <: TTop

    | s_all : forall G T1 U1 T2 U2,
        G |-d T2 <: T1  ->
        G ~ T2 |-d U1 ^^ (length G) <: U2 ^^ (length G) ->
        G ~ T2 |-d U1 ^^ (length G) ->
        G |-d TAll T1 U1 <: TAll T2 U2
          
    | s_typ : forall G T1 U1 T2 U2,
        G |-d T2 <: T1 ->
        G |-d U1 <: U2 ->
        G |-d TTyp T1 U1 <: TTyp T2 U2

    | s_sel1 : forall G x T U,
        G |-d `x : TTyp T U ->
        G |-d T <: TSel `x 

    where "G |-d T <: U" := (subtype G T U) : d_scope.

  Fixpoint hasType_wfCx {G e T} (eT : G |-d e : T) : G |-d
    with wfTy_wfCx {G T} (Ts : G |-d T) : G |-d.
  Proof.
    * destruct eT; 
      try assumption;
      try (eapply hasType_wfCx; eassumption);
      try (eapply wfTy_wfCx; eassumption).
  
    * destruct Ts; try assumption;
      try (eapply wfTy_wfCx; eassumption);
      try (eapply hasType_wfCx; eassumption).
  Qed.

  Fixpoint subtype_wfCx {G T U} (st : G |-d T <: U) : G |-d.
  Proof.
    destruct st;
    try (eapply hasType_wfCx; eassumption);
    try (eapply wfTy_wfCx; eassumption);
    try (eapply subtype_wfCx; eassumption).
  Qed.

  Hint Resolve hasType_wfCx wfTy_wfCx subtype_wfCx : core.

End D.

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

Module D2CC.
  Open Scope d_scope.
  Open Scope cc_scope.

  Import CC (prop).
  Coercion CC.TSort : CC.sort >-> CC.expr.
  Coercion CC.tVar : var >-> CC.expr.
  Coercion D.tVar : var >-> D.expr.

  Fixpoint d2ccCx {G} (wfG : D.wfCx G) : CC.cx :=
    match wfG in D.wfCx G with
    | D.wf_nil => nil
    | D.wf_snoc _ _ wfG' Ts => d2ccCx wfG' ~ d2ccTy Ts
    end

    with d2ccTy {G T} (wfT : D.wfTy G T) : CC.expr :=
    match wfT in D.wfTy G T with
    | D.wf_bot _ _ => CC.TBot
    | D.wf_top _ _ => CC.TTop
    | D.wf_all _ _ _ _ Ts Us => CC.TAll (d2ccTy Ts) (d2ccTy Us)
    | D.wf_typ _ _ _ Ts Us => CC.TTyp (d2ccTy Ts) (d2ccTy Us)
    | D.wf_sel _ _ _ _ xTU => CC.tFst (d2ccTm xTU)
    end

    with d2ccTm {G e T} (eT : D.hasType G e T) : CC.expr :=
    match eT in D.hasType G e T with
    | D.t_var _ x _ _ _ => `x
    | D.t_lam _ _ _ _ _ _ Ts eU => CC.tLam (d2ccTy Ts) (d2ccTm eU)
    | D.t_app _ _ _ _ _ tTU uT _ | D.t_dapp _ _ _ _ _ tTU uT =>
        CC.tApp (d2ccTm tTU) (d2ccTm uT)
    | D.t_typ _ _ Ts => CC.tTyp (d2ccTy Ts)
    | D.t_sub _ _ _ _ eT st => CC.tApp (d2ccSt st) (d2ccTm eT)
    end

    with d2ccSt {G T U} (TstU : D.subtype G T U) : CC.expr :=
    match TstU in D.subtype G T U with
    | D.s_bot _ _ Ts => CC.SBot (d2ccTy Ts)
    | D.s_top _ _ Ts => CC.STop (d2ccTy Ts)
    | _ => prop
    end.

  Fixpoint d2cc_wfCx {G} (wfG : D.wfCx G) : CC.wfCx (d2ccCx wfG)
    with d2cc_wfTy {G T} (wfT : D.wfTy G T) 
    : CC.hasType (d2ccCx wfG) (d2ccExpr wfT)
