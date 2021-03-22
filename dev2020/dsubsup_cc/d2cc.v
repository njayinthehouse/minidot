Require Import Compare_dec.
Require Import EqNat.
Require Import Equality.
Require Import List.
Require Import Lia.
Require Import PeanoNat.

Import Notations.

Declare Scope var_scope.
Declare Scope d_scope.
Declare Scope cc_scope.
Delimit Scope d_scope with d.
Delimit Scope cc_scope with cc.

Corollary Nat_lneb_le : forall n m, n <=? m = false -> m < n.
Proof.
  intros. destruct (le_lt_dec n m). apply Nat.leb_le in l. rewrite l in H.
  discriminate. assumption.
Qed.

Corollary Nat_neq_bneq : forall n m, n <> m -> n =? m = false.
Proof.
  intros. destruct (n =? m) eqn:E. apply beq_nat_true in E. lia. auto.
Qed.

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

(* You cannot look up a variable that is not in the context. *)
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
    | tLam : expr -> expr
    | tApp : expr -> expr -> expr
    | TSig : expr -> expr -> expr
    | tPair : expr -> expr -> expr
    | tFst : expr -> expr
    | tSnd : expr -> expr.

  Definition cx := list expr.
  Definition env := list expr.

  Notation "t $" := (tApp t) (at level 4) : cc_scope.
  Notation "t & u" := (tPair t u) (at level 4) : cc_scope.
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
    | tLam t => tLam (e{S i :-> e'} t)
    | t $ u => (e{i :-> e'} t) $ (e{i :-> e'} u)
    | TSig T U => TSig (e{i :-> e'} T) (e{S i :-> e'} U)
    | t & u => (e{i :-> e'} t) & (e{i :-> e'} u)
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
    | cl_lam : forall e, closed (S b) f e -> closed b f (tLam e)
    | cl_app : forall t u,
        closed b f t -> closed b f u -> closed b f (t $ u)
    | cl_sig : forall T U,
        closed b f T -> closed (S b) f U -> closed b f (TSig T U)
    | cl_pair : forall t u,
        closed b f t -> closed b f u -> closed b f (t & u)
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
    | tLam t => tLam (decrB' (S i) t)
    | t $ t' => (decrB' i t) $ (decrB' i t')
    | TSig T U => TSig (decrB' i T) (decrB' (S i) U)
    | t & t' => (decrB' i t) & (decrB' i t')
    | tFst t => tFst (decrB' i t)
    | tSnd t => tSnd (decrB' i t)
    end.
  Definition decrB := decrB' 0.
  Notation "e ^$ u" := (decrB (e *^ u)) (at level 50).

  Hint Unfold decrB : core.

  (* Full beta-eta-pi reduction *)
  (* Do we need eta equality? *)
  Inductive reduce : expr -> expr -> Prop :=
    | r_beta : forall e u, (tLam e) $ u ~~> e ^$ u
    | r_pi1 : forall e u, tFst (e & u) ~~> e
    | r_pi2 : forall e u, tSnd (e & u) ~~> u
    | r_all1 : forall T U T', T ~~> T' -> TAll T U ~~> TAll T' U
    | r_all2 : forall T U U', U ~~> U' -> TAll T U ~~> TAll T U'
    | r_lam : forall e e', e ~~> e' -> tLam e ~~> tLam e'
    | r_app1 : forall e u e', e ~~> e' -> e $ u ~~> e' $ u
    | r_app2 : forall e u u', u ~~> u' -> e $ u ~~> e $ u'
    | r_sig1 : forall T U T', T ~~> T' -> TSig T U ~~> TSig T' U
    | r_sig2 : forall T U U', U ~~> U' -> TSig T U ~~> TSig T U'
    (* The lecture notes linked above don't mention adding these 
       substructural rules for pairs, but I think they're required, else
       we can't reduce inside tuples. *)
    | r_pair1 : forall t u t', t ~~> t' -> t & u ~~> t' & u
    | r_pair2 : forall t u u', u ~~> u' -> t & u ~~> t & u'
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
        G |-cc tLam e : TAll T U

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
        G |-cc t & u : TSig T U

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
    | TAll T U | T $ U | TSig T U | T & U => S (esize_flat T + esize_flat U)
    | tLam t => S (esize_flat t)
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

  (* Substitution *)
  Reserved Notation "e[ x :-> u ]" (at level 50).
  Fixpoint subst (x : fVar) (u e : expr) : expr :=
    match e with
    | tVar `y => if x =? y then u else `y
    | TSort _ | tVar #_ => e
    | TAll T U => TAll (e[x :-> u] T) (e[x :-> u] U)
    | tLam t => tLam (e[x:-> u] t)
    | t $ t' => (e[x :-> u] t) $ (e[x :-> u] t')
    | TSig T U => TSig (e[x :-> u] T) (e[x :-> u] U)
    | t & t' => (e[x :-> u] t) & (e[x :-> u] t')
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
    | tLam t => tLam (k +> t)
    | t $ u => (k +> t) $ (k +> u)
    | TSig T U => TSig (k +> T) (k +> U)
    | t & u => (k +> t) & (k +> u)
    | tFst t => tFst (k +> t)
    | tSnd t => tSnd (k +> t)
    end
    where "k +>" := (splice k) : cc_scope.

  (* Unsplicing 
  Reserved Notation "k -<" (at level 45, right associativity).
  Fixpoint unsplice (k : nat) (e : expr) : expr :=
    match e with
    | tVar `x => varF (if k <=? x then x - 1 else x)
    | TSort _ | tVar #_ => e
    | TAll T U => TAll (k -< T) (k -< U)
    | tLam t => tLam (k -< t)
    | t $ u => (k -< t) $ (k -< u)
    | TSig T U => TSig (k -< T) (k -< U)
    | t & u :[T ** U] => (k -< t) & (k -< u) :[k -< T ** k -< U]
    | tFst t => tFst (k -< t)
    | tSnd t => tSnd (k -< t)
    end
     where "k -<" := (unsplice k) : cc_scope. *)

  (* Closing *)
  Fixpoint close (f : fVar) (b : bVar) (e : expr) : expr :=
    match e with
    | tVar `x => if f =? x then #b else `x
    | TAll T U => TAll (close f b T) (close f (S b) U)
    | tLam t => tLam (close f (S b) t)
    | t $ u => (close f b t) $ (close f b u)
    | TSig T U => TSig (close f b T) (close f (S b) U)
    | t & u => (close f b t) & (close f b u)
    | tFst t => tFst (close f b t)
    | tSnd t => tSnd (close f b t)
    | _ => e
    end.

  (* Opening with variables and closing are inverses in some cases. *)
  Lemma open_close : forall b f e,
    closed b (S f) e -> open (S b) `f (close f (S b) e) = e.
  Proof.
    induction 1.
    all: simpl; try solve [ reflexivity
                          | rewrite IHclosed1; rewrite IHclosed2; auto
                          | rewrite IHclosed; auto ].
    destruct (f =? x) eqn:E; auto; simpl. rewrite <- beq_nat_refl.
    apply beq_nat_true in E. subst. auto.
    destruct i; auto. destruct (b =? i) eqn:E; auto. apply beq_nat_true in E.
    lia.
  Qed.

  Lemma close_open : forall b f e,
    closed (S b) f e -> close (S f) b (open b (varF (S f)) e) = e.
  Proof.
    intros b f e cle. remember (S b) as Sb. generalize dependent b.
    induction cle; intros; subst; auto.
    simpl. destruct x. auto. destruct (f =? x) eqn:E. apply beq_nat_true in E.
    lia. auto.
    simpl. destruct (b0 =? i) eqn:E. simpl. rewrite <- beq_nat_refl.
    apply beq_nat_true in E. subst. auto. auto.
    1,3,4,5: simpl; try rewrite IHcle1; try rewrite IHcle2; auto.
    all: simpl; try rewrite IHcle; auto.
  Qed.

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
    induction 1; try constructor; 
    try apply IHclosed; try apply IHclosed2; try apply IHclosed4; 
    try lia; eauto.
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

  Lemma closed_close : forall e b f,
    closed b (S f) e ->
    closed (S b) f (close f b e).
  Proof.
    induction e; simpl; inversion 1; subst; try constructor; eauto.
    destruct (f =? x) eqn:E. constructor. lia. constructor. 
    apply beq_nat_false in E. lia.
  Qed.

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
    intros j. destruct (j <=? i) eqn:E; constructor; lia.
    apply IHe. assumption. lia.
  Qed.

  Lemma closed_decrB : forall e b f,
    closed (S b) f e -> forall i, i < b -> closed b f (decrB' i e).
  Proof.
    induction e; inversion 1; subst; simpl; try constructor; auto;
    try apply IHe2; try apply IHe4; try lia; auto.
    simpl. intros j. destruct (j <=? i) eqn:E. 
    constructor. lia. constructor. pose (le_lt_dec j i). destruct s.
    rewrite <- Nat.leb_le in l. rewrite E in l. discriminate. lia.
    apply IHe. assumption. lia.
  Qed.

  Lemma closed_splice : forall e b f, 
    closed b f e -> forall k, closed b (S f) (k +> e).
  Proof.
    induction 1; simpl; intros; try destruct (k <=? x); constructor; try lia;
    eauto.
  Qed.
  
  Hint Rewrite splice_decrB : core.
  Hint Resolve closed_open_front closed_open_middle : core.

  Lemma splice_close : forall e f b k,
    k +> (close f b e) = close (if k <=? f then S f else f) b (k +> e).
  Proof.
    induction e; intros.
    reflexivity.
    2-8: simpl.
    2,4-6: rewrite IHe1; rewrite IHe2; reflexivity.
    2-4: rewrite IHe; reflexivity.
    destruct v. reflexivity. simpl.
    destruct (f =? f0) eqn:E.
    apply beq_nat_true in E. subst. rewrite <- beq_nat_refl. reflexivity.
    destruct (k <=? f) eqn:k_lt_f, (k <=? f0) eqn:k_lt_f0; simpl.
    rewrite k_lt_f0. rewrite E. reflexivity.
    rewrite k_lt_f0. destruct f0. reflexivity. 
    assert (f =? f0 = false). 
    { apply Nat.leb_le in k_lt_f. apply Nat_lneb_le in k_lt_f0. 
      apply Nat_neq_bneq. lia.  }
    rewrite H. reflexivity.
    rewrite k_lt_f0. assert (f =? S f0 = false).
    { apply Nat_neq_bneq. apply Nat_lneb_le in k_lt_f. 
      apply Nat.leb_le in k_lt_f0. lia. }
    rewrite H. reflexivity.
    rewrite k_lt_f0. rewrite E. reflexivity.
  Qed.
    
    

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

  (***************************************************************************
   * Properties of expressions and types *)

  (* If an expression is well-typed under G, then G is a context. *)
  Theorem hasType_wfCx : forall G e T, G |-cc e : T -> G |-cc.
  Proof.
    induction 1; try assumption.
  Qed.

  Hint Resolve hasType_wfCx : core.

  Fixpoint hasType_closed {G e T} (eT : G |-cc e : T)
    : closed 0 (length G) e * closed 0 (length G) T

    with wfCx_closed {G} (wfG : G |-cc) 
    : forall T, In T G -> closed 0 (length G) T.
  Proof.
    * destruct eT.
      - constructor; constructor.
      - constructor. constructor. eauto. eapply wfCx_closed; eauto.
      - constructor. apply hasType_closed in eT1. constructor. intuition.
        assumption. constructor.
      - inversion H. subst. constructor; auto. constructor; auto.
      - apply hasType_closed in eT1. apply hasType_closed in eT2.
        constructor. constructor; intuition. apply closed_open.
        destruct eT1. inversion c0. subst. assumption. intuition.
      - constructor. constructor. apply hasType_closed in eT1.
        intuition. assumption. constructor.
      - apply hasType_closed in eT1. apply hasType_closed in eT2.
        destruct eT1. inversion c. subst. apply hasType_closed in eT3.
        constructor. 1-2: constructor; intuition.
      - apply hasType_closed in eT. destruct eT. inversion c0. subst.
        constructor. constructor. assumption. assumption.
      - apply hasType_closed in eT. destruct eT. inversion c0. subst.
        constructor. constructor. assumption. apply closed_open. assumption.
        constructor. assumption.
      - apply hasType_closed in eT1. apply hasType_closed in eT2. intuition.

    * destruct wfG; inversion 1; subst.
      - apply hasType_closed in H. simpl. intuition. 
        eapply closed_monotonic. eassumption. lia. lia.
      - eapply closed_monotonic with (f := length G). apply wfCx_closed;
        assumption. lia. simpl. lia.
  Qed.
  
  (* The prefix of any context is a context. *)
  Theorem wfCx_drop_back : forall G' G,
    G +~ G' |-cc -> G |-cc.
  Proof.
    induction G'. auto. inversion 1. subst. auto.
  Qed.

  Hint Resolve wfCx_closed wfCx_drop_back : core.

  Lemma lookup_wfCx_splice : forall G' G x T,
    lookup (G +~ G') x T ->
    forall U, G ~ U +~ map (length G +>) G' |-cc ->
    lookup (G ~ U +~ map (length G +>) G') 
        (if length G <=? x then S x else x) (length G +> T).
  Proof.
    induction G'; simpl; intros.
    - replace (length G <=? x) with false. 
      assert (length G +> T = T). 
      eapply splice_closed. apply wfCx_closed; eauto. inversion H0. auto.
      rewrite H1. constructor. assumption.
      assert (x < length G). eapply lookup_lt. eassumption. 
      destruct (length G <=? x) eqn:E. apply Nat.leb_le in E. lia. auto.
    - inversion H; subst.
      + replace (length G <=? length (G +~ G')) with true.
        replace (S (length (G +~ G'))) 
          with (length (G ~ U +~ map (length G +>) G')).
        constructor. rewrite length_elim_middle. repeat rewrite app_length.
        rewrite map_length. reflexivity. rewrite app_length. symmetry.
        rewrite Nat.leb_le. lia.
      + inversion H0. constructor. apply IHG'; eauto.
  Qed.

  Hint Resolve lookup_wfCx_splice : core.

  (* Splicing preserves well-typedness. *)
  Lemma t_thin : forall G G' e T,
    G +~ G' |-cc e : T ->
    forall U, G ~ U +~ map (length G +>) G' |-cc ->
    G ~ U +~ map (length G +>) G' |-cc length G +> e : length G +> T.
  Proof.
    intros G G'. remember (G +~ G') as GG'. intros e T H. 
    generalize dependent HeqGG'. generalize dependent G.
    generalize dependent G'. induction H; intros; subst.
    - constructor. auto.
    - constructor; auto. 
    - simpl. econstructor.
      + rewrite length_elim_middle. rewrite app_length. rewrite map_length.
        rewrite <- app_length. apply closed_splice. assumption.
      + erewrite splice_sort. eauto.
      + replace ((G0 ~ U0 +~ map (length G0 +>) G') ~ length G0 +> T)
          with (G0 ~ U0 +~ map (length G0 +>) (G' ~ T)) by reflexivity. 
        assert (length G0 +> ` (length (G0 +~ G')) 
                = ` (length (G0 ~ U0 +~ map (length G0 +>) G'))).
        repeat rewrite app_length. rewrite map_length. simpl.
        assert (length G0 <=? length G' + length G0 = true).
        apply Nat.leb_le. lia. rewrite H3. rewrite plus_n_Sm. reflexivity.
        rewrite <- H3. rewrite <- splice_open. erewrite splice_sort.
        apply IHhasType2; auto. simpl. econstructor; eauto.
    - simpl. econstructor.
      + rewrite length_elim_middle. rewrite app_length in *. 
        rewrite map_length. rewrite splice_all. apply closed_splice. 
        assumption.
      + rewrite length_elim_middle. rewrite app_length in *.
        rewrite map_length. apply closed_splice. assumption.
      + erewrite splice_sort. auto.
      + replace ((G0 ~ U0 +~ map (length G0 +>) G') ~ length G0 +> T)
          with (G0 ~ U0 +~ map (length G0 +>) (G' ~ T)) by reflexivity. 
        assert (length G0 +> ` (length (G0 +~ G')) 
                = ` (length (G0 ~ U0 +~ map (length G0 +>) G'))).
        repeat rewrite app_length. rewrite map_length. simpl.
        assert (length G0 <=? length G' + length G0 = true).
        apply Nat.leb_le. lia. rewrite H4. rewrite plus_n_Sm. reflexivity.
        rewrite <- H4. repeat rewrite <- splice_open. 
        apply IHhasType2; eauto. econstructor; eauto.
    - simpl. rewrite splice_open. 
      apply t_app with (T := length G0 +> T); eauto.
    - simpl. econstructor.
      + rewrite length_elim_middle. rewrite app_length in *.
        rewrite map_length. apply closed_splice. assumption.
      + erewrite splice_sort. eauto.
      + replace ((G0 ~ U0 +~ map (length G0 +>) G') ~ length G0 +> T)
          with (G0 ~ U0 +~ map (length G0 +>) (G' ~ T)) by reflexivity. 
        assert (length G0 +> ` (length (G0 +~ G')) 
                = ` (length (G0 ~ U0 +~ map (length G0 +>) G'))).
        repeat rewrite app_length. rewrite map_length. simpl.
        assert (length G0 <=? length G' + length G0 = true).
        apply Nat.leb_le. lia. rewrite H3. rewrite plus_n_Sm. reflexivity.
        rewrite <- H3. rewrite <- splice_open. erewrite splice_sort.
        apply IHhasType2; auto. simpl. econstructor; eauto.
    - simpl. econstructor; eauto. rewrite <- splice_open. auto.
    - simpl. apply t_fst with (U := length G0 +> U). rewrite splice_sig.
      auto.
    - simpl. rewrite splice_open. apply t_snd with (T := length G0 +> T).
      rewrite splice_sig. auto.
    - eapply t_conv with (T := length G0 +> T). auto. erewrite splice_sort.
      auto. apply e_splice. auto.
  Qed.

  Theorem t_weak : forall G e T, 
    G |-cc e : T ->
    forall U, G ~ U |-cc ->
    G ~ U |-cc e : T.
  Proof.
    intros. 
    assert (length G +> e = e /\ length G +> T = T).
    apply hasType_closed in H. split; eapply splice_closed; intuition; eauto.
    intuition.
    assert (G ~ U = G ~ U +~ map (length G +>) nil) by reflexivity.
    rewrite H1. rewrite <- H2. rewrite <- H3. apply t_thin; auto.
  Qed.

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

  Definition tId := tLam #0.

  (* Presyntax *)
  Definition TBot := TAll prop #0.
  Definition TTop := TSig prop #0.
  
  Definition TTyp (T U : expr) := 
    TSig prop (TSig (TAll T #1) (TAll #1 U)).

  Definition TSel (x : expr) := tFst x.
  Definition tTyp (T : expr) := (T & (tId & tId)).

  (* Coercions for subtyping *)
  Definition SBot (T : expr) := tLam (#0 $ T).
  Definition STop (T : expr) := tLam (T & #0).

  Definition SAll (T'2T U2U' : expr) :=
    tLam (tLam (U2U' $ (#1 $ (T'2T $ #0)))).

  Definition SSel1 (x : expr) := tLam ((tFst (tSnd x)) $ #0).
  Definition SSel2 (x : expr) := tLam ((tSnd (tSnd x)) $ #0).

  Definition STyp (T'2T U2U' : expr) :=
    tLam ((tFst #0) & 
             ((tLam ((tFst (tSnd #1)) $ (T'2T $ #0))) &
             (tLam (U2U' $ ((tSnd (tSnd #1)) $ #0))))).

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
    1-49: try constructor; try lia; eauto.
    1-8: apply hasType_closed in H; apply hasType_closed in H0; intuition;
         eauto.
  Qed.
  
  Corollary wf_sel : forall G T U e,
    G |-cc e : TTyp T U ->
    G |-cc TSel e : prop.
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
    intros. assert (U = U *^ u). symmetry. eapply open_closed. 
    apply hasType_closed in H1. intuition. eauto. lia. rewrite H2.
    econstructor; eauto.
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
  Admitted.

End CC.

Inductive empty : Type :=.
Inductive Squash (X : Type) : Prop := squash : X -> Squash X.

Fixpoint In' {X} (x : X) (xs : list X) : Type :=
  match xs with
  | nil => empty
  | cons x' xs' => (x = x') + (In' x xs')
  end.

Corollary In'_In : forall X (x : X) xs, In' x xs -> In x xs.
Proof. 
  induction xs. inversion 1. simpl. destruct 1. left. symmetry. auto. 
  right. auto.
Qed.

Inductive lookup' {ty} : list ty -> fVar -> ty -> Type :=
  | last' : forall G T, lookup' (G ~ T) (length G) T
  | prev' : forall G T U x, lookup' G x T -> lookup' (G ~ U) x T.

Corollary lookup'_lookup : forall ty G x (T : ty), 
  lookup' G x T -> lookup G x T.
Proof. induction 1. constructor. constructor. assumption. Qed.

Corollary lookup_lookup' : forall ty G x (T : ty),
  lookup G x T -> Squash (lookup' G x T).
Proof.
  induction 1. do 2 constructor. inversion IHlookup. do 2 constructor.
  assumption.
Qed.

Corollary lookup_in' : forall ty G x (T : ty), lookup' G x T -> In' T G.
Proof.
  induction 1.
  - left. auto.
  - right. auto.
Qed.

Corollary lookup_lt' : forall ty G x (T : ty), lookup' G x T -> x < length G.
Proof.
  induction 1.
  - simpl. lia.
  - simpl. lia.
Qed.

Module D.

  Inductive expr : Type :=
    | TBot : expr
    | TTop : expr
    | tVar : var -> expr
    | TAll : expr -> expr -> expr
    | tLam : expr -> expr
    | tApp : expr -> expr -> expr
    | TTyp : expr -> expr -> expr
    | tTyp : expr -> expr
    | TSel : var -> expr.

  Definition cx := list expr.

  Coercion tVar : var >-> expr.
  Infix "$" := tApp (at level 5, left associativity) : d_scope.
  Coercion CC.TSort : CC.sort >-> CC.expr.
  Coercion CC.tVar : var >-> CC.expr.

  Open Scope cc_scope.
  Open Scope d_scope.

  Fixpoint open (i : bVar) (x : fVar) (e : expr) : expr :=
    match e with
    | tVar #j => tVar (if i =? j then `x else #j)
    | TSel #j => TSel (if i =? j then `x else #j)
    | TBot | TTop | tVar `_ | TSel `_ => e
    | TAll T U => TAll (open i x T) (open (S i) x U)
    | tLam t => tLam (open (S i) x t)
    | t $ u => (open i x t) $ (open i x u)
    | TTyp T U => TTyp (open i x T) (open i x U)
    | tTyp T => tTyp (open i x T)
    end.

  Notation "{ i :-> x }" := (open i x) : d_scope.
  Notation "e ^^ x" := (open 0 x e) (at level 10) : d_scope.

  Inductive closed (b f : nat) : expr -> Type :=
    | cl_bot : closed b f TBot
    | cl_top : closed b f TTop
    | cl_varB : forall i, i < b -> closed b f #i
    | cl_varF : forall x, x < f -> closed b f `x
    | cl_all : forall T U, 
        closed b f T -> closed (S b) f U -> closed b f (TAll T U)
    | cl_lam : forall e, closed (S b) f e -> closed b f (tLam e)
    | cl_app : forall e u, 
        closed b f e -> closed b f u -> closed b f (e $ u)
    | cl_typT : forall T U,
        closed b f T -> closed b f U -> closed b f (TTyp T U)
    | cl_typ : forall T, closed b f T -> closed b f (tTyp T)
    | cl_selB : forall i, i < b -> closed b f (TSel #i)
    | cl_selF : forall x, x < f -> closed b f (TSel `x).

  Reserved Notation "G |-d" (at level 90, no associativity).
  Reserved Notation "G |-d T ~> T'" 
      (at level 90, T at next level, no associativity).
  Reserved Notation "G |-d e : T ~> e'" 
      (at level 90, e at next level, no associativity).
  Reserved Notation "G |-d T <: U ~> c" 
      (at level 90, T at next level, no associativity).

  Inductive wfCx : cx -> Type :=
    | wf_nil : nil |-d

    | wf_snoc : forall {G T T'}, 
        G |-d -> 
        G |-d T ~> T' -> 
        G ~ T |-d

    where "G |-d" := (wfCx G) : d_scope

    with wfTy : cx -> expr -> CC.expr -> Type :=
    | wf_bot : forall {G}, 
        G |-d -> 
        G |-d TBot ~> CC.TBot

    | wf_top : forall {G},
        G |-d ->
        G |-d TTop ~> CC.TTop

    | wf_all : forall {G T U T' U'},
        closed 1 (length G) U ->
        G |-d T ~> T' ->
        G ~ T |-d U ^^ (length G) ~> U' ->
        G |-d TAll T U ~> CC.TAll T' (CC.close (length G) 0 U')

    | wf_typ : forall {G T U T' U'},
        G |-d T ~> T'->
        G |-d U ~> U' ->
        G |-d TTyp T U ~> CC.TTyp T' U'

    | wf_sel : forall G x T U e',
        G |-d `x : TTyp T U ~> e' ->
        G |-d TSel `x ~> CC.TSel e'

    where "G |-d T ~> T'" := (wfTy G T T') : d_scope

    with hasType : cx -> expr -> expr -> CC.expr -> Type :=
    | t_var : forall G x T,
        G |-d ->
        lookup' G x T ->
        G |-d `x : T ~> `x

    | t_lam : forall G T e U T' e',
        closed 1 (length G) e ->
        closed 0 (length G) (TAll T U) ->
        G |-d T ~> T' ->
        G ~ T |-d e ^^ (length G) : U ^^ (length G) ~> e' ->
        G |-d tLam e : TAll T U ~> CC.tLam (CC.close (length G) 0 e')

    | t_app : forall G t u T U t' u' U',
        G |-d t : TAll T U ~> t' ->
        G |-d u : T ~> u' ->
        G |-d U ~> U' ->
        G |-d t $ u : U ~> CC.tApp t' u'

    | t_dapp : forall G t x T U t' e',
        G |-d t : TAll T U ~> t' -> 
        G |-d `x : T ~> e' ->
        G |-d t $ `x : U ^^ x ~> CC.tApp t' e'

    | t_typ : forall G T T',
        G |-d T ~> T' ->
        G |-d tTyp T : TTyp T T ~> CC.TTyp T' T'

    | t_sub : forall G e T U e' c,
        G |-d e : T ~> e' ->
        G |-d T <: U ~> c ->
        G |-d e : U ~> CC.tApp c e'
          
    where "G |-d e : T ~> T'" := (hasType G e T T') : d_scope

    with subtype : cx -> expr -> expr -> CC.expr -> Type :=
    | s_bot : forall G T T', 
        G |-d T ~> T' ->
        G |-d TBot <: T ~> CC.SBot T'

    | s_top : forall G T T',
        G |-d T ~> T' ->
        G |-d T <: TTop ~> CC.STop T'

    | s_all : forall G T1 U1 T2 U2 U1' cT cU,
        closed 1 (length G) U1 ->
        closed 1 (length G) U2 ->
        G |-d T2 <: T1 ~> cT ->
        G ~ T1 |-d U1 ^^ (length G) ~> U1' ->
        G ~ T2 |-d U1 ^^ (length G) <: U2 ^^ (length G) ~> cU ->
        G |-d TAll T1 U1 <: TAll T2 U2 ~> CC.SAll cT (CC.close (length G) 0 cU)
          
    | s_typ : forall G T1 U1 T2 U2 cT cU,
        G |-d T2 <: T1 ~> cT ->
        G |-d U1 <: U2 ~> cU ->
        G |-d TTyp T1 U1 <: TTyp T2 U2 ~> CC.STyp cT cU

    | s_sel1 : forall G x T U e',
        G |-d `x : TTyp T U ~> e' ->
        G |-d T <: TSel `x ~> CC.SSel1 e'

    | s_sel2 : forall G x T U e',
        G |-d `x : TTyp T U ~> e' ->
        G |-d TSel `x <: U ~> CC.SSel2 e'

    | s_refl : forall G T T', G |-d T ~> T' -> G |-d T <: T ~> CC.tId

    | s_trans : forall G T U V T2U U2V,
        G |-d T <: U ~> T2U ->
        G |-d U <: V ~> U2V ->
        G |-d T <: V ~> CC.tLam (CC.tApp U2V (CC.tApp T2U #0))

    where "G |-d T <: U ~> c" := (subtype G T U c) : d_scope.

  Reserved Notation "k +>" (at level 45).
  Fixpoint splice (k : nat) (e : expr) : expr :=
    match e with
    | tVar `x => varF (if k <=? x then S x else x)
    | TSel `x => TSel (varF (if k <=? x then S x else x))
    | TAll T U => TAll (k +> T) (k +> U)
    | tLam t => tLam (k +> t)
    | t $ u => (k +> t) $ (k +> u)
    | TTyp T U => TTyp (k +> T) (k +> U)
    | tTyp T => tTyp (k +> T)
    | _ => e
    end
    where "k +>" := (splice k) : d_scope.

  Corollary closed_monotonic : forall e b f, 
    closed b f e ->
    forall b', b <= b' ->
    forall f', f <= f' ->
    closed b' f' e.
  Proof.
    induction 1; constructor; eauto; try lia; try apply IHclosed; 
    try apply IHclosed2; lia.
  Qed.

  Corollary splice_typ : forall T U k, 
    TTyp (k +> T) (k +> U) = k +> (TTyp T U).
  Proof. reflexivity. Qed.

  Corollary splice_fVar : forall x k, 
    tVar (varF (if k <=? x then S x else x)) = k +> `x.
  Proof. reflexivity. Qed.

  Lemma closed_splice : forall e b f,
    closed b f e -> forall k, closed b (S f) (k +> e).
  Proof.
    induction 1; simpl; constructor; auto; destruct (k <=? x); lia.
  Qed.

  Lemma splice_closed : forall f e b, closed b f e -> f +> e = e.
  Proof.
    induction 1; simpl; auto.
    1,7: assert (f <=? x = false); destruct (f <=? x) eqn:E; auto; 
         try apply Nat.leb_le in E; lia.
    1,3,4: rewrite IHclosed1; rewrite IHclosed2; reflexivity.
    1,2: rewrite IHclosed; reflexivity.
  Qed.

  Lemma splice_open : forall e x k i,
    k +> ({i :-> x} e) = {i :-> if k <=? x then S x else x} (k +> e).
  Proof.
    induction e; intros; simpl; auto.
    1,7: destruct v; simpl; try destruct (i =? b) eqn:E; reflexivity.
    1,3,4: rewrite IHe1; rewrite IHe2; reflexivity.
    1-2: rewrite IHe; reflexivity.
  Qed.

  Lemma closed_open : forall e b f,
    closed (S b) f e -> 
    forall x, x < f ->
    closed b f ({b :-> x} e).
  Proof.
    induction e; simpl; inversion 1; subst; try constructor; eauto.
    all: destruct (b =? i) eqn:E; constructor; try apply beq_nat_false in E;
    lia.
  Qed.

  Fixpoint wfTy_closed {G T T'} (wfTT' : G |-d T ~> T') 
      : closed 0 (length G) T * CC.closed 0 (length G) T'

    with hasType_closed {G e T e'} (eTe' : G |-d e : T ~> e')
      : closed 0 (length G) e * closed 0 (length G) T * 
        CC.closed 0 (length G) e'

    with wfCx_closed {G} (wfG : G |-d) 
      : forall T, In' T G -> closed 0 (length G) T

    with subtype_closed {G T U c} (stTUc : G |-d T <: U ~> c)
      : closed 0 (length G) T * closed 0 (length G) U * 
        CC.closed 0 (length G) c.
  Proof.
    * destruct wfTT'.
      - repeat constructor.
      - repeat constructor.
      - apply wfTy_closed in wfTT'1. apply wfTy_closed in wfTT'2.
        repeat constructor; intuition. apply CC.closed_close. assumption.
      - apply wfTy_closed in wfTT'1. apply wfTy_closed in wfTT'2.
        repeat constructor; intuition. eapply CC.closed_monotonic.
        eassumption. lia. lia. eapply CC.closed_monotonic. eassumption.
        lia. lia.
      - apply hasType_closed in h; intuition. constructor. inversion a0. 
        assumption. constructor. assumption.

    * destruct eTe'.
      - split. split. constructor. eapply lookup_lt'. eassumption. 
        apply wfCx_closed. assumption. eapply lookup_in'. eassumption.
        constructor. eapply lookup_lt'. eassumption.
      - split. split. constructor. assumption. assumption.
        apply hasType_closed in eTe'. constructor. apply CC.closed_close.
        intuition.
      - apply hasType_closed in eTe'1. apply hasType_closed in eTe'2.
        apply wfTy_closed in w. split. split. constructor; intuition.
        intuition. constructor; intuition.
      - apply hasType_closed in eTe'1. apply hasType_closed in eTe'2.
        split. split. constructor; intuition. intuition.
        inversion b1. subst. apply closed_open. assumption. inversion a.
        subst. lia. constructor; intuition.
      - apply wfTy_closed in w. repeat constructor; intuition.
        eapply CC.closed_monotonic. eassumption. lia. lia. 
        eapply CC.closed_monotonic. eassumption. lia. lia.
      - apply hasType_closed in eTe'. apply subtype_closed in s.
        split. split; intuition. constructor; intuition.

    * destruct wfG.
      - destruct 1.
      - intros. apply closed_monotonic with (b := 0) (f := length G).
        destruct X. subst. apply wfTy_closed in w. intuition.
        apply wfCx_closed; assumption. lia. simpl. lia.

    * destruct stTUc.
      - apply wfTy_closed in w. intuition. constructor. constructor.
        constructor. constructor. lia. eapply CC.closed_monotonic.
        eassumption. lia. lia.
      - apply wfTy_closed in w. intuition. constructor. constructor.
        constructor. eapply CC.closed_monotonic. eassumption. lia.
        lia. constructor. lia.
      - apply subtype_closed in stTUc1. apply subtype_closed in stTUc2.
        intuition. constructor; assumption. constructor; assumption.
        constructor. constructor. constructor.
        apply CC.closed_monotonic with (b := 1) (f := length G).
        apply CC.closed_close. assumption. lia. lia. constructor.
        constructor. lia. constructor. eapply CC.closed_monotonic.
        eassumption. lia. lia. constructor. lia.
      - apply subtype_closed in stTUc1. apply subtype_closed in stTUc2.
        intuition; constructor; try eassumption. constructor.
        constructor. constructor. lia. constructor. constructor. constructor.
        constructor. constructor. constructor. lia. constructor. 
        eapply CC.closed_monotonic. eassumption. lia. lia. constructor.
        lia. constructor. constructor. eapply CC.closed_monotonic.
        eassumption. lia. lia. constructor. constructor. constructor.
        constructor. lia. constructor. lia.
      - apply hasType_closed in h. intuition. inversion b0. subst.
        assumption. constructor. inversion a0. subst. lia. 
        repeat constructor. eapply CC.closed_monotonic. eassumption. lia.
        lia.
      - apply hasType_closed in h. intuition. constructor. inversion a0.
        subst. lia. inversion b0. subst. assumption. constructor.
        constructor. constructor. constructor. eapply CC.closed_monotonic.
        eassumption. lia. lia. constructor. lia.
      - apply wfTy_closed in w. intuition. constructor. constructor. lia.
      - apply subtype_closed in stTUc1. apply subtype_closed in stTUc2.
        intuition. repeat constructor. eapply CC.closed_monotonic.
        eassumption. lia. lia. eapply CC.closed_monotonic. eassumption.
        lia. lia.
  Qed.

  (* If a preterm (resp. pretype) is a term (resp. type) under precontext G, 
     then G is a context. *)
  Fixpoint wfTy_wfCx {G T T'} (wfTT' : G |-d T ~> T') : G |-d
    with hasType_wfCx {G e T e'} (eTe' : G |-d e : T ~> e') : G |-d.
  Proof.
    * destruct wfTT'; try solve [ assumption 
                                | eapply wfTy_wfCx; eassumption
                                | eapply hasType_wfCx; eassumption ].
    * destruct eTe'; try solve [ assumption 
                               | eapply wfTy_wfCx; eassumption
                               | eapply hasType_wfCx; eassumption ].
  Qed.

  Lemma lookup_wfCx_splice' : forall G' G x T,
    lookup' (G +~ G') x T ->
    forall U, G ~ U +~ map (length G +>) G' |-d ->
    lookup' (G ~ U +~ map (length G +>) G')
        (if length G <=? x then S x else x) (length G +> T).
  Proof.
    induction G'; simpl; intros.
    - replace (length G <=? x) with false.
      assert (length G +> T = T). eapply splice_closed.
  Admitted.

  Fixpoint wf_thin
    {G G' T T'} (wfTT' : G +~ G' |-d T ~> T')
    {U} (wfGUG' : G ~ U +~ map (length G +>) G' |-d)
    : G ~ U +~ map (length G +>) G' |-d length G +> T ~> 
        CC.splice (length G) T'

    with t_thin 
    {G G' e T e'} (eTe' : G +~ G' |-d e : T ~> e')
    {U} (wfGUG' : G ~ U +~ map (length G +>) G' |-d) 
    : G ~ U +~ map (length G +>) G' |-d length G +> e : length G +> T ~>
        CC.splice (length G) e'.
  Proof.
    all: remember (G +~ G') as GG'.

    * destruct wfTT'; subst; simpl.
      - constructor. assumption.
      - constructor. assumption.
      - rewrite CC.splice_close. 
        replace (length G <=? length (G +~ G')) with true.
        replace (S (length (G +~ G'))) 
          with (length (G ~ U +~ map (length G +>) G')).
        constructor. rewrite length_elim_middle. apply closed_splice.
        rewrite app_length in *. rewrite map_length. assumption.
        apply wf_thin; assumption.
        replace ((G ~ U +~ map (length G +>) G') ~ length G +> T)
          with (G ~ U +~ map (length G +>) (G' ~ T)).
        replace (length (G ~ U +~ map (length G +>) G'))
          with (if length G <=? length (G +~ G') 
                then (S (length (G +~ G')))
                else length (G +~ G')).
        rewrite <- splice_open.
        apply wf_thin. assumption. simpl. econstructor.
        assumption. apply wf_thin; eassumption.
        replace (length G <=? length (G +~ G')) with true.
        symmetry. rewrite length_elim_middle. repeat rewrite app_length.
        rewrite map_length. reflexivity. symmetry. apply Nat.leb_le.
        rewrite app_length. lia. reflexivity. rewrite length_elim_middle.
        repeat rewrite app_length. rewrite map_length. reflexivity.
        symmetry. rewrite app_length. apply Nat.leb_le. lia.
      - constructor; apply wf_thin; assumption.
      - apply wf_sel with (T := length G +> T) (U := length G +> U0).
        rewrite splice_typ. rewrite splice_fVar. apply t_thin; assumption.

    * destruct eTe'; subst.
      - constructor. assumption. apply lookup_wfCx_splice'; assumption.
      - admit.
      - admit.
      - admit.
      - admit.
      - admit.
  Admitted.

  Definition t_weak 
    {G e T e'} (eTe' : G |-d e : T ~> e') 
    {U} (wfGU : G ~ U |-d)
    : G ~ U |-d e : T ~> e'.
  Proof.
    assert ((length G +> e = e) * (length G +> T = T) * 
            (CC.splice (length G) e' = e')).
    apply hasType_closed in eTe'. split. 
    split; apply splice_closed with (b := 0); intuition.
    apply CC.splice_closed with (b := 0). intuition.
    assert (G ~ U = G ~ U +~ (map (length G +>) nil)) by reflexivity.
    intuition. rewrite <- a0. rewrite <- b0. rewrite <- b. rewrite H0.
    apply t_thin; eassumption.
  Qed.

  Definition wf_weak
    {G T T'} (wfTT' : G |-d T ~> T')
    {U} (wfGU : G ~ U |-d)
    : G ~ U |-d T ~> T'.
  Proof.
    apply wfTy_closed in wfTT' as H.
    assert (length G +> T = T). apply splice_closed with (b := 0). intuition.
    assert (CC.splice (length G) T' = T').
    apply CC.splice_closed with (b := 0). intuition.
    assert (G ~ U = G ~ U +~ map (length G +>) nil) by reflexivity.
    rewrite <- H0. rewrite <- H1. rewrite H2.
    apply wf_thin; eassumption.
  Qed.

  (* If an expression is well-typed as T under context G, then T is a type 
     under G. *)
  Fixpoint hasType_wfTy {G e T e'} (eTe' : G |-d e : T ~> e')
    : sigT (fun T' => G |-d T ~> T')

    with subtype_wfTy {G T U c} (stTUc : G |-d T <: U ~> c)
    : sigT (fun T' => G |-d T ~> T') * sigT (fun U' => G |-d U ~> U')

    with wfCx_wfTy {G} (wfG : G |-d)
    : forall T, In' T G -> sigT (fun T' => G |-d T ~> T').
  Proof.
    * destruct eTe'.
      - apply wfCx_wfTy. assumption. eapply lookup_in'. eassumption.
      - apply hasType_wfTy in eTe'. destruct eTe'. inversion c0. subst.
        do 2 econstructor. assumption. eassumption. eassumption.
      - econstructor. eassumption.
      - apply hasType_wfTy in eTe'1. destruct eTe'1. inversion w. subst.
        admit (* Substitution lemma *).
      - econstructor. econstructor; eassumption.
      - apply subtype_wfTy in s. intuition.

    * destruct stTUc; split.
      1,4: do 2 econstructor; eapply wfTy_wfCx; eassumption.
      1-2,11-12: econstructor; eassumption.
      1-4: eapply subtype_wfTy in stTUc1; eapply subtype_wfTy in stTUc2;
           intuition; destruct a; destruct b; destruct a0; destruct b0;
           do 2 econstructor; eassumption.
      1,4: eapply hasType_wfTy in h; destruct h; inversion w; subst;
           econstructor; eassumption.
      1-2: do 2 econstructor; eassumption.
      1-2: eapply subtype_wfTy in stTUc1; eapply subtype_wfTy in stTUc2;
           intuition.

  Admitted.

  Search "proj".

  Fixpoint d2cc_wfCx 
    {G} (wfG : G |-d) 
    : sig (fun G' => CC.wfCx G')

    with d2cc_wfTy
    {G T T'} (wfTT' : G |-d T ~> T')
    : sig (fun G' => CC.hasType G' T' CC.prop)

    with d2cc_hasType
    {G e T e'} (eTe' : G |-d e : T ~> e')
    : sigT (fun T' => 
        (G |-d T ~> T') * 
        (sig (fun G' => CC.hasType G' e' T'))).
  Proof.
    * destruct wfG.
      - (* wf_nil *) exists nil. constructor.
      - (* wf_snoc wfG w *) apply d2cc_wfCx in wfG. apply d2cc_wfTy in w.
        exists (proj1_sig wfG ~ T'). econstructor. exact (proj2_sig wfG).
  Abort (* proj1_sig wfg = proj1_sig w *).

End D.

(* 
  TODO: 
   1. I seem to need some sort of proof degeneracy theorem. It's not
      proof irrelevance, because it depends on the shape of the proof. 
      For contexts, it might just be that all proofs of G |-d are equal.
   2. Finish thinning, *_wfTy lemmas. The latter might help you in admitA.
   3. 
 *)
