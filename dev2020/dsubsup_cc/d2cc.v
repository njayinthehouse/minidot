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
  | first : forall G T, lookup (G ~ T) (length G) T
  | weaken : forall G T U x, lookup G x T -> lookup (G ~ U) x T.

(* Lookup -- de Bruijn indices *)
Inductive lookup' {ty} : list ty -> fVar -> ty -> Prop :=
  | z : forall G T, lookup' (G ~ T) 0 T
  | s : forall G T U x, lookup' G x T -> lookup' (G ~ U) (S x) T.

(* We previously used indexr to get the pretype at de Bruijn level x from
   a precontext. *)
Fixpoint indexr {ty} (G : list ty) (x : fVar) : option ty :=
  match G with
  | G' ~ T => if x =? length G' then Some T else indexr G' x
  | nil => None
  end.

(* To convince myself that my lookup is equivalent to indexr. *)
Lemma lookup_indexr : forall ty G x (T : ty), 
  lookup G x T <-> indexr G x = Some T.
Proof.
  split.
  * induction 1.
    - simpl. replace (length G =? length G) with true. reflexivity. 
      rewrite <- beq_nat_refl. reflexivity.
    - simpl. replace (x =? length G) with false. assumption. 
      admit (* If x = length G, then IHlookup is false. *).
  * induction G.
    - discriminate.
    - simpl. destruct (x =? length G) eqn:E.
      + inversion 1. replace x with (length G). constructor. admit (*E*).
      + constructor. eauto.
Admitted.

Lemma lookup_append_r : forall ty (G G' : list ty) x T,
  lookup G x T -> lookup (G +~ G') x T.
Proof.
  induction G'.
  - auto.
  - simpl. constructor. auto.
Qed.

Lemma lookup_fail : forall ty (G : list ty) x T,
  x >= length G -> ~ (lookup G x T).
Proof.
  induction G; simpl; inversion 2; subst.
  + lia.
  + generalize H5. apply IHG. lia.
Qed.

Lemma lookup_drop_r : forall ty (G G' : list ty) T T',
  lookup (G ~ T +~ G') (length G) T' -> T = T'.
Proof.
  induction G'; simpl; inversion 1; subst.
  - reflexivity.
  - apply lookup_fail in H4. contradiction. lia.
  - rewrite app_length in H3. simpl in H3. lia.
  - apply IHG'. assumption.
Qed.

Lemma lookup'_drop_front : forall ty G (T U : ty) x,
  lookup' G x T -> lookup' (nil ~ U +~ G) x T.
Proof.
  induction 1; constructor. assumption.
Qed.

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

Lemma length_elim_middle : forall ty G G' (T : ty), 
  length (G ~ T +~ G') = S (length (G +~ G')).
Proof.
  induction G'.
  - reflexivity.
  - simpl. intros. rewrite IHG'. reflexivity.
Qed.

Lemma lookup_not_x : forall ty G G' x (T T' U : ty),
  lookup (G ~ T +~ G') x U ->
  x <> length G ->
  lookup (G ~ T' +~ G') x U.
Proof.
  intros. destruct (x ?= length G) eqn:E.
  - assert (x = length G). admit (*E*). contradiction.
  - admit (* TODO: Case when x is in G *).
  - admit (* TODO: Case when x is in G' *).
Admitted.


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
    | tPair : expr -> expr -> expr -> expr
    | tFst : expr -> expr
    | tSnd : expr -> expr.

  Definition cx := list expr.
  Definition env := list expr.

  Notation "\: T" := (tLam T) (at level 5) : cc_scope.
  Notation "t $" := (tApp t) (at level 4) : cc_scope.
  Notation "t & u :[ T ]" := (tPair t u T) (at level 4) : cc_scope.
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
    | t & u :[T] => (e{i :-> e'} t) & (e{i :-> e'} u) :[e{i :-> e'} T]
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

  (* Full beta-pi reduction *)
  (* TODO: Do we need eta equality? *)
  Inductive reduce : expr -> expr -> Prop :=
    | r_beta : forall T e u, (\:T e) $ u ~~> e *^ u
    | r_pi1 : forall e u T, tFst (e & u :[T]) ~~> e
    | r_pi2 : forall e u T, tSnd (e & u :[T]) ~~> u
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
    | r_pair1 : forall t u T t', t ~~> t' -> (t & u :[T]) ~~> (t' & u :[T])
    | r_pair2 : forall t u T u', u ~~> u' -> (t & u :[T]) ~~> (t & u' :[T])
    | r_pair3 : forall t u T T', T ~~> T' -> (t & u :[T]) ~~> (t & u :[T'])
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
        G |-e T : TSort sT ->
        G ~ T |-e U *^ varF (length G) : TSort sU ->
        G |-e TAll T U : TSort sU

    | t_lam : forall G T U e s,
        G |-e T : TSort s ->
        G ~ T |-e e *^ varF (length G) : U *^ varF (length G) ->
        G |-e \:T e : TAll T U

    | t_app : forall G T U t u,
        G |-e t : TAll T U ->
        G |-e u : T ->
        G |-e t $ u : U *^ u

    | t_sig : forall G T U sT sU,
        G |-e T : TSort sT ->
        G ~ T |-e U *^ varF (length G) : TSort sU ->
        G |-e TSig T U : TSort sU

    | t_pair : forall G T U s t u,
        G |-e TSig T U : TSort s ->
        G |-e t : T ->
        G |-e u : U *^ t ->
        G |-e t & u :[TSig T U] : TSig T U

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
    | t & t' :[T] => (e[x :-> u] t) & (e[x :-> u] t') :[e[x :-> u] T]
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
    | t & u :[T] => (k +> t) & (k +> u) :[k +> T]
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
    | t & u :[T] => (k -< t) & (k -< u) :[k -< T]
    | tFst t => tFst (k -< t)
    | tSnd t => tSnd (k -< t)
    end
    where "k -<" := (unsplice k) : cc_scope.

  (* Renaming *)
  Reserved Notation "x <~> y" (at level 45, right associativity).
  Fixpoint rename (x y : fVar) (e : expr) : expr :=
    match e with
    | tVar `w => if x =? w then `y else if y =? w then `x else `w
    | TSort _ | tVar #_ => e
    | TAll T U => TAll ((x <~> y) T) ((x <~> y) U)
    | \:T t => \:((x <~> y) T) ((x <~> y) t)
    | t $ u => ((x <~> y) t) $ ((x <~> y) u)
    | TSig T U => TSig ((x <~> y) T) ((x <~> y) U)
    | t & u :[T] => ((x <~> y) t) & ((x <~> y) u) :[(x <~> y) T]
    | tFst t => tFst ((x <~> y) t)
    | tSnd t => tSnd ((x <~> y) t)
    end
    where "x <~> y" := (rename x y) : cc_scope.

  (* Unsplicing is the inverse of splicing. *)
  Lemma splice_unsplice : forall e k, k -< (k +> e) = e.
  Proof.
    induction e; simpl; intros; try (rewrite IHe1; rewrite IHe2); 
    try rewrite IHe3; try rewrite IHe; try reflexivity.
    - destruct v. reflexivity. destruct (k <=? f) eqn:E.
      + simpl. replace (k <=? S f) with true (* since k <= f *).
        assert (f - 0 = f). lia. rewrite H. reflexivity. 
        assert (k <= f). apply Nat.leb_le. assumption.
        assert (k <= S f). lia.
        apply Nat.leb_le in H0. symmetry. assumption.
      + simpl. rewrite E. reflexivity.
  Qed.

  (* Splicing distributes on opening. *)
  Lemma splice_open : forall e t k i, 
    k +> (e{i :-> t} e) = e{i :-> k +> t} (k +> e).
  Proof.
    induction e; simpl; intros; 
    try (rewrite IHe1; rewrite IHe2; try rewrite IHe3); 
    try rewrite IHe;
    try reflexivity.
    - destruct v; simpl. 
      + destruct (i =? b) eqn:E; reflexivity.
      + reflexivity.
  Qed.

  (* Renaming distributes on opening. *)
  Lemma rename_open : forall e t x y i,
    (x <~> y) (e{i :-> t} e) = e{i :-> (x <~> y) t} ((x <~> y) e).
  Proof.
    induction e; simpl; intros;
    try (rewrite IHe1; rewrite IHe2; try rewrite IHe3);
    try rewrite IHe;
    try reflexivity.
    - destruct v; simpl.
      + destruct (i =? b); reflexivity.
      + destruct (x =? f), (y =? f); reflexivity.
  Qed.

  (* Valid renamings *)
  (* !!! *)
  Lemma t_ren : forall G e T,
    G |-e e : T ->
    forall G' G1 T1 G2 T2 G3 r,
    G = G1 ~ T1 +~ G2 ~ T2 +~ G3 ->
    r = length G1 <~> length (G1 ~ T1 +~ G2) ->
    G' = map r (G1 ~ T2 +~ G2 ~ T1 +~ G3) ->
    G' |-cc ->
    G' |-e r e : r T.
  Proof.
    induction 1; intros G' G1 T1 G2 T2 G3 r Geq req G'eq H'.
    - rewrite req. constructor. assumption.
    - rewrite req. simpl. destruct (length G1 =? x) eqn:E.
      + constructor. assumption. rewrite G'eq. rewrite <- req. 
        apply lookup_map. 
        assert (length (G1 ~ T1 +~ G2) = length (G1 ~ T2 +~ G2)).
        { repeat rewrite length_elim_middle. reflexivity. }
        rewrite H1. simpl. 
        assert (length G1 = x). { apply beq_nat_true. assumption. }
        assert (T1 = T).
        { eapply lookup_drop_r. rewrite Geq in H0. rewrite <- H2 in H0.
          rewrite app_assoc in H0. eassumption. }
        rewrite H3. apply lookup_append_r. constructor.
      + destruct (length (G1 ~ T1 +~ G2) =? x) eqn:E'.
        * constructor. assumption. rewrite G'eq. rewrite <- req.
          apply lookup_map. 
          assert (length (G1 ~ T1 +~ G2) = x). 
          { apply beq_nat_true. assumption. }
          assert (T2 = T).
          { eapply lookup_drop_r. rewrite Geq in H0. 
            rewrite <- app_comm_cons in H0. rewrite <- H1 in H0.
          eassumption. }
          rewrite <- H2. rewrite app_assoc. apply lookup_append_r. constructor.
        * admit (* TODO: Use lookup_not_x *).
    - rewrite req. simpl. rewrite <- req.
      assert (G' |-e r T : sT).
      { replace (TSort sT) with (r sT). eapply IHhasType1; eassumption.
        rewrite req. reflexivity. }
      econstructor. 
      + eassumption. 
      + replace (tVar (` (length G'))) with (r (` (length G))).
        rewrite req. rewrite <- rename_open. 
        replace (TSort sU) with (r sU). rewrite <- req.
        eapply IHhasType2 with (G1 := G1) (G2 := G2) (G3 := G3 ~ T).
        rewrite Geq. reflexivity. assumption. rewrite G'eq. reflexivity.
        econstructor; eassumption. rewrite req. reflexivity. rewrite req.
        admit (* length G not in {length G1, length G1 ~ T1 +~ G2} *).
    - admit (* TODO: Similar to TAll case *).
    - admit (* TODO *).
    - admit (* TODO: Similar to TAll case *).
    - admit (* TODO *).
    - admit (* TODO *).
    - admit (* TODO *).
    - admit (* TODO *).
  Admitted.

  (* Any typing judgment under context G is valid under context G ~ T. *)
  (* !!! *)
  Lemma t_weaken : forall G e T,
    G |-e e : T ->
    forall U s, 
    G |-e U : TSort s ->
    G ~ U |-e e : T. 
  Proof.
    induction 1.
    - constructor. econstructor; eassumption.
    - constructor. econstructor; eassumption. constructor. assumption.
    - econstructor.
      + eapply IHhasType1. eassumption.
      + remember (length G <~> length (G ~ U)) as r.
        assert (r U = U).
        { admit (* 
              U is the body of the TAll, which is well formed under G.
              Thus, it is not locally closed, but it does not contain
              any free variables that are not in G.
          *). }
        assert (U *^ ` (length (G ~ U0)) = r (U *^ ` (length G))).
        { rewrite Heqr. rewrite rename_open. simpl. rewrite <- beq_nat_refl.
          simpl in Heqr. rewrite <- Heqr. rewrite H2. reflexivity. }
        rewrite H3. 
        replace (TSort sU) with (r sU).
        apply t_ren with (G := G ~ T ~ U0) (G' := G ~ U0 ~ T)
          (G1 := G) (T1 := T) (G2 := nil) (T2 := U0) (G3 := nil).
        eapply IHhasType2.
  Abort (* 
      We're stuck trying to prove G ~ T |-e U0 : s0. We have G |-e U0 : s0,
      but no suitable IH. We likely cannot use Fixpoint to give us more 
      power, because we use renaming to prove that the codomain of TAll is
      well-formed. However, this looks like a potential candidate for well-
      founded recursion -- renaming doesn't grow the term. 
  *).
        

  (* Any pretype in a context is a type. *)
  Theorem wfCx_lookup : forall G,
    G |-cc ->
    forall T, In T G ->
    exists s : sort, G |-e T : s.
  Admitted.

  Hint Resolve wfCx_lookup : core.

  Lemma hasType_splice : forall G G' e T,
    G' +~ G |-e e : T ->
    forall U,
    G' ~ U +~ map (length G' +>) G |-cc ->
    G' ~ U +~ map (length G' +>) G |-e (length G' +> e) : (length G' +> T).
  Proof.
    (* Attempted induction on 1, nonsense IH2 in TAll case *)
    intros ? ? ? ? ?. remember (G' +~ G) as G'G. induction H; subst.
    - constructor. assumption.
    - simpl. destruct (length G' <=? x) eqn:E.
      + constructor. assumption. 
        admit (* 
            1. S x >= length (G' ~ U) -> S x = length (G' ~ U) + x' for some x'
               TODO: Define split_nat.
            2. Goal: lookup (map (length G' +>) G) x' (length G' +> T)
               TODO: Prove that lookup (T +~ G) (S x) U -> lookup G x U
            3. Goal: lookup G x' T
               TODO: Prove lookup_map
            H0: lookup G x' T
        *).
      + constructor. assumption.
        admit (*
            Goal: lookup (map (length G' +>) G' ~ U +~ map (length G' +>) G)
                         x (length G' +> T)
            Since x < length G',
            Goal: lookup (map (length G' +>) G') x (length G' +> T)
            Goal: lookup G' x T
            H0: lookup G' x T
        *).
    - Abort (* That second induction hypothesis is nonsense. *).
  (* forall n, esize_flat e <= n, lemma <<- guard the proof*)
  Fixpoint hasType_splice G G' e T (H : G +~ G' |-e e : T)
      : forall U, 
        G ~ U +~ map (length G +>) G' |-cc -> 
        G ~ U +~ map (length G +>) G' |-e length G +> e : length G +> T.
  Proof.
    remember (G +~ G') as GG'. 
    assert (forall k (s : sort), TSort s = k +> s). reflexivity.
    destruct H; subst.
    - constructor. assumption.
    - constructor. assumption. admit (* lookup_splice *).
    - simpl. econstructor; erewrite H0. 
      + apply hasType_splice; eassumption.
      + (* Rewrite the expression to the form (length G +> (U *^ `x)) *)
        rewrite length_elim_middle. 
        assert (tVar (varF (S (length (G +~ map (length G +>) G')))) =
                  length G +> (varF (length (G +~ map (length G +>) G')))).
        { simpl. admit (* length G <= length (G +~ map (length G +>) G')*). }
        rewrite H3. rewrite <- splice_open. 
        (* Rewrite the context to the form (G1 ~ T +~ G2) *)
        replace ((G ~ U0 +~ map (length G +>) G') ~ length G +> T) with
          (G ~ U0 +~ map (length G +>) (G' ~ T)).
        apply hasType_splice.
        replace (G +~ G' ~ T) with ((G +~ G') ~ T). 
        replace (length (G +~ map (length G +>) G')) with (length (G +~ G')).
        assumption. admit (* map preserves length *). 
        admit (* cons and append commute *). simpl. econstructor. assumption.
        erewrite H0. apply hasType_splice. eassumption. assumption.
        reflexivity.
    - admit (* TODO: Should be same as TAll case *).
    - admit (* TODO *).
    - admit (* TODO: Should be same as TAll and tLam cases *).
    - admit (* TODO *).
    - admit (* TODO *).
    - admit (* TODO *).
  Abort (* I strongly suspect this proof will be rejected because Coq's 
    primitive recursion scheme won't be able to tell that this definition is
    indeed well-founded. I'd have to use well-founded recursion. But I'm not
    clear what the well-founded relation should be here -- we have to prove
    that U *^ (length G) < TAll T U. I suppose a relation which says that
    opening U with a variable makes it less than TAll T U would work.
  *).

  (* This time, I'mma try using the Fix combinator. *)
  Reserved Notation "e e<= u" (at level 90, no associativity).
  Inductive expr_lt : expr -> expr -> Prop :=
    | lt_sort : forall T s, TSort s e<= T
    | lt_var : forall T x, tVar x e<= T
    | lt_all1 : forall T U, T e<= TAll T U
    | lt_all2 : forall T U, U e<= TAll T U
    | lt_lam1 : forall T e, T e<= \:T e
    | lt_lam2 : forall T e, e e<= \:T e
    | lt_app1 : forall e u, e e<= e $ u
    | lt_app2 : forall e u, u e<= e $ u
    | lt_sig1 : forall T U, T e<= TSig T U
    | lt_sig2 : forall T U, U e<= TSig T U
    | lt_pair1 : forall t u T, t e<= (t & u :[T])
    | lt_pair2 : forall t u T, u e<= (t & u :[T])
    | lt_pair3 : forall t u T, T e<= (t & u :[T])
    | lt_fst : forall t, t e<= tFst t
    | lt_snd : forall t, t e<= tSnd t
    | lt_open : forall e u i x, e e<= u -> e{i :-> tVar x} e e<= u
    where "e e<= u" := (expr_lt e u) : cc_scope.

  (* A more intuitive measure *)
  Fixpoint esize_flat (e : expr) : nat :=
    match e with
    | TSort _ | tVar _ => 0
    | TAll T U | \:T U | T $ U | TSig T U => S (esize_flat T + esize_flat U)
    | t & u :[T] => S (esize_flat t + esize_flat u + esize_flat T)
    | tFst t | tSnd t => S (esize_flat t)
    end.

  (* Opening with a variable preserves size *)
  Lemma open_var_size : forall e x i,
    esize_flat e = esize_flat (e{i :-> tVar x} e).
  Proof.
    induction e; intros; simpl; eauto.
    destruct v; try destruct (i =? b); auto.
  Qed.

  Lemma wf'_expr_lt : forall n e, esize_flat e <= n -> Acc expr_lt e.
  Proof.
    induction n.
    - destruct e; intros. constructor; intros; simpl in *; inversion H0;
      subst; try lia. Print Acc. constructor.  admit (* TODO:% How do I proceed? :P *).
  Admitted.

  Theorem wf_expr_lt : well_founded expr_lt. Admitted.

  Print Fix.
  (*
  Definition hasType_splice {G G' e T} 
    (H1 : G' +~ G |-e e : T)
    {U} (H2 : G' ~ U +~ map (length G' +>) G |-cc) :
    G' ~ U +~ map (length G' +>) G |-e (length G' +> e) : (length G' +> T).
  refine (
  Fix wf_expr_lt 
  (fun _ => 
    G' ~ U +~ map (length G' +>) G |-e (length G' +> e) : (length G' +> T))
  (fun ()))
   *)

  Lemma hasType_splice : forall G G' e T,
    G' +~ G |-e e : T ->
    forall U,
    G' ~ U +~ map (length G' +>) G |-cc ->
    G' ~ U +~ map (length G' +>) G |-e (length G' +> e) : (length G' +> T).
  Proof. admit. Admitted.

  (* If a term is well-typed under precontext G, then G is a context. *)
  Theorem hasType_wfCx : forall G e T, G |-e e : T -> G |-cc.
  Proof.
    induction 1; try assumption.
  Qed.

  Hint Resolve hasType_wfCx : core.

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

  Definition wfTy G T := hasType G T prop.
  Notation "G |-* T" := (wfTy G T) (at level 90) : cc_scope.

  (* Type formation: Our shallow embedding lives in prop, so well formed types
     are simply types that live in prop. *)
  Lemma wf_bot : forall G, G |-cc -> G |-* TBot.
  Proof.
    repeat (constructor || assumption || econstructor).
  Qed.

  Lemma wf_top : forall G, G |-cc -> G |-* TTop.
  Proof.
    repeat (constructor || assumption || econstructor).
  Qed.

  Lemma wf_all : forall G T U,
    G |-* T ->
    G ~ T |-* U *^ varF (length G) ->
    G |-* TAll T U.
  Proof.
    repeat (constructor || assumption || eassumption || econstructor).
  Qed.

  Lemma wf_typ : forall G T U,
    G |-* T ->
    G |-* U ->
    G |-* TTyp T U.
  Proof.
    intros.
    assert (T *^ varF (length G) = T). admit (* TODO: From G |-* T *).
    assert (G ~ TSort prop |-* T). admit (* TODO: Weakening on H *).
    assert (forall i t, e{i :-> t} U = U). admit (* TODO: From G |-* T *).
    assert (forall T1 T2, G ~ TSort prop ~ T1 ~ T2 |-* U). 
    admit (* TODO: Weakening on H0. *).
    assert (G ~ TSort prop |-* TAll T (varF (length G))).
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
 * [ ] Types
 * [ ] Contexts
 * [ ] Terms
 * [ ] Reduction preservation *)

Open Scope d_scope.
Open Scope cc_scope.Z
