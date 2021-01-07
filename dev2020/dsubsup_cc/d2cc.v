Require Import List.
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

Bind Scope var_scope with var.
Open Scope var_scope.

Fixpoint lookup {ty} (G : list ty) (x : fVar) : option ty :=
  match G with
  | nil => None
  | G' ~ A => if length G =? x then Some A else lookup G' x
  end.

(***************************************************************************
 * System D<:>
 * -----------
 * [X] Presyntax
 * [X] Opening
 * [X] Context formation
 * [ ] Type formation
 * [ ] Typechecking
 * [ ] Subtyping
 * [ ] Splicing
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
  Reserved Notation "T{ i :-> x }" (at level 50).
  Fixpoint openTy (i : bVar) (x : fVar) (T : ty) : ty :=
    match T with
    | TSel #j => TSel (if i =? j then `x else #j)
    | TBot | TTop | TSel `_ => T
    | TAll T1 T2 => TAll (T{i :-> x} T1) (T{S i :-> x} T2)
    | TTyp T1 T2 => TTyp (T{i :-> x} T1) (T{i :-> x} T2)
    end
    where "T{ i :-> x }" := (openTy i x) : d_scope.

  Reserved Notation "t{ i :-> x }" (at level 50).
  Fixpoint openTm (i : bVar) (x : fVar) (t : tm) : tm :=
    match t with
    | tVar #j => if i =? j then `x else #j
    | tVar `_ => t
    | \:T e => \:(T{i :-> x} T) (t{i :-> x} e)
    | e $ u => (t{i :-> x} e) $ (t{i :-> x} u)
    | tTyp T => tTyp (T{i :-> x} T)
    end
    where "t{ i :-> x }" := (openTm i x) : d_scope.

  Notation "T ^* x" := (openTy 0 x T) (at level 50).
  Notation "t ^^ x" := (openTm 0 x t) (at level 50).

  Reserved Notation "G |-d" (no associativity, at level 90).
  Reserved Notation "G |-ty T" (no associativity, at level 90).
  Reserved Notation "G |-tm t : T" (no associativity, at level 90,
                                    t at next level).
  Reserved Notation "G |-s T <: U" (no associativity, at level 90).

  (* Context Formation *)
  Inductive wfCx : cx -> Prop :=
    | wf_nil : nil |-d

    | wf_cons : forall G T,
        G |-d ->
        G |-ty T ->
        G ~ T |-d

    where "G |-d" := (wfCx G) : d_scope

  with wfTy : cx -> ty -> Prop :=
    | wf_bot : forall G, G |-ty TBot

    where "G |-ty T" := (wfTy G T) : d_scope.

(***************************************************************************
 * Calculus of Constructions
 * -------------------------
 * [ ] Presyntax
 * [ ] Opening
 * [ ] Evaluation
 * [ ] Context formation
 * [ ] Typechecking 
 * [ ] Splicing
 * [ ] Optional: Locally closed predicate
 * - Required Lemmas (TBD) *)

(***************************************************************************
 * Translation
 * -----------
 * [ ] Presyntax
 * [ ] Types
 * [ ] Contexts
 * [ ] Terms
 * [ ] Reduction preservation *)
