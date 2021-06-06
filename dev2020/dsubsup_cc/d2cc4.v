Require Import List.

Definition fVar : Set := nat.

Definition bVar : Set := nat.

Inductive var : Set :=
  | varB : bVar -> var
  | varF : fVar -> var.

Notation "# i" := (varB i) (at level 0).
Notation "` x" := (varF x) (at level 0).
Notation "G ~ T" := (cons T G) (at level 50).
Notation "G +~ G'" := (G' ++ G) (at level 60).

Bind Scope var_scope with var.
Open Scope var_scope.

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

  Notation "t $" := (tApp t) (at level 4).
  Notation "t & u" := (tPair t u) (at level 4).
  Coercion TSort : sort >-> expr.
  Coercion tVar : var >-> expr.

  
