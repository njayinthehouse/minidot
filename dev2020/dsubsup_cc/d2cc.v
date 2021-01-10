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

Inductive lookup {ty} : list ty -> fVar -> ty -> Prop :=
  | first : forall G T, lookup (G ~ T) (length G) T
  | weaken : forall G T U x, lookup G x T -> lookup (G ~ U) x T.

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
    | s_bot : forall G T, G |-d -> G |-s TBot <: T
    | s_top : forall G T, G |-d -> G |-s T <: TTop

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
   is weird, since he derives it by extending LF. I'm not very comfortable 
   with this extension, but I'll add it for now.
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
    | TEx : expr -> expr -> expr
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
  Fixpoint open (i : bVar) (x : fVar) (e : expr) : expr :=
    match e with
    | tVar #j => if i =? j then `x else #j
    | TSort _ | tVar `_ => e
    | TAll T U => TAll (e{i :-> x} T) (e{S i :-> x} U)
    | \:T t => \:(e{i :-> x} T) (e{S i :-> x} t)
    | t $ u => (e{i :-> x} t) $ (e{i :-> x} u)
    | TEx T U => TEx (e{i :-> x} T) (e{S i :-> x} U)
    | t & u :[T] => (e{i :-> x} t) & (e{i :-> x} u) :[e{i :-> x} T]
    | tFst t => tFst (e{i :-> x} t)
    | tSnd t => tSnd (e{i :-> x} t)
    end
    where "e{ i :-> x }" := (open i x) : cc_scope.

  Notation "e *^ x" := (open 0 x e) (at level 50).

  (* Substitution *)
  Reserved Notation "e[ x :-> u ]" (at level 50).
  Fixpoint subst (x : fVar) (u e : expr) : expr :=
    match e with
    | tVar `y => if x =? y then u else `y
    | TSort _ | tVar #_ => e
    | TAll T U => TAll (e[x :-> u] T) (e[x :-> u] U)
    | \:T t => \:(e[x :-> u] T) (e[x:-> u] t)
    | t $ t' => (e[x :-> u] t) $ (e[x :-> u] t')
    | TEx T U => TEx (e[x :-> u] T) (e[x :-> u] U)
    | t & t' :[T] => (e[x :-> u] t) & (e[x :-> u] t') :[e[x :-> u] T]
    | tFst t => tFst (e[x :-> u] t) 
    | tSnd t => tSnd (e[x :-> u] t)
    end
    where "e[ x :-> u ]" := (subst x u) : cc_scope.

  Notation "*[ x :-> u ] e" := (subst x u (e *^ x)) (at level 50).

  Reserved Notation "G |-cc" (no associativity, at level 90).
  Reserved Notation "G |-e e : T" (no associativity, at level 90,
                                   e at next level).
  Reserved Notation "G |-q e == u : T" (no associativity, at level 90,
                                          u at next level).

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

    (* PTS has weakening as an explicit rule. We can (probably?) prove this
       rule from the rest. However, Charguer doesn't add this in his 
       formulation, and Pierce doesn't mention it in ATAPL either. :( *)
    | t_weaken : forall G e T U s,
        G |-e e : T ->
        G |-e U : TSort s ->
        G ~ U |-e e : T

    | t_var : forall G x T,
        G |-cc ->
        lookup G x T ->
        G |-e `x : T

    | t_all : forall G T U sT sU,
        G |-e T : TSort sT ->
        G ~ T |-e U *^ (length G) : TSort sU ->
        G |-e TAll T U : TSort sU

    | t_lam : forall G T U e s,
        G |-e T : TSort s ->
        G ~ T |-e e *^ (length G) : U *^ (length G) ->
        G |-e \:T e : TAll T U

    | t_app : forall G T U t u,
        G |-e t : TAll T U ->
        G |-e u : T ->
        G |-e t $ u : *[length G :-> u] U

    | t_ex : forall G T U sT sU,
        G |-e T : TSort sT ->
        G ~ T |-e U *^ (length G) : TSort sU ->
        G |-e TEx T U : TSort sU

    | t_pair : forall G T U s t u,
        G |-e TEx T U : TSort s ->
        G |-e t : T ->
        G |-e u : *[length G :-> t] U ->
        G |-e t & u :[TEx T U] : TEx T U

    | t_fst : forall G T U e,
        G |-e e : TEx T U ->
        G |-e tFst e : T

    | t_snd : forall G T U e,
        G |-e e : TEx T U ->
        G |-e tSnd e : *[length G :-> tFst e] U

    | t_conv : forall G t s T U,
        G |-e t : T ->
        G |-q T == U : TSort s ->
        G |-e t : U

    where "G |-e e : T" := (hasType G e T) : cc_scope
  
  with equal : cx -> expr -> expr -> expr -> Prop :=
  (* Do I need kind equivalence? I can't show that type = type with these 
     rules. But I don't need that equivalence rule with the t_conv rule. *)
    | q_beta : forall G e u T U,
        G ~ T |-e e *^ (length G) : U *^ (length G) ->
        G |-e u : T ->
        G |-q (\:T e) $ u == *[length G :-> u] e : *[length G :-> u] U

    | q_eta : forall G e T U,
        G |-e e : TAll T U ->
        (* (length G) is not free in e -- not needed coz nameless? *)
        G |-q \:T (e $ #0) == e : TAll T U

    | q_refl : forall G e T, G |-e e : T -> G |-q e == e : T
    | q_sym : forall G e u T, G |-q e == u : T -> G |-q u == e : T
    | q_trans : forall G e u t T,
        G |-q e == u : T ->
        G |-q u == t : T ->
        G |-q e == t : T

    | q_all : forall G T U T' U' (s s' : sort),
        G |-q T == T' : s ->
        G ~ T |-q U *^ (length G) == U' *^ (length G) : s' ->
        G |-q TAll T U == TAll T' U' : s'

    | q_lam : forall G T e T' e' U (s : sort),
        G |-q T == T' : s ->
        G ~ T |-q e *^ (length G) == e' *^ (length G) : U ->
        G |-q \:T e == \:T' e' : TAll T U

    | q_app : forall G e u e' u' T U,
        G |-q e == e' : TAll T U ->
        G |-q u == u' : T ->
        G |-q e $ u == e' $ u' : e[length G :-> u] (U *^ (length G))

    | q_ex : forall G T U T' U' (s s' : sort),
        G |-q T == T' : s ->
        G ~ T |-q U *^ (length G) == U' *^ (length G) : s' ->
        G |-q TEx T U == TEx T' U' : s'

    | q_pair : forall G t T U,
        G |-e t : TEx T U ->
        G |-q (tFst t) & (tSnd t) :[TEx T U] == t : TEx T U

    | q_proj1 : forall G t u T U (s : sort),
        G |-e TEx T U : s ->
        G |-e t : T ->
        G |-e u : e[length G :-> t] (U *^ (length G)) ->
        G |-q (tFst (t & u :[TEx T U])) == t : T

    | q_proj2 : forall G t u T U (s : sort),
        G |-e TEx T U : s ->
        G |-e t : T ->
        G |-e u : e[length G :-> t] (U *^ (length G)) ->
        G |-q (tSnd (t & u :[TEx T U])) == u : T

    where "G |-q e == u : T" := (equal G e u T).

  Hint Constructors wfCx hasType equal : Core.

  Reserved Notation "k +> e" (at level 45, right associativity).
  Fixpoint splice (k : nat) (e : expr) : expr :=
    match e with
    | tVar `x => varF (if k <=? x then S x else x)
    | TSort _ | tVar #_ => e
    | TAll T U => TAll (k +> T) (k +> U)
    | \:T t => \:(k +> T) (k +> t)
    | t $ u => (k +> t) $ (k +> u)
    | TEx T U => TEx (k +> T) (k +> U)
    | t & u :[T] => (k +> t) & (k +> u) :[k +> T]
    | tFst t => tFst (k +> t)
    | tSnd t => tSnd (k +> t)
    end
    where "k +> e" := (splice k e) : cc_scope.

  (* Properties of terms *)

  (* If a term is well-typed under precontext G, then G is a context. *)
  Theorem hasType_wfCx : forall G e T, G |-e e : T -> G |-cc.
  Proof.
    induction 1; try assumption.
    econstructor; eassumption.
  Qed.

  Hint Resolve hasType_wfCx : core.

  (*************************************************************************
   * Shallow embedding of System D<:> 
   * --------------------------------*)

  Definition tId (T : expr) := \:T #0.

  (* Presyntax *)
  Definition TBot := TAll prop #0.
  Definition TTop := TEx prop #0.
  
  Definition TTyp (T U : expr) := 
    TEx prop (TEx (TAll T #1) (TAll #1 U)).

  Definition TSel (x : var) := tFst x.

  Definition tTyp (T : expr) := 
    (T & 
      (tId T & tId T :[TEx (TAll T T) (TAll T T)])
    :[TEx prop (TEx (TAll #0 #1) (TAll #1 #2))]).

  (* Type formation: Our shallow embedding lives in prop, so well formed types
     are simply types that live in prop. *)
  Definition wfTy G T := hasType G T prop.
  Notation "G |-* T" := (wfTy G T) (at level 90) : cc_scope.

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
    G ~ T |-* U *^ (length G) ->
    G |-* TAll T U.
  Proof.
    repeat (constructor || assumption || eassumption || econstructor).
  Qed.

  Lemma wf_typ : forall G T U,
    G |-* T ->
    G |-* U ->
    G |-* TTyp T U.
  Proof.
    econstructor. constructor. eauto. 
    

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
Open Scope cc_scope.

Fixpoint d2ccTy (T : D.ty) : CC.expr :=
  match T with
  | 
