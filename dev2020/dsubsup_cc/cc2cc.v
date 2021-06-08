Require Import Lia List PeanoNat.
Import Notations.

Axiom proof_irrelevance: forall {P: Prop} (p1 p2: P), p1 = p2.

(* Variables and Contexts *)
Definition fVar : Set := nat.

Definition bVar : Set := nat.

Inductive var : Set :=
  | varB : bVar -> var
  | varF : fVar -> var.

Notation "# i" := (varB i) (at level 0) : var_scope.
Notation "` x" := (varF x) (at level 0) : var_scope.
Notation "g ~ T" := (cons T g) (at level 50) : var_scope.
Notation "g +~ g'" := (g' ++ g) (at level 60) : var_scope.

Bind Scope var_scope with var.
Open Scope var_scope.

(* Lookup -- de Bruijn levels *)
Inductive lookup {ty} : list ty -> fVar -> ty -> Prop :=
  | last : forall g T, lookup (g ~ T) (length g) T
  | prev : forall g T U x, lookup g x T -> lookup (g ~ U) x T.


Inductive sort: Set := prop | type.

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

Coercion TSort: sort >-> expr.
Coercion tVar: var >-> expr.

(* Opening *)
Reserved Notation "e{ i :-> x }" (at level 50).
Fixpoint open (i : bVar) (e' e : expr) : expr :=
  match e with
  | tVar #j => if i =? j then e' else #j
  | TSort _ | tVar `_ => e
  | TAll T U => TAll (e{i :-> e'} T) (e{S i :-> e'} U)
  | tLam t => tLam (e{S i :-> e'} t)
  | tApp t u => tApp (e{i :-> e'} t) (e{i :-> e'} u)
  | TSig T U => TSig (e{i :-> e'} T) (e{S i :-> e'} U)
  | tPair t u => tPair (e{i :-> e'} t) (e{i :-> e'} u)
  | tFst t => tFst (e{i :-> e'} t)
  | tSnd t => tSnd (e{i :-> e'} t)
  end
  where "e{ i :-> e' }" := (open i e').

Notation "e *^ u" := (open 0 u e) (at level 50).

Reserved Notation "e ~~> u" (no associativity, at level 90).

Compute (e{0 :-> tVar (varF 1)} (tLam (varB 2))).

(* Closed expressions *)
Inductive closed (b f : nat) : expr -> Prop :=
  | cl_sort : forall s : sort, closed b f s
  | cl_varF : forall x, x < f -> closed b f `x
  | cl_varB : forall i, i < b -> closed b f #i
  | cl_all : forall T U, 
      closed b f T -> closed (S b) f U -> closed b f (TAll T U)
  | cl_lam : forall e, closed (S b) f e -> closed b f (tLam e)
  | cl_app : forall t u,
      closed b f t -> closed b f u -> closed b f (tApp t u)
  | cl_sig : forall T U,
      closed b f T -> closed (S b) f U -> closed b f (TSig T U)
  | cl_pair : forall t u,
      closed b f t -> closed b f u -> closed b f (tPair t u)
  | cl_fst : forall t, closed b f t -> closed b f (tFst t)
  | cl_snd : forall t, closed b f t -> closed b f (tSnd t).

Reserved Notation "e ~~> u" (no associativity, at level 90).
Inductive reduce : expr -> expr -> Prop :=
  | r_beta : forall e u, tApp (tLam e) u ~~> e *^ u
  | r_eta : forall e, (tLam (tApp e #0)) ~~> e
  | r_pi1 : forall e u, tFst (tPair e u) ~~> e
  | r_pi2 : forall e u, tSnd (tPair e u) ~~> u
  | r_all1 : forall T U T', T ~~> T' -> TAll T U ~~> TAll T' U
  | r_all2 : forall T U U', U ~~> U' -> TAll T U ~~> TAll T U'
  | r_lam : forall e e', e ~~> e' -> tLam e ~~> tLam e'
  | r_app1 : forall e u e', e ~~> e' -> tApp e u ~~> tApp e' u
  | r_app2 : forall e u u', u ~~> u' -> tApp e u ~~> tApp e u'
  | r_sig1 : forall T U T', T ~~> T' -> TSig T U ~~> TSig T' U
  | r_sig2 : forall T U U', U ~~> U' -> TSig T U ~~> TSig T U'
  (* The lecture notes linked above don't mention adding these 
     substructural rules for pairs, but I think they're required, else
     we can't reduce inside tuples. *)
  | r_pair1 : forall t u t', t ~~> t' -> tPair t u ~~> tPair t' u
  | r_pair2 : forall t u u', u ~~> u' -> tPair t u ~~> tPair t u'
  | r_fst : forall t t', t ~~> t' -> tFst t ~~> tFst t'
  | r_snd : forall t t', t ~~> t' -> tSnd t ~~> tSnd t'
   where "e ~~> u" := (reduce e u).

Reserved Notation "e == u" (at level 90, no associativity).
Inductive equals: expr -> expr -> Prop :=
  | e_red: forall {e u}, e ~~> u -> e == u
  | e_refl: forall {e}, e == e
  | e_sym: forall {e u}, e == u -> u == e
  | e_trans: forall {e u t}, e == u -> u == t -> e == t
  where "e == u" := (equals e u).

Inductive hasType: cx -> expr -> expr -> Prop :=
  | t_ax: forall {g}, hasType g prop type

  | t_var: 
      forall {g x T}, lookup g x T ->
      hasType g `x T

  | t_all:
      forall {g T sT}, hasType g T (TSort sT) ->
      forall {U sU}, hasType (g ~ T) (U *^ varF (length g)) (TSort sU) ->
      closed 1 (length g) U ->
      hasType g (TAll T U) sU

  | t_lam: 
      forall {g T s}, hasType g T (TSort s) ->
      forall {e U}, hasType (g ~ T) (e *^ ` (length g)) (U *^ ` (length g)) ->
      closed 0 (length g) (TAll T U) ->
      closed 1 (length g) e ->
      hasType g (tLam e) (TAll T U)

  | t_app:
      forall {g e T U}, hasType g e (TAll T U) ->
      forall {u}, hasType g u T ->
      hasType g (tApp e u) (U *^ u)

  | t_sig:
      forall {g T sT}, hasType g T (TSort sT) ->
      forall {U sU}, hasType (g ~ T) (U *^ varF (length g)) (TSort sU) ->
      closed 1 (length g) U ->
      hasType g (TSig T U) sU

  | t_pair:
      forall {g T U s}, hasType g (TSig T U) (TSort s) ->
      forall {t}, hasType g t T ->
      forall {u}, hasType g u (U *^ t) ->
      hasType g (tPair t u) (TSig T U)

  | t_fst: 
      forall {g e T U}, hasType g e (TSig T U) -> 
      hasType g (tFst e) T

  | t_snd:
      forall {g e T U}, hasType g e (TSig T U) ->
      hasType g (tSnd e) (U *^ tFst e)

  | t_conv:
      forall {g e T}, hasType g e T ->
      forall {U}, T == U ->
      forall {s}, hasType g U (TSort s) ->
      hasType g e U.

Inductive wfCx: cx -> Prop :=
  | wf_nil: wfCx nil
  | wf_snoc: 
      forall {g}, wfCx g ->
      forall {T} {s: sort}, hasType g T s -> 
      wfCx (g ~ T).

Theorem lookup_closed:
  forall {g: cx} {x T}, lookup g x T -> closed 0 (length g) `x.
Proof.
  induction 1.
  - constructor. simpl. lia.
  - inversion IHlookup. constructor. simpl. lia.
Qed.

Theorem hasType_closed: 
  forall {g e T}, hasType g e T -> closed 0 (length g) e.
Proof.
  induction 1; auto; try solve [constructor; auto].
  eapply lookup_closed. eassumption.
Qed.

Inductive lookupTr: cx -> fVar -> expr -> cx -> fVar -> expr -> Prop :=
  | tr_top: forall {g T g' T'}, 
      lookupTr (g ~ T) (length g) T (g' ~ T') (length g') T'

  | tr_pop: 
      forall {g x T g' x' T'}, lookupTr g x T g' x' T' ->
      forall {U U'}, lookupTr (g ~ U) x T (g' ~ U') x' T'.

  Inductive hasTypeTr: cx -> expr -> expr -> cx -> expr -> expr -> Prop :=
  | tr_ax: 
      forall {g g'}, hasTypeTr g prop type g' prop type

  | tr_var:
      forall {g x T g' x' T'}, lookupTr g x T g' x' T' ->
      hasTypeTr g `x T g' `x' T'

  | tr_all:
      forall {g T g' T'} {sT sT': sort}, hasTypeTr g T sT g' T' sT' ->
      forall {U U'} {s s': sort}, hasTypeTr (g ~ T) (U *^ ` (length g)) s 
                                    (g' ~ T') (U'*^ ` (length g')) s' ->
      hasTypeTr g (TAll T U) s g' (TAll T' U') s'
  
  | tr_lam: 
      forall {g T g' T'} {sT sT': sort}, hasTypeTr g T sT g' T' sT' ->
      forall {e U e' U'}, 
      hasTypeTr (g ~ T) (e *^ ` (length g)) (U *^ ` (length g))
                (g' ~ T') (e' *^ ` (length g')) (U' *^ ` (length g')) ->
      hasTypeTr g (tLam e) (TAll T U) g' (tLam e') (TAll T' U')

  | tr_app: forall {g e T U g' e' T' U'}, 
      hasTypeTr g e (TAll T U) g' e' (TAll T' U') ->
      forall {u u'}, hasTypeTr g u T g' u' T' ->
      hasTypeTr g (tApp e u) (U *^ u) g' (tApp e' u') (U' *^ u')

  | tr_sig:
      forall {g T g' T'} {sT sT': sort}, hasTypeTr g T sT g' T' sT' ->
      forall {U U'} {s s': sort}, hasTypeTr (g ~ T) (U *^ ` (length g)) s 
                                    (g' ~ T') (U'*^ ` (length g')) s' ->
      hasTypeTr g (TSig T U) s g' (TSig T' U') s'

  | tr_pair: forall {g T U g' T' U'} {s s': sort}, 
      hasTypeTr g (TSig T U) s g' (TSig T' U') s' ->
      forall {t t'}, hasTypeTr g t T g' t' T' ->
      forall {u u'}, hasTypeTr g u (U *^ t) g' u' (U' *^ t') ->
      hasTypeTr g (tPair t u) (TSig T U) g' (tPair t' u') (TSig T' U')

  | tr_fst: forall {g T U g' T' U'}, 
      forall {e e'}, hasTypeTr g e (TSig T U) g' e' (TSig T' U') ->
      hasTypeTr g (tFst e) T g' (tFst e') T'

  | tr_snd: forall {g T U g' T' U'},
      forall {e e'}, hasTypeTr g e (TSig T U) g' e' (TSig T' U') ->
      hasTypeTr g (tSnd e) (U *^ tFst e) g' (tSnd e') (U' *^ tFst e')

  | tr_conv: 
      forall {g e T g' e' T'}, hasTypeTr g e T g' e' T' ->
      forall {U}, T == U ->
      forall {U'}, T' == U' ->
      forall {s s': sort}, hasTypeTr g U s g' U' s' ->
      hasTypeTr g e U g' e' U'.

Inductive wfCxTr: cx -> cx -> Prop :=
  | tr_nil: wfCxTr nil nil

  | tr_snoc: 
      forall {g g'}, wfCxTr g g' ->
      forall {T T'} {s s': sort}, hasTypeTr g T s g' T' s' ->
      wfCxTr (g ~ T) (g' ~ T').

Theorem lookupTr_lookup:
  forall {g x T g' x' T'}, lookupTr g x T g' x' T' ->
  lookup g x T /\ lookup g' x' T'.
Proof.
  induction 1.
  - repeat constructor.
  - intuition; constructor; assumption.
Qed.

Theorem hasTypeTr_hasType: 
  forall {g e T g' e' T'}, hasTypeTr g e T g' e' T' ->
  hasType g e T /\ hasType g' e' T'.
Proof.
  induction 1; split; econstructor; try intuition eauto.
  1,2: apply lookupTr_lookup in H; intuition.
Admitted.

Theorem lookup_lookupTr:
  forall {g x T}, lookup g x T ->
  lookupTr g x T g x T.
Proof.
  induction 1; constructor. auto.
Qed.

Theorem hasType_hasTypeTr:
  forall {g e T}, hasType g e T -> 
  hasTypeTr g e T g e T.
Proof.
  induction 1; try solve [econstructor; eauto].
  constructor. apply lookup_lookupTr. auto.
Qed.
