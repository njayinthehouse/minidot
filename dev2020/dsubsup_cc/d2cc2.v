Require Import List.

Infix "\o" := (fun f g x => f (g x)) (at level 50).

Module Cx.
  Section var.
    Context {var ty : Type}.
    Hypothesis lem_var : forall x y : var, {x = y} + {x <> y}.

    Definition t : Type := list (var * ty).

    Inductive lookup : t -> var -> ty -> Prop :=
      | top : forall {G x T}, lookup ((x, T) :: G) x T
      | pop : forall {G x T}, lookup G x T -> 
              forall {y U}, x <> y -> lookup ((y, U) :: G) x T.

    Definition isFresh (G : t) (x : var) : Prop := forall T, ~ lookup G x T.
    Definition eq (G D : t) := forall x T, lookup G x T <-> lookup D x T.

  End var.
End Cx.

Module Result.

  Inductive t (X : Type) := 
    | Ok : X -> nat -> t X
    | Fail : t X
    | NoFuel : t X.

  Definition bind {X} (u : t X) {Y} (f : X -> nat -> t Y) : t Y :=
    match u with
    | Ok _ x n => f x n
    | Fail _ => Fail _
    | NoFuel _ => NoFuel _
    end.

End Result.

Notation "'do' x , n <- e ; u" := (Result.bind e (fun n x => u))
  (at level 200, x ident, n ident, e at level 100, u at level 200).

Module CC.
  (* We're adopting the Theory of Contexts. Thus, we parameterize over all
     variables and postulate decidable equality. *)
  Parameter var : Type.
  Hypothesis lem_var : forall x y : var, {x = y} + {x <> y}.

  Definition beq_var (x y : var) : bool :=
    match lem_var x y with
    | left _ => true
    | right _ => false
    end.

  (* Presyntax *)
  Inductive sort : Type := prop | type.

  Inductive expr : Type :=
    | TSort : sort -> expr
    | tVar : var -> expr
    | TAll : expr -> (var -> expr) -> expr
    | tLam : (var -> expr) -> expr
    | tApp : expr -> expr -> expr
    | TSig : expr -> (var -> expr) -> expr
    | tPair : expr -> expr -> expr
    | tFst : expr -> expr
    | tSnd : expr -> expr.

  Definition cx : Type := @Cx.t var expr.

  Coercion TSort : sort >-> expr.
  Coercion tVar : var >-> expr.

  (* The Theory of Contexts is actually a theory about term contexts, or
     holes. *)
  Fixpoint hole (n : nat) : Type :=
    match n with
    | 0 => expr
    | S n' => var -> hole n'
    end.

  Inductive isFresh (x : var) : forall n, hole n -> Prop :=
    | fr_sort : forall s : sort, isFresh x 0 s
    | fr_var : forall y, x <> y -> isFresh x 0 y
    | fr_all : forall T U, 
        isFresh x 0 T -> isFresh x 1 U -> isFresh x 0 (TAll T U)
    | fr_lam : forall t, isFresh x 1 t -> isFresh x 0 (tLam t)
    | fr_app : forall t u, 
        isFresh x 0 t -> isFresh x 0 u -> isFresh x 0 (tApp t u)
    | fr_sig : forall T U, 
        isFresh x 0 T -> isFresh x 1 U -> isFresh x 0 (TSig T U)
    | fr_pair : forall t u, 
        isFresh x 0 t -> isFresh x 0 u -> isFresh x 0 (tPair t u)
    | fr_fst : forall t, isFresh x 0 t -> isFresh x 0 (tFst t)
    | fr_snd : forall t, isFresh x 0 t -> isFresh x 0 (tSnd t)
    | fr_hole : forall e y, isFresh x 0 (e y) -> isFresh x 0 y -> isFresh x 1 e.

  Hypothesis freshVarP : forall {n} e, sig (fun x => isFresh x n e).
  Definition freshVar {n} (e : hole n) : var := proj1_sig (freshVarP e).

  (* Holes are actually monads on variable representation in non-dependently 
     typed systems. They are almost monads in our dependently typed language. *)
  Fixpoint flatMap {n} (f : var -> hole n) {m} : hole m -> hole (n + m).
  Abort.
  (* But we don't need that kind of expressive power for now. Let's settle for 
     this slightly less powerful function. *)
  Fixpoint flatMap (f : var -> expr) (e : expr) : expr :=
    match e with
    | TSort s => TSort s
    | tVar x => f x
    | TAll T U => TAll (flatMap f T) (flatMap f \o U)
    | tLam t => tLam (flatMap f \o t)
    | tApp t u => tApp (flatMap f t) (flatMap f u)
    | TSig T U => TSig (flatMap f T) (flatMap f \o U)
    | tPair t u => tPair (flatMap f t) (flatMap f u)
    | tFst t => tFst (flatMap f t)
    | tSnd t => tSnd (flatMap f t)
    end.

  Definition subst (x : var) (e : expr) : var -> expr := 
    fun y => if beq_var x y then e else y.
  Notation "[ e \ x ]" := (flatMap (subst x e)) (at level 50).

  Definition close (x : var) (e : expr) : var -> expr := fun y => [y \ x] e.

  (*
  (* Postulate unsaturation? *)
  Fixpoint eval (fuel : nat) (e : expr) : Result.t (expr * nat).
  Proof.
    refine(
    match fuel with
    | 0 => Result.NoFuel _

    | S fuel' =>
        match e with
        | TSort s => 
          Result.Ok _ (TSort s) fuel'

        | tVar x => 
          Result.Ok _ (tVar x) fuel'

        | TAll T U =>
          do T', n1 <- eval fuel' T;
          let x := freshVar U in
          do U', n2 <- eval1 n (U x);
          Result.Ok _ (TAll T' (close x U')) n2

        | tLam t => 
          let x := freshVar t in
          do t', n <- eval fuel' (t x);
          Result.Ok _ (tLam (close x t')) n

        | tApp t u => 
          do t', n1 <- eval fuel' t;
          match t' with
          | tLam w =>
            do u', n2 <- eval n1 u;
            _

          | _ => Result.Fail _
          end

        | TSig T U => 
          do T', n1 <- eval fuel' T;
          let x := freshVar U' in
          do U', n2 <- eval n1 (U x);
          Result.Ok _ (TSig T' (close x U')) n2

        | tPair t u => 
          do t', n1 <- eval fuel' t;
          do u', n2 <- eval n1 u;
          Result.Ok _ (tPair t' u') n2

        | tFst t => 
          do t', n <- eval fuel' t;
          match (fst tk) with
          | tPair u _ => 
            if n >=? 0 then Result.Ok _ 

          | _ => Result.Fail _
          end

        | tSnd t => 
          do tk <- eval fuel' t;
          match (fst tk) with
          | tPair _ u =>
            Result.Ok _ (u, snd tk)

          | _ => Result.Fail _
          end
        end
     end).
  Proof.

  Inductive step : expr -> expr -> Prop :=
    | r_beta : forall t u x, step (tApp (tLam t) u) ([u \ ])
   *)
  
  Definition Eq (e u : expr) : Prop := True.

  Inductive Cx : cx -> Prop :=
    | Nil : Cx nil

    | Snoc : forall {G T x s},
        Expr G T (TSort s) ->
        Cx.isFresh G x ->
        Cx ((x, T) :: G)

    with Expr : cx -> expr -> expr -> Prop :=
    | TyAx : forall {G}, Cx G -> Expr G prop type
    | tmVar : forall {G x T}, Cx G -> Cx.lookup G x T -> Expr G x T

    | TyAll : forall {G T s U s' x},
        Expr G T (TSort s) ->
        Expr ((x, T) :: G) (U x) (TSort s') ->
        Cx.isFresh G x -> (* Do we need this? *)
        Expr G (TAll T U) (TSort s')

    | tmLam : forall {G T s t U x},
        Expr G T (TSort s) ->
        Expr ((x, T) :: G) (t x) (U x) ->
        Cx.isFresh G x -> (* Do we need this? *)
        Expr G (tLam t) (TAll T U)

    | tmApp : forall {G t T U u x},
        Expr G t (TAll T U) ->
        Expr G u T ->
        Cx.isFresh G x -> (* Do we need this? *)
        Expr G (tApp t u) ([u \ x] (U x))

    | TySig : forall {G T s U s' x},
        Expr G T (TSort s) ->
        Expr ((x, T) :: G) (U x) (TSort s') ->
        Cx.isFresh G x -> (* Do we need this? *)
        Expr G (TSig T U) (TSort s')

    | tmPair : forall {G T U s t u x},
        Expr G (TSig T U) (TSort s) ->
        Expr G t T ->
        Expr G u ([t \ x] (U x)) ->
        Cx.isFresh G x ->
        Expr G (tPair t u) (TSig T U)

    | tmFst : forall {G t T U},
        Expr G t (TSig T U) ->
        Expr G (tFst t) T

    | tmSnd : forall {G t T U x},
        Expr G t (TSig T U) ->
        Cx.isFresh G x ->
        Expr G (tSnd t) ([tFst t \ x] (U x))

    | tmConv : forall {G e T U s},
        Expr G e T ->
        Eq T U ->
        Expr G U (TSort s) ->
        Expr G e U.

  Theorem Expr_Cx : forall {G e T}, Expr G e T -> Cx G.
  Proof.
  Admitted.

  Corollary eq_fresh : 
    forall G D : cx, Cx.eq G D -> 
    forall x, Cx.isFresh G x -> 
    Cx.isFresh D x.
  Admitted.

  Corollary eq_cons : 
    forall G D : cx, Cx.eq G D ->
    forall x, Cx.isFresh G x -> 
    forall T, Cx.eq ((x, T) :: G) ((x, T) :: D).
  Admitted.

  Hint Resolve eq_fresh eq_cons : core.

  Theorem t_ren :
    forall {G e T}, Expr G e T ->
    forall {G'}, Cx G' ->
    Cx.eq G G' -> Expr G' e T.
  Proof.
    induction 1.
    1,2: constructor; eauto. apply H2. auto.
    1,4: econstructor; eauto; apply IHExpr2.
    1,3: econstructor; eauto. 1,2: eapply eq_cons; eauto.
    1: { econstructor; eauto. apply IHExpr2. econstructor; eauto. 
         eapply eq_cons; eauto. }
    all: econstructor; eauto. 
  Qed.

  Hint Resolve Expr_Cx t_ren : core.
  (*
  Fixpoint t_weak 
    {G e T} (eT : Expr G e T)
    {W s} (Ws : Expr G W (TSort s))
    : exists x, Expr ((x, W) :: G) e T.
  Proof.
    assert (forall x, Cx.fresh G x -> Cx (G ;; (x, W))). 
    econstructor; eassumption.
    destruct eT.
    - econstructor. constructor. apply H. exact (proj2_sig (unsatur G)).
    - admit.
    - econstructor. econstructor. 
   *)  

  Theorem t_weak :
    forall {G e T}, Expr G e T ->
    forall {x W}, Cx ((x, W) :: G) ->
    Expr ((x, W) :: G) e T.
  Proof.
    induction 1.
    - constructor. auto.
    - constructor. auto. constructor. auto. admit.
    - inversion 1; subst. eapply TyAll. 
      2: apply @t_ren with (G := (x0, W) :: (x, T) :: G). 2: apply IHExpr2.
      2,3: econstructor. 1,4: apply IHExpr1; eauto. 
      admit (* TODO: Change to fixpoint? *). admit. admit. admit. admit.
    - admit.
    - econstructor. apply IHExpr1; auto. apply IHExpr2; auto. admit.
    - admit.
    - econstructor. apply IHExpr1; auto. apply IHExpr2; auto. 
      apply IHExpr3; auto. admit.
    - econstructor. apply IHExpr; auto.
    - econstructor. apply IHExpr; eauto. admit.
    - econstructor; eauto.
  Admitted.
    



