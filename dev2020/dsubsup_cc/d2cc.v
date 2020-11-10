Require Import Arith.EqNat.
Require Import Lists.List.
Require Import Init.Specif.
Import ListNotations.
Import Notations.

Module Lang.

  Inductive var : Set :=
  | varF : nat -> var
  | varB : nat -> var.

  Definition cx (ty : Set) : Set := list ty.

  Fixpoint indexr {ty : Set} (G : cx ty) (n : nat) : option ty :=
    match G with
    | [] => None
    | T :: G' => if (beq_nat n (length G')) then Some T else indexr G' n
    end.

  Module D.

    Inductive ty : Set :=
    | TBot : ty
    | TTop : ty
    | TTyp : ty -> ty -> ty
    | TSel : var -> ty
    | TPi  : ty -> ty -> ty.

    Inductive tm : Set :=
    | tVar : var -> tm
    | tLam : ty -> tm -> tm
    | tApp : tm -> tm -> tm
    | tTyp : ty -> tm.

    Coercion tVar : var >-> tm.

    Fixpoint openTyWith_aux (l : nat) (T : ty) (x : var) : ty :=
      match T with
      | TSel (varB y) => if beq_nat y l then TSel x else T
      | TTyp T1 T2 => TTyp (openTyWith_aux l T1 x) (openTyWith_aux l T2 x)
      | TPi T1 T2 => TPi (openTyWith_aux l T1 x) (openTyWith_aux (S l) T2 x)
      | _ => T
      end.

    Definition openTyWith : ty -> var -> ty := openTyWith_aux 0.

    Definition cx : Set := cx ty.

    Definition openTy (G : cx) (T : ty) : ty := openTyWith T (varF (length G)).

    Fixpoint openTm_aux (l : nat) (g : nat) (e : tm) : tm :=
      match e with
      | tVar (varB x) => if beq_nat x l then tVar (varF g) else e
      | tVar _ => e
      | tLam T e' => tLam (openTyWith_aux l T (varF g)) (openTm_aux (S l) g e')
      | tApp e1 e2 => tApp (openTm_aux l g e1) (openTm_aux l g e2)
      | tTyp T => tTyp (openTyWith_aux l T (varF g))
      end.

    Definition openTm (G : cx) (e : tm) : tm := openTm_aux 0 (length G) e.

    Inductive wf_ty : cx -> ty -> Set :=
    | wf_bot : forall {G},
        wf_ty G TBot

    | wf_top : forall {G},
        wf_ty G TTop

    | wf_typ : forall {G T1 T2},
        wf_ty G T1 ->
        wf_ty G T2 ->
        wf_ty G (TTyp T1 T2)

    (* Note that x has any type below. Restricting x : S ... T causes sel to be
       parametric in S and T. *)
    | wf_sel : forall {G x T},
        has_type G (tVar x) T ->
        wf_ty G (TSel x)

    | wf_pi : forall {G T1 T2},
        wf_ty G T1 ->
        wf_ty (T1 :: G) (openTy G T2) ->
        wf_ty G (TPi T1 T2)

    with has_type : cx -> tm -> ty -> Set :=
    | t_var : forall {G T1 x},
        wf_ty G T1 ->
        indexr G x = Some T1 ->
        has_type G (varF x) T1 (* Typing rule for varB? Not needed since we open T2?*)

    | t_lam : forall {G T1 T2 e},
        wf_ty G T1 ->
        has_type (T1 :: G) (openTm G e) (openTy G T2) ->
        has_type G (tLam T1 e) (TPi T1 T2)

    | t_app : forall {G T1 T2 e e'},
        has_type G e (TPi T1 T2) ->
        has_type G e' T1 ->
        openTy G T2 = T2 -> (* If opening T2 does not change T2 i.e. T2 is independent of e' *)
        has_type G (tApp e e') T2

    | t_dapp : forall {G T1 T2 e x},
        has_type G e (TPi T1 T2) ->
        has_type G (tVar x) T1 ->
        has_type G (tApp e (tVar x)) (openTyWith T2 x)

    | t_typ : forall {G T},
        wf_ty G T ->
        has_type G (tTyp T) (TTyp T T)

    | t_sub : forall {G T1 T2 e},
        has_type G e T1 ->
        subtype G T1 T2 ->
        has_type G e T2

    with subtype : cx -> ty -> ty -> Set :=
    | s_bot : forall {G T},
        wf_ty G T ->
        subtype G TBot T

    | s_top : forall {G T},
        wf_ty G T ->
        subtype G T TTop

    | s_typ : forall {G T1 T2 T1' T2'},
        subtype G T1' T1 ->
        subtype G T2 T2' ->
        subtype G (TTyp T1 T2) (TTyp T1' T2')

    | s_sel1 : forall {G T1 T2 x},
        has_type G (tVar x) (TTyp T1 T2) ->
        subtype G T1 (TSel x)

    | s_sel2 : forall {G T1 T2 x},
        has_type G (tVar x) (TTyp T1 T2) ->
        subtype G (TSel x) T2

    | s_pi : forall {G T1 T2 T1' T2'},
        subtype G T1' T1 ->
        subtype (T1' :: G) (openTy G T2) (openTy G T2') ->
        subtype G (TPi T1 T2) (TPi T1' T2')

    | s_refl : forall {G T},
        wf_ty G T ->
        subtype G T T

    | s_trans : forall {G T1 T2 T3},
        subtype G T1 T2 ->
        subtype G T2 T3 ->
        subtype G T1 T3.

    Inductive wf_cx : cx -> Set :=
    | wf_nil : wf_cx []

    | wf_cons : forall {G T},
        wf_ty G T ->
        wf_cx G ->
       (*---------------*)
        wf_cx (T :: G).

    Lemma strengthen_by_opening : forall {G T0 T T' x},
        wf_ty (T0 :: G) (openTy G T) ->
        has_type G (tVar x) T' ->
        wf_ty G (openTyWith T x).
    Admitted.

    Lemma strengthen_by_independence : forall {G T T'},
        wf_ty (T' :: G) (openTy G T) ->
        openTy G T = T ->
        wf_ty G T.
    Proof.
      intros. Admitted.

    Corollary inversion_wf_pi_2 : forall {G T T'},
        wf_ty G (TPi T T') ->
        wf_ty (T :: G) (openTy G T').
    Proof. intros. inversion H. assumption. Qed.

    Lemma rename_by_subtyping {G T T1 T2}
                             (wfT : wf_ty (T1 :: G) T)
                             (ST : subtype G T1 T2) : wf_ty (T2 :: G) T.
    Proof. Admitted.

    (* All well typed terms have well formed types. *)
    Fixpoint has_type_implies_wf {G T e} (eT : has_type G e T) : wf_ty G T
    with subtype_implies_wf {G T T'} (ST : subtype G T T') : wf_ty G T * wf_ty G T'.
      -  (* has_type G e T -> wf_ty G T *)
        induction eT.
        + (* t_var *) assumption.
        + (* t_lam *) constructor. assumption. eauto.
        + (* t_app *) eapply strengthen_by_independence. apply inversion_wf_pi_2.
          eauto. auto.
        + (* t_dapp*) eapply strengthen_by_opening. apply inversion_wf_pi_2.
          eauto. eauto.
        + (* t_typ *) constructor. assumption. assumption.
        + (* t_sub *) exact (snd (subtype_implies_wf _ _ _ s)).
      - (* subtype G T T' -> wf_ty G T * wf_ty G T' *)
        induction ST.
        + (* s_bot *) apply pair. constructor. assumption.
        + (* s_top *) apply pair. assumption. constructor.
        + (* s_typ *) apply pair; constructor; intuition; intuition.
        + (* s_sel1 *) apply pair.
          * pose (has_type_implies_wf _ _ _ h) as H. inversion H. assumption.
          * econstructor. exact h.
        + (* s_sel2 *) apply pair.
          * econstructor. exact h.
          * pose (has_type_implies_wf _ _ _ h) as H. inversion H. assumption.
        + (* s_pi *) apply pair.
          * constructor. intuition. eapply rename_by_subtyping. exact (fst IHST2).
            assumption.
          * constructor. intuition. intuition.
        + (* s_refl *) intuition.
        + (* s_trans *) intuition.
          Qed.

  End D.

  Module CC.

    Inductive sort : Set := prop | type.

    Inductive expr : Set :=
    | TSort : sort -> expr
    | TAll : expr -> expr -> expr
    | TSig : expr -> expr -> expr
    | tLam : expr -> expr -> expr
    | tApp : expr -> expr -> expr
    | tVar : var -> expr
    | tPair : expr -> expr -> expr
    | tFst : expr -> expr
    | tSnd : expr -> expr.

    Coercion tVar : var >-> expr.

    Definition cx : Set := cx expr.

    Fixpoint openWith_aux (l : nat) (e : expr) (e' : expr) : expr :=
      match e with
      | tVar (varB x) => if beq_nat l x then e' else e
      | TAll A B => TAll (openWith_aux l A e') (openWith_aux (S l) B e')
      | TSig A B => TSig (openWith_aux l A e') (openWith_aux (S l) B e')
      | tLam A e => tLam (openWith_aux l A e') (openWith_aux (S l) e e')
      | tApp e1 e2 => tApp (openWith_aux l e1 e') (openWith_aux l e2 e')
      | tPair e1 e2 => tPair (openWith_aux l e1 e') (openWith_aux l e2 e')
      | tFst e1 => tFst (openWith_aux l e1 e')
      | tSnd e1 => tSnd (openWith_aux l e1 e')
      | _ => e
      end.

    Definition openWith : expr -> expr -> expr := openWith_aux 0.
    Definition open (G : cx) (e : expr) : expr :=
      openWith e (tVar (varF (length G))).

    Fixpoint close_aux (l : nat) (n : nat) (e : expr) : expr :=
      match e with
      | tVar (varF x) => if beq_nat x n then varB l else e
      | TAll A B => TAll (close_aux l n A) (close_aux (S l) n B)
      | TSig A B => TSig (close_aux l n A) (close_aux (S l) n B)
      | tLam A e => tLam (close_aux l n A) (close_aux (S l) n e)
      | tApp e1 e2 => tApp (close_aux l n e1) (close_aux l n e2)
      | tPair e1 e2 => tPair (close_aux l n e1) (close_aux l n e2)
      | tFst e1 => tFst (close_aux l n e1)
      | tSnd e1 => tSnd (close_aux l n e1)
      | _ => e
      end.

    Definition close' : nat -> expr -> expr := close_aux 0.
    Definition close (G : cx) : expr -> expr := close' (length G).

    Inductive has_type : cx -> expr -> expr -> Set :=
    | t_ax : forall {G},
        has_type G (TSort prop) (TSort type)

    | t_var : forall {G A x},
        indexr G x = Some A ->
        has_type G (varF x) A (* Typing rule for varB? Not needed since we open T2*)

    | t_all : forall {G A B s s'},
        has_type G A (TSort s) ->
        has_type (A :: G) (open G B) (TSort s') ->
        has_type G (TAll A B) (TSort s')

    | t_sig : forall {G A B s s'},
        has_type G A (TSort s) ->
        has_type (A :: G) (open G B) (TSort s') ->
        has_type G (TSig A B) (TSort s')

    | t_lam : forall {G A B s e},
        has_type G A (TSort s) ->
        has_type (A :: G) (open G e) (open G B) ->
        has_type G (tLam A e) (TAll A B)

    | t_app : forall {G A B e e'},
        has_type G e (TAll A B) ->
        has_type G e' A ->
        has_type G (tApp e e') (openWith B e')

    | t_pair : forall {G A B e e'},
        has_type G e A ->
        has_type G e' (openWith B e) ->
        has_type G (tPair e e') (TSig A B)

    | t_fst : forall {G A B e},
        has_type G e (TSig A B) ->
        has_type G (tFst e) A

    | t_snd : forall {G A B e},
        has_type G e (TSig A B) ->
        has_type G (tSnd e) (openWith B (tFst e))

    | t_conv : forall {G A B s e},
        has_type G e A ->
        eq_cc G A B (TSort s) ->
        has_type G e B

    with eq_cc : cx -> expr -> expr -> expr -> Set :=
    | eq_beta : forall {G A B e e'},
        has_type (A :: G) e (open G B) ->
        has_type G e' A ->
        eq_cc G (tApp (tLam A e) e') (openWith e e') (openWith B e')

    | eq_eta : forall {G A B e},
        has_type G e (TAll A B) ->
        eq_cc G (tLam A (tApp e (varB 0))) e (TAll A B)

    | eq_all : forall {G A B A' B' sA sB},
        eq_cc G A A' (TSort sA) ->
        eq_cc (A :: G) (open G B) (open G B') (TSort sB) ->
        eq_cc G (TAll A B) (TAll A' B') (TSort sB)

    | eq_sig : forall {G A B A' B' sA sB},
        eq_cc G A A' (TSort sA) ->
        eq_cc (A :: G) (open G B) (open G B') (TSort sB) ->
        eq_cc G (TSig A B) (TSig A' B') (TSort sB)

    | eq_fst : forall {G A B s e e'},
        has_type G (TSig A B) (TSort s) ->
        has_type G e A ->
        has_type G e' (openWith B e) ->
        eq_cc G (tFst (tPair e e')) e A

    | eq_snd : forall {G A B s e e'},
        has_type G (TSig A B) (TSort s) ->
        has_type G e A ->
        has_type G e' (openWith B e) ->
        eq_cc G (tSnd (tPair e e')) e' (openWith B e)

    | eq_pair : forall {G A B e},
        has_type G e (TSig A B) ->
        eq_cc G (tPair (tFst e) (tSnd e)) e (TSig A B)

    | eq_lam : forall {G A A' B e e' s},
        eq_cc G A A' (TSort s) ->
        eq_cc (A :: G) (open G e) (open G e') (open G B) ->
        eq_cc G (tLam A e) (tLam A' e') (TAll A B)

    | eq_app : forall {G A B e1 e2 e1' e2'},
        eq_cc G e1 e1' (TAll A B) ->
        eq_cc G e2 e2' A ->
        eq_cc G (tApp e1 e2) (tApp e1' e2') (openWith B e2)

    | eq_refl : forall {G e A},
        has_type G e A ->
        eq_cc G e e A

    | eq_sym : forall {G A e e'},
        eq_cc G e e' A ->
        eq_cc G e' e A

    | eq_trans : forall {G A e1 e2 e3},
        eq_cc G e1 e2 A ->
        eq_cc G e2 e3 A ->
        eq_cc G e1 e3 A.

    Inductive wf_cx : cx -> Set :=
    | wf_nil : wf_cx []
    | wf_cons : forall {G A s},
        has_type G A (TSort s) ->
        wf_cx G ->
        wf_cx (A :: G).

    Definition TBot : expr := TAll (TSort prop) (varB 0).

    Definition TTop : expr := TSig (TSort prop) (varB 0).

    Definition TTyp (A B : expr) : expr :=
      TSig (TSort prop) (TSig (TAll A (varB 1)) (TAll (varB 1) B)).

    Definition TSel (e : expr) : expr := tFst e.
    Definition tSel1 (e : expr) : expr := tFst (tSnd e).
    Definition tSel2 (e : expr) : expr := tSnd (tSnd e).

    Definition tId A : expr := tLam A (tVar (varB 0)).
    Definition tTyp (A : expr) : expr := tPair A (tPair (tId A) (tId A)).
    Definition tComp (e e' A : expr) := tLam A (tApp e (tApp e' (varB 0))).

  Definition bind {A B : Type} (a : option A) (f : A -> option B) : option B :=
    match a with
    | None => None
    | Some a' => f a'
    end.

  Fixpoint translateTy {G T} (wfT : D.wf_ty G T) (k : nat) : option CC.expr :=
    match k with
    | 0 => None
    | S k' =>
      match wfT in D.wf_ty G T with
      | D.wf_bot           => Some CC.TBot
      | D.wf_top           => Some CC.TTop

      | D.wf_typ wfT1 wfT2 =>
        bind (translateTy wfT1 k') (fun A =>
        bind (translateTy wfT2 k') (fun B =>
        Some (CC.TTyp A B)))

      | D.wf_sel xT =>
        bind (translateTm xT k') (fun A => Some (CC.TSel A))

      | D.wf_pi wfT1 wfT2 =>
        bind (translateTy wfT1 k') (fun A =>
        bind (translateTy wfT2 k') (fun B =>
        Some (CC.TAll A B)))
      end
    end
  with
  translateTm {G e T} (eT : D.has_type G e T) (k : nat) : option CC.expr :=
    match k with
    | 0 => None
    | S k' =>
      match eT in D.has_type G e T with
      | @D.t_var _ _ x _ _ => Some (CC.tVar (varF x))

      | D.t_lam wfT eT' =>
        bind (translateTy wfT k') (fun A =>
        bind (translateTm eT' k') (fun e' =>
        Some (CC.tLam A (close' (length G) e'))))

      | D.t_app eT eT' _ | D.t_dapp eT eT' =>
        bind (translateTm eT k') (fun t =>
        bind (translateTm eT' k') (fun t' =>
        Some (CC.tApp t t')))

      | D.t_typ wfT =>
        bind (translateTy wfT k') (fun A => Some (CC.TTyp A A))

      | D.t_sub eT ST =>
        bind (translateSub ST k') (fun f =>
        bind (translateTm eT k') (fun t =>
        Some (CC.tApp f t)))
      end
    end
  with
  translateSub {G T1 T2} (ST : D.subtype G T1 T2) (k : nat) : option CC.expr :=
    match k with
    | 0 => None
    | S k' =>
      let wfTP := D.subtype_implies_wf ST in
      bind (translateTy (fst wfTP) k') (fun A1 =>
      bind (translateTy (snd wfTP) k') (fun A2 =>
      bind
         (match ST with
          | D.s_bot _ => Some (CC.tApp (varB 0) A2)
          | D.s_top _ => Some (CC.tPair A1 A1)

          | D.s_typ ST1 ST2 =>
            bind (translateTy (fst (D.subtype_implies_wf ST1)) k') (fun B =>
            bind (translateSub ST1 k') (fun B2A =>
            bind (translateSub ST2 k') (fun A'2B' =>
            Some
            (CC.tPair (CC.TSel (varB 0))
              (CC.tPair (CC.tComp (CC.tSel1 (varB 0)) B2A B)
                        (CC.tComp A'2B' (CC.tSel2 (varB 0)) (CC.TSel (varB 0))))))))

          | D.s_sel1 xT =>
            bind (translateTm xT k') (fun x =>
            Some (CC.tApp (CC.tSel1 x) (varB 0)))

          | D.s_sel2 xT =>
            bind (translateTm xT k') (fun x =>
            Some (CC.tApp (CC.tSel2 x) (varB 0)))

          | D.s_pi ST1 ST2 =>
            bind (translateSub ST1 k') (fun B2A =>
            bind (translateSub ST2 k') (fun A'2B' =>
            Some (CC.tApp A'2B' (CC.tApp (varB 0) (CC.tApp B2A (varB 1))))))

          | D.s_refl _ => Some (tVar (varB 0))

          | D.s_trans ST12 ST23 =>
            bind (translateSub ST12 k') (fun A2B =>
            bind (translateSub ST23 k') (fun B2C =>
            Some (CC.tApp B2C (CC.tApp A2B (varB 0)))))
          end) (fun e => Some (CC.tLam A1 e))))
    end.
