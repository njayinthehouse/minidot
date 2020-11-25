Require Import Arith.EqNat.
Require Import Lists.List.
Require Import Init.Specif.
Require Import Init.Nat.
Import ListNotations.
Import Notations.
Require Import Program.Equality.

Module Lang.

  Definition var : Set := nat.

  Definition cx (ty : Set) : Set := list ty.

  Fixpoint get {ty} (G : cx ty) (x : var) : option ty :=
    match G, x with
    | [], _ => None
    | T :: G, 0 => Some T
    | T :: G, S x' => get G x'
    end.

  Definition closed {ty} (G : cx ty) (x : var) : Set := sigT (fun T => get G x = Some T).
  Definition closed' {ty} (G : cx ty) (x : var) : Set := x < (length G).

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

    Definition cx : Set := cx ty.

(*
    Fixpoint closedTy (G : cx) (T : ty) : Prop :=
      match T with
      | TSel x => closed G x
      | TTyp T1 T2 => closedTy G T1 /\ closedTy G T2
      | TPi T1 T2 => closedTy G T1 /\ closedTy (T1 :: G) T2
      | _ => True
      end.
*)
    Inductive closedTy (G : cx) : ty -> Set :=
    | cl_bot : closedTy G TBot
    | cl_top : closedTy G TTop

    | cl_typ : forall {T1 T2},
        closedTy G T1 ->
        closedTy G T2 ->
        closedTy G (TTyp T1 T2)

    | cl_sel : forall {x},
        closed G x ->
        closedTy G (TSel x)

    | cl_pi : forall {T1 T2},
        closedTy G T1 ->
        closedTy (T1 :: G) T2 ->
        closedTy G (TPi T1 T2).

    Definition shift_aux (f : nat -> nat -> nat) (d c : nat) (x : var) : var := if ltb x c then x else f x d.
    Definition shiftU := shift_aux add.
    Definition shiftD := shift_aux sub.

    Fixpoint shiftTy_aux (shift : nat -> nat -> var -> var) (d c : nat) (T : ty) : ty :=
      match T with
      | TSel x => TSel (shift d c x)
      | TTyp T1 T2 => TTyp (shiftTy_aux shift d c T1) (shiftTy_aux shift d c T2)
      | TPi T1 T2 => TPi (shiftTy_aux shift d c T1) (shiftTy_aux shift d (S c) T2)
      | _ => T
      end.
    Definition shiftTyU := shiftTy_aux shiftU.
    Definition shiftTyD := shiftTy_aux shiftD.

    Fixpoint substTy (T : ty) (l : nat) (x : var) : ty :=
      match T with
      | TSel x' => if beq_nat x' l then TSel x else TSel x'
      | TTyp T1 T2 => TTyp (substTy T1 l x) (substTy T2 l x)
      | TPi T1 T2 => TPi (substTy T1 l x) (substTy T2 (S l) (shiftU 1 0 x))
      | _ => T
      end.
    Definition appTy (T : ty) (x : var) : ty := shiftTyD 1 0 (substTy T 0 (shiftU 1 0 x)).

    Inductive wf_ty (G : cx) : ty -> Set :=
    | wf_bot : wf_ty G TBot

    | wf_top : wf_ty G TTop

    | wf_typ : forall {T1 T2},
        wf_ty G T1 ->
        wf_ty G T2 ->
        wf_ty G (TTyp T1 T2)

    (* Note that x has any type below. Restricting x : S ... T causes sel to be
       parametric in S and T. *)
    | wf_sel : forall {x},
        closed G x ->
        wf_ty G (TSel x)

    | wf_pi : forall {T1 T2},
        wf_ty G T1 ->
        wf_ty (T1 :: G) T2 ->
        wf_ty G (TPi T1 T2)

    with has_type (G : cx) : tm -> ty -> Set :=
    | t_var : forall {T1 x},
        wf_ty G T1 ->
        get G x = Some T1 ->
        has_type G x T1 (* Typing rule for varB? Not needed since we open T2?*)

    | t_lam : forall {T1 T2 e},
        wf_ty G T1 ->
        has_type (T1 :: G) e T2 ->
        has_type G (tLam T1 e) (TPi T1 T2)

    | t_app : forall {T1 T2 e e'},
        has_type G e (TPi T1 T2) ->
        has_type G e' T1 ->
        closedTy G T2 ->
        has_type G (tApp e e') T2

    | t_dapp : forall {T1 T2 e x},
        has_type G e (TPi T1 T2) ->
        has_type G (tVar x) T1 ->
        has_type G (tApp e (tVar x)) (appTy T2 x)

    | t_typ : forall {T},
        wf_ty G T ->
        has_type G (tTyp T) (TTyp T T)

    | t_sub : forall {T1 T2 e},
        has_type G e T1 ->
        subtype G T1 T2 ->
        has_type G e T2

    with subtype (G : cx) : ty -> ty -> Set :=
    | s_bot : forall {T},
        wf_ty G T ->
        subtype G TBot T

    | s_top : forall {T},
        wf_ty G T ->
        subtype G T TTop

    | s_typ : forall {T1 T2 T1' T2'},
        subtype G T1' T1 ->
        subtype G T2 T2' ->
        subtype G (TTyp T1 T2) (TTyp T1' T2')

    | s_sel1 : forall {T1 T2 x},
        has_type G (tVar x) (TTyp T1 T2) ->
        subtype G T1 (TSel x)

    | s_sel2 : forall {T1 T2 x},
        has_type G (tVar x) (TTyp T1 T2) ->
        subtype G (TSel x) T2

    | s_pi : forall {T1 T2 T1' T2'},
        subtype G T1' T1 ->
        subtype (T1' :: G) T2 T2' ->
        wf_ty (T1 :: G) T2 ->
        subtype G (TPi T1 T2) (TPi T1' T2')

    | s_refl : forall {T},
        wf_ty G T ->
        subtype G T T

    | s_trans : forall {T1 T2 T3},
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

    Definition closed_implies_ht {G x} (clx : closed G x) : sigT (fun T => wf_ty G T -> has_type G (tVar x) T).
      eapply existT. constructor. assumption. exact (projT2 clx).
    Defined.

    Fixpoint ht_implies_closed {G T x} (xT : has_type G (tVar x) T) : closed G x.
      inversion xT; subst.
      - eapply existT. eassumption.
      - eapply ht_implies_closed. eassumption.
    Defined.

    Fixpoint strengthening_by_appTy {G T T' x} (wfT : wf_ty (T' :: G) T) (clX : closed G x) : wf_ty G (appTy T x).
      remember (T' :: G) as T'G. induction wfT.
      - constructor.
      - constructor.
      - constructor. apply IHwfT1. assumption. apply IHwfT2. assumption.
        - 

    Fixpoint ht_implies_wf {G T e} (eT : has_type G e T) : wf_ty G T
    with st_implies_wf {G T T'} (ST : subtype G T T') : wf_ty G T * wf_ty G T'.
      (* has_type G e T -> wf_ty G T *)
      - induction eT.
        + (* t_var *) assumption.
        + (* t_lam *) constructor. assumption. eapply ht_implies_wf. eassumption.
        + (* t_app *)
        + (* t_dapp *)
        + constructor. assumption. assumption.
        + eapply st_implies_wf. apply s.
      - induction ST.
        + apply pair. constructor. assumption.
        + apply pair. assumption. constructor.
        + apply pair.
          * constructor. exact (snd IHST1). exact (fst IHST2).
          * constructor. exact (fst IHST1). exact (snd IHST2).
        + apply pair.
          * apply ht_implies_wf in h. inversion h. subst. assumption.
          * constructor. eapply ht_implies_closed. eassumption.
        + apply pair.
          * constructor. eapply ht_implies_closed. eassumption.
          * apply ht_implies_wf in h. inversion h. subst. assumption.
        + apply pair.
          * constructor. exact (snd IHST1). assumption.
          * constructor. exact (fst IHST1). exact (snd IHST2).
        + exact (w, w).
        + apply pair. exact (fst IHST1). exact (snd IHST2).
    Admitted.

(*
    Lemma strengthen_by_opening : forall {G T0 T T' x},
        wf_ty (T0 :: G) (openTy G T) ->
        has_type G (tVar x) T' ->
        wf_ty G (openTyWith T x).
    Proof.
      intros G T0 T. generalize dependent G. generalize dependent T0.
      induction T; intros.
      - constructor.
      - constructor.
      - inversion H. subst. clear H. constructor.
        + eapply IHT1. eassumption. eassumption.
        + eapply IHT2. eassumption. eassumption.
      - inversion H. subst. Abort.

    Lemma strengthen_by_independence : forall {G T T'},
        wf_ty (T' :: G) (openTy G T) ->
        openTy G T = T ->
        wf_ty G T.
    Proof.
      intros. rewrite H0 in H. induction H.
      - constructor.
      - constructor.
      - Abort.

    Example problem : forall {G}, openTy G (TSel (varF (length G))) = TSel (varF (length G)).
    reflexivity. Qed.
*)
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
    (* Write examples *)
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

          | D.s_pi ST1 ST2 _ =>
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

  (* TODO:
     1. Check out well-founded recursion and induction. Chlipala's book
     2. Complete those substitution lemmas
     3. Write the translation using well-founded recursion, or any method which
        makes it total.
     4. Prove that translated expressions are well-typed in CoC. *)
