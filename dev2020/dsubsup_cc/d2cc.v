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
    | tyBot : ty
    | tyTop : ty
    | tyTyp : ty -> ty -> ty
    | tySel : var -> ty
    | tyPi  : ty -> ty -> ty.

    Inductive tm : Set :=
    | tmVar : var -> tm
    | tmLam : ty -> tm -> tm
    | tmApp : tm -> tm -> tm
    | tmTyp : ty -> tm.
(*
    Inductive closedTy : nat -> nat -> ty -> Prop :=
    | cl_Bot : forall b f, closedTy b f tyBot
    | cl_Top : forall b f, closedTy b f tyTop

    | cl_Typ : forall b f T1 T2,
        closedTy b f T1 ->
        closedTy b f T2 ->
        closedTy b f (tyTyp T1 T2)

    | cl_SelB : forall b f x,
        x < b ->
        closedTy b f (tySel (varB x))

    | cl_SelF : forall b f x,
        x < f ->
        closedTy b f (tySel (varF x))

    | cl_Pi : forall b f T1 T2,
        closedTy b f T1 ->
        closedTy (S b) f T2 -> (* Is this really correct, given our type formation rule introduces a new free var? *)
        closedTy b f (tyPi T1 T2).
*)
    Fixpoint appTy_aux (l : nat) (T : ty) (x : var) : ty :=
      match T with
      | tySel (varB y) => if beq_nat y l then tySel x else T
      | tyTyp T1 T2 => tyTyp (appTy_aux l T1 x) (appTy_aux l T2 x)
      | tyPi T1 T2 => tyPi (appTy_aux l T1 x) (appTy_aux (S l) T2 x)
                           (* Call to T2 uses S l, since formation rule for pi types adds a
                              free variable to the codomain type. *)
      | _ => T
      end.

    Definition appTy : ty -> var -> ty := appTy_aux 0.
    Definition openTy (T : ty) : ty := appTy T (varF 0).

    Definition cx : Set := cx ty.

    Inductive wf_cx : cx -> Set :=
    | wf_nil : wf_cx []

    | wf_cons : forall {G T},
        wf_cx G ->
        wf_ty G T ->
       (*---------------*)
        wf_cx (T :: G)

    with wf_ty : cx -> ty -> Set :=
    | wf_bot : forall {G},
        wf_ty G tyBot

    | wf_top : forall {G},
        wf_ty G tyTop

    | wf_typ : forall {G T1 T2},
        wf_ty G T1 ->
        wf_ty G T2 ->
        wf_ty G (tyTyp T1 T2)

    (* Note that x has any type below. Restricting x : S ... T causes sel to be
       parametric in S and T. *)
    | wf_sel : forall {G x T},
        has_type G (tmVar x) T ->
        wf_ty G (tySel x)

    | wf_pi : forall {G T1 T2},
        wf_ty G T1 ->
        wf_ty (T1 :: G) T2 ->
        wf_ty G (tyPi T1 T2)

    with has_type : cx -> tm -> ty -> Set :=
    | t_var : forall {x G T1},
        indexr G x = Some T1 ->
        has_type G (tmVar (varF x)) T1 (* Typing rule for varB? Not needed since we open T2?*)

    | t_lam : forall {G T1 T2 e},
        wf_ty G T1 ->
        has_type (T1 :: G) e T2 ->
        has_type G (tmLam T1 e) (tyPi T1 T2)

    | t_app : forall {G T1 T2 e e'},
        has_type G e (tyPi T1 T2) ->
        has_type G e' T1 ->
        openTy T2 = T2 -> (* If opening T2 does not change T2 i.e. T2 is independent of e' *)
        has_type G (tmApp e e') T2

    | t_dapp : forall {G T1 T2 e x},
        has_type G e (tyPi T1 T2) ->
        has_type G (tmVar x) T1 ->
        has_type G (tmApp e (tmVar x)) (appTy T2 x)

    | t_typ : forall {G T},
        wf_ty G T ->
        has_type G (tmTyp T) (tyTyp T T)

    | t_sub : forall {G e T1 T2},
        has_type G e T1 ->
        subtype G T1 T2 ->
        has_type G e T2

    with subtype : cx -> ty -> ty -> Set :=
    | s_bot : forall {G T}, subtype G tyBot T
    | s_top : forall {G T}, subtype G T tyTop

    | s_typ : forall {G T1 T2 T1' T2'},
        subtype G T1' T1 ->
        subtype G T2 T2' ->
        subtype G (tyTyp T1 T2) (tyTyp T1' T2')

    | s_sel1 : forall {G x T1 T2},
        has_type G (tmVar x) (tyTyp T1 T2) ->
        subtype G T1 (tySel x)

    | s_sel2 : forall {G x T1 T2},
        has_type G (tmVar x) (tyTyp T1 T2) ->
        subtype G (tySel x) T2

    | s_selx : forall {G x}, subtype G (tySel x) (tySel x)

    | s_pi : forall {G T1 T2 T1' T2'},
        subtype G T1' T1 ->
        subtype (T1' :: G) T2 T2' ->
        subtype G (tyPi T1 T2) (tyPi T1' T2').

  End D.

  Module CC.

    Inductive sort : Set := prop | type.

    Inductive expr : Set :=
    | eSort : sort -> expr
    | eVar : var -> expr
    | eLam : expr -> expr -> expr
    | eAll : expr -> expr -> expr
    | eApp : expr -> expr -> expr.

    Definition cx : Set := cx expr.

    Fixpoint substi_aux (l : nat) (e : expr) (e' : expr) : expr :=
      match e with
      | eVar (varB x) => if beq_nat l x then e' else e
      | eLam A e => eLam (substi_aux l A e') (substi_aux (S l) e e')
      | eAll A B => eAll (substi_aux l A e') (substi_aux (S l) B e')
      | eApp e1 e2 => eApp (substi_aux l e1 e') (substi_aux l e2 e')
      | _ => e
      end.

    Definition substi : expr -> expr -> expr := substi_aux 0.

    Inductive wf_cx : cx -> Set :=
    | wf_nil : wf_cx []
    | wf_cons : forall {G A s},
        wf_cx G ->
        has_type G A (eSort s) ->
        wf_cx (A :: G)

    with has_type : cx -> expr -> expr -> Set :=
    | t_ax : forall {G},
        has_type G (eSort prop) (eSort type)

    | t_var : forall {G x A},
        wf_cx G ->
        indexr G x = Some A ->
        has_type G (eVar (varF x)) A (* Typing rule for varB? Not needed since we open T2*)

    | t_lam : forall {G e A B s},
        has_type G A (eSort s) ->
        has_type (A :: G) e B ->
        has_type G (eLam A e) (eAll A B)

    | t_all : forall {G A B s s'},
        has_type G A (eSort s) ->
        has_type G B (eSort s') ->
        has_type G (eAll A B) (eSort s')

    | t_app : forall {G e e' A B},
        has_type G e (eAll A B) ->
        has_type G e' A ->
        has_type G (eApp e e') (substi B e').

    Definition eImplies (A B : expr) : expr := eAll A B.

    Definition eExists (A B : expr) : expr :=
      eAll (eSort prop) (eImplies (eAll A (eImplies B (eVar (varB 2)))) (eVar (varB 1))).

    Definition eAnd (A B : expr) : expr :=
      eAll (eSort prop) (eImplies (eImplies A (eImplies B (eVar (varB 2)))) (eVar (varB 1))).

(*
The below attempt failed. We want a translateTy which translates G |- T type to [G] |- S : k.
But Coq does not allow us to use translateCx in the type of translateTy, so we cannot
specify environment [G]'s relation to G. However, abstracting over [G] means that we don't
get enough information to complete the D.wf_cons branch of translateCx.
*)
  Fail Fixpoint translateCx {G : D.cx} (wfG : D.wf_cx G) : sigT CC.wf_cx :=
    match wfG with
    | @D.wf_nil => existT CC.wf_cx [] CC.wf_nil
    | @D.wf_cons _ T wfG wfT =>
      match translateCx wfG, translateTy wfT with
      | existT _ G' wfG', existT _ _ (existT _ A (existT _ _ wfA)) =>
        existT _ (A :: G') (CC.wf_cons wfG' wfA)
      end
    end

  with translateTy {G : D.cx} {T : D.ty} (wfT : D.wf_ty G T) :
         sigT (fun s =>
                 sigT (fun A => has_type (translateCx (D.from_wfTy wfT) A (eSort s)))).

  Fail Fixpoint translateCx {G : D.cx} (wfG : D.wf_cx G) : sigT CC.wf_cx :=
    match wfG with
    | @D.wf_nil => existT CC.wf_cx [] CC.wf_nil
    | @D.wf_cons _ T wfG wfT =>
      match translateCx wfG, translateTy wfT with
      | existT _ G' wfG', existT _ _ (existT _ A (existT _ _ wfA)) =>
        existT _ (A :: G') (CC.wf_cons wfG' wfA)
      end
    end

  with translateTy {G : D.cx} {T : D.ty} (wfT : D.wf_ty G T) :
         sigT (fun G' => sigT (fun A => sigT (fun s => CC.has_type G' A (CC.eSort s)))).

  (* What if we remove the dependency of typechecking on context well-formedness? Then, our
     translation function for types requires a proof that the type we're trying to translate
     is well-formed. Maybe this helps untangle the type signatures? *)
  Fail Fixpoint translateCx {G : D.cx} (wfG : D.wf_cx G) : sigT CC.wf_cx :=
    match wfG with
    | D.wf_nil => existT _ [] CC.wf_nil
    | D.wf_cons _ _ => existT _ [] CC.wf_nil
    end

  with translateTy {G : D.cx} (wfG : D.wf_cx G) {T : D.ty} (wfT : D.wf_ty G T) :
         sigT (fun A => sigT (fun s => translateCx)).

  (* Of course that didn't work, I should've thought it through more. But I guess it's not
     bad to find out that I was wrong by quickly coding it up, since this was relatively
     small. *)

  (* What if I just map (G, wfG, T, wfT) to (G', wfG', T', wfT') and then prove that my
     mapping is the correct one? *)

  Fail Fixpoint translateTy {G : D.cx} (wfG : D.wf_cx G) {T : D.ty} (wfT : D.wf_ty G T) :
    sigT (fun G' => sigT (fun A => sigT (fun s => CC.has_type G' A (eSort s)))) :=
    let G' := match wfG with
             | D.wf_nil => []
             | D.wf_cons wfG' wfT' => projT1 (translateTy wfG' wfT')
             end
    in let A := match wfT with
               | D.wf_bot => eAll (eSort prop) (varB 0)
               | D.wf_top => eExists (eSort prop) (varB 0)
               | @D.wf_typ _ T1 T2 wfT1 wfT2 =>
                 eExists (eSort prop) (eAnd (eImplies T1 (eVar (varB 0)))
                                            (eImplies (eVar (varB 0)) T2))
               end in 0.
