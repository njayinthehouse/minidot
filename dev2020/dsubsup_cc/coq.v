Set Printing Universes.


Section Types.

  Polymorphic Definition TNat: Type := nat.

  Polymorphic Definition TMem L U: Type :=
    sigT (fun a:Type => prod (L -> a) (a -> U)).

  Polymorphic Definition TSel {L U} (t: TMem L U): Type :=
    projT1 t.

  Polymorphic Definition TTop: Type := sigT (fun a: Type => a).

  Polymorphic Definition TBot: Type := forall x: Type, x.

  Polymorphic Definition TAll (A : Type) (B: A -> Type): Type := forall x:A, (B x).

  Polymorphic Definition TAnd (A: Type) (B: Type): Type := A * B. (* TODO: not sure *)

  (* TODO: TBind, use coinduction? *)

  Check (TAll (TMem TBot TTop) (fun x => TAll (TSel x) (fun _ => (TSel x)))).

End Types.


Section Terms.

  Polymorphic Definition tzro: TNat :=
  0.

  Polymorphic Definition ttyp T: TMem T T :=
  existT (fun a => prod (T -> a) (a -> T)) T (pair (fun (a:T) => a) (fun (a:T) => a)).

  Polymorphic Definition tabs {A: Type} {B: A -> Type} (f: forall x:A, B x): TAll A B := f.

  Polymorphic Definition tapp {A: Type} {B: A -> Type} (f: TAll A B) (x: A): (B x) := f x.

  Check tabs.

  (* TODO: unpack *)

End Terms.


Section Typing.

  (* Intro & elim forms *)
  Lemma tmem_intro: forall L U (x: TMem L U) (y: L), (TSel x).
  Proof.
    intros. destruct x. destruct p. simpl. apply x0. apply y.
  Qed.

  Lemma tmem_elim: forall L U (x: TMem L U) (y: TSel x), U.
  Proof.
    intros. destruct x. destruct p. simpl. apply u. apply y.
  Qed.

End Typing.

(* Verify impredicativity via universe polymorphism *)
Definition nest T: TMem (TMem T T) (TMem T T) :=
  ttyp (TMem T T).

Check nest.

Definition unnest T: TSel (nest T) :=
ttyp T.

Check unnest.

Section Subtyping.

  (* Subtyping could be translated as coercions *)

  Polymorphic Definition sub_any {A: Type} (t: A): TTop := existT (fun a: Type => a) A t.
  Polymorphic Definition sub_bot {A: Type} (t: TBot): A := t A.

  Polymorphic Definition tmem_any {L U: Type} (t: TMem L U): TTop := sub_any t.
  Polymorphic Definition bot_tmem {L U: Type} (t: TBot): (TMem L U) := sub_bot t.

End Subtyping.

Require Export Arith.EqNat.
Require Export Arith.Le.
Require Import Coq.Program.Equality.
Require Import Omega.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import languages_o2.

Section D_meta.
Import D.

Lemma ty_wf_weaken: forall Gamma T U, ty_wf Gamma T -> ctx_wf (U :: Gamma) -> ty_wf (U :: Gamma) T.
Proof.
  Admitted.

Lemma wf_lookup: forall Gamma x T, ctx_wf Gamma -> indexr x Gamma = Some T -> ty_wf Gamma T.
Proof.
  intros.
  induction H; inversion H0.
  inversion H0.
  destruct (beq_nat x (length Gamma)).
  - injection H2. intros. subst.
    apply ty_wf_weaken. assumption. constructor. assumption. assumption.
  - apply IHctx_wf in H2. apply ty_wf_weaken. assumption. constructor. assumption. assumption.
Qed.

Lemma hcwf: forall {Gamma e T}, has_type Gamma e T -> ctx_wf Gamma
    with
    tcwf: forall {Gamma T}, ty_wf Gamma T -> ctx_wf Gamma.
Proof.
  - intros. induction H; eauto.
  - intros. induction H; eauto.
Qed.

Lemma extract1: forall Gamma T1 T2, ty_wf Gamma (TMem T1 T2) -> ty_wf Gamma T2.
Proof.
  intros. inversion H. eauto.
Qed.

Lemma extract2: forall Gamma T1 T2, ty_wf Gamma (TMem T1 T2) -> ty_wf Gamma T1.
Proof.
  intros. inversion H. eauto.
Qed.

Lemma ty_wf_open: forall Gamma e T1 T2,
    ty_wf (T1 :: Gamma) (open (varF (length Gamma)) T2) ->
    has_type Gamma e T1 ->
    ty_wf Gamma (open' e T2)
  with
    has_type_open: forall Gamma e1 e2 T1 T2,
      has_type (T1 :: Gamma) e2 T2 ->
      has_type Gamma e1 T1 ->
      has_type Gamma (open_tm' e1 e2) (open' e1 T2).
Proof.
  -  (* ty_wf_open *)
    intros.  unfold open in *. unfold open' in *. unfold open_tm' in *.
    generalize dependent Gamma. generalize dependent e. generalize dependent T1.
    induction T2; intros.
    (* TTop *)
    -- simpl. constructor. eapply hcwf. eauto.
    (* TBot *)
    -- simpl. constructor. eapply hcwf. eauto.
    (* TAll *)
    -- simpl in H. inversion H. subst. simpl. constructor.
       --- eapply IHT2_1; eauto.
       --- unfold open in *.
         admit. (* TODO messy *)
    (* TSel *)
    -- inversion H0; subst; eauto.
    (* TMem *)
    -- inversion H. subst. simpl. constructor.
       eapply IHT2_1. eauto. auto.
       eapply IHT2_2. eauto. auto.
    (* TBind *)
    -- inversion H.
    (* TAnd *)
    -- inversion H.

  (* has_type_open *)
  - intros. unfold open in *. unfold open' in *. unfold open_tm' in *.
    generalize dependent Gamma. generalize dependent e1. generalize dependent e2.
    generalize dependent T1.
    induction T2; intros; eauto.
Admitted. (*TODO: most of the cases are wrong, try avoiding eauto *)

Lemma htwf: forall {Gamma e T}, has_type Gamma e T -> ty_wf Gamma T.
Proof.
  intros. induction H; auto.
  - eapply wf_lookup; eauto.
  - apply wf_sel with (T1 := T1) (T2 := TTop); auto. constructor. eapply tcwf. eauto.
  - apply (extract1 _ _ _ IHhas_type2).
  - constructor; auto.
  - inversion IHhas_type1. subst. eapply ty_wf_open; eauto.
  - constructor; auto.
Qed.

End D_meta.

Section Term_Reflect.

  (* "term T" is the type of coq terms having type T, where T ranges over the shallow embedded types above.  *)
  Polymorphic Inductive term: Type -> Type :=
  | term_tnat: TNat -> term TNat (* TODO remove later *)
  | term_ttop: TTop -> term TTop
  | term_tbot: TTop -> term TBot
  | term_tmem: forall T, TMem T T -> term (TMem T T)
  | term_tsel: forall L U (t: TMem L U), @TSel L U t -> term (@TSel L U t)
  | term_tall: forall T U, TAll T U -> term (TAll T U)
  | term_tand: forall T U, TAnd T U -> term (TAnd T U)
  .

  (* ∃T.term T*)
  Polymorphic Definition TERM: Type := sigT (fun T: Type => term T).

  (* pack a term T into TERM *)
  Polymorphic Definition TERM_of {T} (t: term T): TERM :=
    existT term T t.

End Term_Reflect.

  (* The context encoding is somewhat inspired by
       "System F in Agda for Fun and Profit",
     by Chapman, Kireev, Nester, and Wadler (MPC'19). *)

  (* Translated typing contexts *)
  Polymorphic Inductive ty_env: Type :=
  | ty_nil: ty_env
  | ty_cons: Type -> ty_env -> ty_env
  .

  (* \lang \rang *)
  Notation "⟪ x ; .. ; y ⟫" := (ty_cons x .. (ty_cons y ty_nil) ..).
  Notation "⟪⟫" := ty_nil.
  Notation "T ;;⋆ Gamma" := (ty_cons T Gamma) (at level 70, right associativity).

  Local Definition ty_env_ex1: ty_env := ty_cons Type (ty_cons Prop (ty_cons Set (ty_cons TERM ty_nil))).
  Local Definition ty_env_ex2: ty_env := ⟪ Type ; Prop ; Set; TERM; ty_env ⟫.

  (* Morally, ty_env is a list of Coq types with heterogeneous universe
   levels However, we cannot just resolve to the standard list type,
   e.g.,

     Polymorphic Definition ty_env: Type = list Type.

   which results in an odd proof obligation

     Type@{coq.1760} = list Type@{coq.1762}.

   It seems doubtful that we can proceed here. *)

  Fixpoint ty_env_length (Gamma: ty_env): nat :=
    match Gamma with
    | ⟪⟫ => 0
    | _ ;;⋆ Gamma' => 1 + (ty_env_length Gamma')
    end.

  (* Term contexts are indexed by the typing context. *)
  Polymorphic Inductive tm_env: ty_env -> Type :=
  | tm_nil:  tm_env ⟪⟫
  | tm_cons: forall T Gamma, T -> tm_env Gamma -> tm_env (T ;;⋆ Gamma)
  .

  (* \lAngle \rAngle*)
  Notation "⟨ x ; .. ; y ⟩" := (tm_cons _ _ x .. (tm_cons _ _ y tm_nil) ..).
  Notation "⟨⟩" := tm_nil.
  Notation "v ;⋆ gamma" := (tm_cons _ _ v gamma) (at level 65, right associativity).

  Local Definition tm_env_ex1 := ⟨ 1; 2; False ⟩.
  Check tm_env_ex1.

  Polymorphic Definition tm_env_destruct {T Gamma} (c: tm_env (T ;;⋆ Gamma)): (T * (tm_env Gamma)) :=
    match c with
    | x ;⋆ xs => (x,xs)
    end.

  Polymorphic Definition tm_env_hd {T Gamma} (c: tm_env (T ;;⋆ Gamma)) := fst (tm_env_destruct c).
  Polymorphic Definition tm_env_tl {T Gamma} (c: tm_env (T ;;⋆ Gamma)) := snd (tm_env_destruct c).

  Fixpoint tm_env_length {Gamma} (gamma: tm_env Gamma): nat :=
    match gamma with
    | ⟨⟩ => 0
    | _ ;⋆ vs => 1 + (tm_env_length vs)
    end.

  Lemma env_length_eq: forall Gamma (gamma: tm_env Gamma), ty_env_length Gamma = tm_env_length gamma.
  Proof.
    intros.
    induction gamma; simpl; auto.
  Qed.


(*

how should this stuff behave?

t_all translation case:
  {{ Gamma }} = list of *terms* having *translated* types as prescribed by Gamma

  ty_wf Gamma T1     ⤳ T1' : {{ Gamma }} -> Type
  ty_wf T1::Gamma T2 ⤳ T2' : {{ T1::Gamma }} -> Type
  ty_wf Gamma (D.Tall T1 T2)

  ⤳ {{ Gamma }} ->  TAll (T1' {{ Gamma }},  λx:T1' {{ Gamma }}.  T2' (x :: {{ Gamma }}))

structural properties:

  ctx_cons [[T1]] {{ Gamma }} = {{ T1 :: Gamma }}

*)

Section Interp.

  Polymorphic Variable DUMMY_TERM: { U: Type & { Gamma': ty_env & tm_env Gamma' -> term U } }.
  Polymorphic Variable DUMMY_TYPE: { Gamma': ty_env & tm_env Gamma' -> Type }.

  Polymorphic Fixpoint tctx {Gamma} (wf: D.ctx_wf Gamma): ty_env :=
    match wf with
    | D.wf_empty => ⟪⟫
    | D.wf_cons Gamma T wf_Gamma_T wf_Gamma => (ttp wf_Gamma_T) ;;⋆ (tctx wf_Gamma)
    end
  with ttp {Gamma} {T} (ty_wf: D.ty_wf Gamma T): { Gamma : ty_env & tm_env Gamma -> Type}  :=
      match ty_wf with
        | _ => DUMMY_TYPE
    (* | D.wf_top _ => *)
    (*   TTop *)
    (* | D.wf_bot _ => *)
    (*   TBot *)
    (* | D.wf_all _ _ _ ty_wf_T1 ty_wf_T2 => *)
    (*   TBot (*TODO: requires denotation as context-dependent functions *) *)
    (* | D.wf_mem _ _ _ ty_wf_T1 ty_wf_T2 => *)
    (*   TMem (ttp ty_wf_T1) (ttp ty_wf_T2) *)
    (* | D.wf_sel _ _ _ _ _ _ has_type_e => *)
    (*   match ttm has_type_e with *)
    (*   | existT _ _ (term_tmem T t) => @TSel T T t *)
    (*   | _ => False *)
    (*   end *)
    end
  (*
    Problem: we cannot mention ttp in the return type of ttm! The idea is to
    construct a TERM = term U for some U s.t. U = ttp (htwf typing).
    reify is supposed to turn this intermediate term representation into a proper
    coq term having the type U.
   *)
  with ttm {Gamma} {t} {T} (typing: D.has_type Gamma t T): { U: Type & { Gamma': ty_env & tm_env Gamma' -> term U } } :=
      match typing with
      | _ => DUMMY_TERM
    (* | D.t_var v _ _ _ _ => *)
    (*   TERM_of (term_tnat 0) (* TODO *) *)
    (* | D.t_typ _ _ ty_wf_T1 => *)
    (*   TERM_of (term_tnat 0) (* TODO *) *)
    (* | D.t_seli _ _ _ _ has_type_a_T1 has_type_e_TM_T1_Top => *)
    (*   TERM_of (term_tnat 0) (* TODO *) *)
    (* | D.t_sele _ _ _ _ has_type_a_TSel_e has_type_e_TM_Bot_T1 => *)
    (*   TERM_of (term_tnat 0) (* TODO *) *)
    (* | D.t_app _ _ _ _ _ has_type_f_TAll_T1_T2 has_type_x_T1 => *)
    (*   TERM_of (term_tnat 0) (* TODO *) *)
    (* | D.t_abs _ _ _ _ ty_wf_T1 has_type_y_T2 => *)
    (*   TERM_of (term_tnat 0) (* TODO *) *)
    end.


  (* Certifies that term U indeed gives a U. *)
  Polymorphic Variable reify: forall U, term U -> U. (* TODO: define *)

  (* TODO: use type classes to make more readable *)
  Polymorphic Lemma ttm_yields_ttp: forall Gamma t T (typing: D.has_type Gamma t T), (projT1 (ttm typing)) = (ttp (htwf typing)).
  Proof.
  Admitted.

  Unset Printing Universes.
  (* type preservation  *)
  Polymorphic Theorem type_preservation: forall Gamma t T (typing: D.has_type Gamma t T), (ttp (htwf typing)).
  Proof.
    intros.
    rewrite <- ttm_yields_ttp.
    destruct (ttm typing).
    simpl.
    apply reify.
    assumption.
  Qed.

(* TODO: how to relate evaluation in D and in Coq?

   - State as axiom that "Coq terms normalize" (does Coq coq correct paper help here?)
   - Seems reasonable to prove: If a well-typed source term never yields a result for any
     amount of fuel, then the coq translation does not normalize => contradiction of axiom

*)


End Interp.
