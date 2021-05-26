Require Import Lia.
Require Import PeanoNat.

Import Notations.

Definition fVar := nat.
Definition bVar  := nat.

Inductive var : Type :=
  | varF : fVar -> var
  | varB : bVar -> var.

Inductive sort : Type := prop | type.

Inductive expr : Type :=
  | TSort : sort -> expr
  | tVar : var -> expr
  | TAll : expr -> expr -> expr
  | tLam : expr -> expr
  | tApp : expr -> expr -> expr
  | TSig : expr -> expr -> expr
  | tPair : expr -> expr -> expr
  | tFst : expr -> expr
  | tSnd : expr -> expr.

Definition cx : Type := list expr.
Notation "G ;; T" := (cons T G) (at level 80).

Coercion TSort : sort >-> expr.
Coercion tVar : var >-> expr.

Reserved Notation "{ i :-> e }" (at level 50).
Fixpoint open (i : bVar) (e' e : expr) : expr :=
  match e with
  | TSort _ | tVar (varF _) => e
  | tVar (varB j) => if i =? j then e' else e
  | TAll T U => TAll ({i :-> e'} T) ({S i :-> e'} U)
  | tLam t => tLam ({S i :-> e'} t)
  | tApp t u => tApp ({i :-> e'} t) ({i :-> e'} u)
  | TSig T U => TSig ({i :-> e'} T) ({S i :-> e'} U)
  | tPair t u => tPair ({i :-> e'} t) ({i :-> e'} u)
  | tFst t => tFst ({i :-> e'} t)
  | tSnd t => tSnd ({i :-> e'} t)
  end
  where "{ i :-> e }" := (open i e).

Notation "T ^ e" := (open 0 e T).

Reserved Notation "{ i <-: x }" (at level 50).
Fixpoint close (x : fVar) (i : bVar) (e : expr) :=
  match e with
  | TSort _ | tVar (varB _) => e
  | tVar (varF y) => if x =? y then varB i else e
  | TAll T U => TAll ({i <-: x} T) ({S i <-: x} U)
  | tLam t => tLam ({i <-: x} t)
  | tApp t u => tApp ({i <-: x} t) ({i <-: x} u)
  | TSig T U => TSig ({i <-: x} T) ({S i <-: x} U)
  | tPair t u => tPair ({i <-: x} t) ({i <-: x} u)
  | tFst t => tFst ({i <-: x} t)
  | tSnd t => tSnd ({i <-: x} t)
  end
  where "{ i <-: x }" := (close x i).

Notation "T \ x" := (close x 0 T) (at level 50).

Inductive closed (b f : nat) : expr -> Type :=
  | cl_sort : forall s : sort, closed b f s
  | cl_varF : forall x, x < f -> closed b f (varF x)
  | cl_varB : forall i, i < b -> closed b f (varB i)
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

Reserved Notation "e ~[ k ]~> u" (no associativity, at level 90).
Reserved Notation "e == u" (no associativity, at level 90).
Reserved Notation "G |-cc" (no associativity, at level 90).
Reserved Notation "G |-cc e : T" (no associativity, at level 90, 
                                  e at next level).

Inductive lookup : cx -> fVar -> expr -> Type :=
  | l_top : forall G T, lookup (G ;; T) (length G) T
  | l_pop : forall G x T, lookup G x T -> forall U, lookup (G ;; U) x T.

Module CC.

Inductive step : nat -> expr -> expr -> Type :=.

(* Context formation *)
Inductive wfCx : cx -> Type :=
  | wf_nil : nil |-cc
 
  | wf_snoc : forall G T s,
    G |-cc T : TSort s ->
    G ;; T |-cc

  where "G |-cc" := (wfCx G)

  (* Typechecking *)
  with hasType : cx -> expr -> expr -> Type :=
  | t_ax : forall G, G |-cc -> G |-cc prop : type

  | t_var : forall G x T,
    G |-cc ->
    lookup G x T ->
    G |-cc varF x : T

  | t_all : forall G T U sT sU,
    closed 1 (length G) U ->
    G |-cc T : TSort sT ->
    G ;; T |-cc U ^ varF (length G) : TSort sU ->
    G |-cc TAll T U : TSort sU

  | t_lam : forall G T U e s,
    closed 0 (length G) (TAll T U) ->
    closed 1 (length G) e ->
    G |-cc T : TSort s ->
    G ;; T |-cc e ^ varF (length G) : U ^ varF (length G) ->
    G |-cc tLam e : TAll T U

  | t_app : forall G T U t u,
    G |-cc t : TAll T U ->
    G |-cc u : T ->
    G |-cc tApp t u : U ^ u

  | t_sig : forall G T U sT sU,
    closed 1 (length G) U ->
    G |-cc T : TSort sT ->
    G ;; T |-cc U ^ varF (length G) : TSort sU ->
    G |-cc TSig T U : TSort sU

  | t_pair : forall G T U s t u,
    G |-cc TSig T U : TSort s ->
    G |-cc t : T ->
    G |-cc u : U ^ t ->
    G |-cc tPair t u : TSig T U

  | t_fst : forall G T U e,
    G |-cc e : TSig T U ->
    G |-cc tFst e : T

  | t_snd : forall G T U e,
    G |-cc e : TSig T U ->
    G |-cc tSnd e : U ^ (tFst e)
        (*
  | t_conv : forall G t T U (s : sort),
    G |-cc t : T ->
    G |-cc U : s ->
    T == U ->
    G |-cc t : U
         *)
where "G |-cc e : T" := (hasType G e T).

End CC.

Reserved Notation "G |-d" (no associativity, at level 90).
Reserved Notation "G |-d T"(no associativity, at level 90).
Reserved Notation "G |-d e : T" (no associativity, at level 90, e at next level).
Reserved Notation "G |-d T <: U"(no associativity, at level 90, T at next level).

Definition TBot := TAll prop (varB 0).
Definition TTop := TSig prop (varB 0).
Definition TTyp T U := TSig prop (TSig (TAll T (varB 1)) (TAll (varB 1) U)).
Definition TSel x := tFst x.
Definition tTyp T := tPair T (tPair (tLam (varB 0)) (tLam (varB 0))).

Module D.

Inductive wfCx : cx -> Type :=
  | wf_nil : nil |-d

  | wf_snoc : forall G T,
    G |-d T ->
    G ;; T |-d

  where "G |-d" := (wfCx G)

  with wfTy : cx -> expr -> Type :=
  | wf_bot : forall G, G |-d -> G |-d TBot
  | wf_top : forall G, G |-d -> G |-d TTop

  | wf_all : forall G T U,
      closed 1 (length G) U ->
      G ;; T |-d U ^ varF (length G) ->
      G |-d TAll T U

  | wf_typ : forall G T U, G |-d T -> G |-d U -> G |-d TTyp T U

  | wf_sel : forall G T U x, G |-d varF x : TTyp T U -> G |-d TSel (varF x)

  where "G |-d T" := (wfTy G T)

  with hasType : cx -> expr -> expr -> Type :=
  | t_var : forall G x T,
      G |-d ->
      lookup G x T ->
      G |-d varF x : T

  | t_lam : forall G T e U,
      closed 1 (length G) e ->
      closed 0 (length G) (TAll T U) ->
      G ;; T |-d e ^ varF (length G) : U ^ varF (length G) ->
      G |-d tLam e : TAll T U

  | t_app : forall G t u T U,
      closed 0 (length G) U ->
      G |-d t : TAll T U ->
      G |-d u : T ->
      G |-d tApp t u : U

  | t_dapp : forall G t x T U,
      G |-d t : TAll T U ->
      G |-d varF x : T ->
      G |-d tApp t (varF x) : U ^ varF x

  | t_sub : forall G t T U,
      G |-d t : T ->
      G |-d T <: U ->
      G |-d t : U

  where "G |-d e : T" := (hasType G e T)

  with subtype : cx -> expr -> expr -> Type :=
  | s_bot : forall G T, G |-d T -> G |-d TBot <: T
  | s_top : forall G T, G |-d T -> G |-d T <: TTop

  | s_all : forall G T1 T2 U1 U2,
      closed 1 (length G) U1 ->
      closed 1 (length G) U2 ->
      G ;; T1 |-d U1 ^ varF (length G) ->
      G |-d T2 <: T1 ->
      G ;; T2 |-d U1 ^ varF (length G) <: U2 ^ varF (length G) ->
      G |-d TAll T1 U1 <: TAll T2 U2

  | s_typ : forall G T1 T2 U1 U2,
      G |-d T2 <: T1 ->
      G |-d U1 <: U2 ->
      G |-d TTyp T1 U1 <: TTyp T2 U2

  | s_sel1 : forall G T U x,
      G |-d varF x : TTyp T U ->
      G |-d T <: TSel (varF x)

  | s_sel2 : forall G T U x,
      G |-d varF x : TTyp T U ->
      G |-d TSel (varF x) <: U

  | s_refl : forall G T, G |-d T -> G |-d T <: T

  | s_trans : forall G T U W,
      G |-d T <: U ->
      G |-d U <: W ->
      G |-d T <: W

  where "G |-d T <: U" := (subtype G T U).

End D.

Definition SBot T := tLam (tApp (varB 0) T).
Definition STop T := tLam (tPair T (varB 0)).
Definition SAll c1 c2 := 
  tLam (tLam (tApp c2 (tApp (varB 1) (tApp c1 (varB 0))))).
Definition SSel1 x := tLam (tApp (tFst (tSnd (tVar x))) (varB 0)).
Definition SSel2 x := tLam (tApp (tSnd (tSnd (tVar x))) (varB 0)).
Definition STyp c1 c2 :=
  tLam (tPair (TSel (varB 0)) 
              (tPair (tLam (tApp (SSel1 (varB 1)) (tApp c1 (varB 0))))
                     (tLam (tApp c2 (tApp (SSel2 (varB 1)) (varB 0)))))).
Definition SRefl := tLam (varB 0).
Definition STrans c1 c2 := tLam (tApp c2 (tApp c1 (varB 0))).

Inductive coercion : expr -> Type :=
  | c_bot : forall T, coercion (SBot T)
  | c_top : forall T, coercion (STop T)
  | c_all : forall c c',
      coercion c -> 
      coercion c' -> 
      coercion (SAll c c')
  | c_typ : forall c c',
      coercion c ->
      coercion c' ->
      coercion (STyp c c')
  | c_sel1 : forall x, coercion (SSel1 x)
  | c_sel2 : forall x, coercion (SSel2 x)
  | c_refl : coercion SRefl
  | c_trans : forall c c',
      coercion c ->
      coercion c' ->
      coercion (STrans c c').

Inductive Cx : cx -> Type :=
  | cx_nil : Cx nil

  | cx_snoc : forall {G T}, Cx G -> Ty G T -> Cx (G ;; T)

  with Ty : cx -> expr -> Type :=
  | ty_bot : forall {G}, Cx G -> Ty G TBot
  | ty_top : forall {G}, Cx G -> Ty G TTop

  | ty_all : forall {G T U},
      closed 1 (length G) U ->
      Ty G T ->
      Ty (G ;; T) (U ^ varF (length G)) ->
      Ty G (TAll T U)

  | ty_typ : forall {G T U}, 
      Ty G T -> Ty G U -> 
      Ty G (TTyp T U)

  | ty_sel : forall {G T U x},
      Tm G (varF x) (TTyp T U) ->
      Ty G (TSel (varF x))

  with Tm : cx -> expr -> expr -> Type :=
  | tm_var : forall {G} x {T},
      Cx G ->
      lookup G x T ->
      Tm G (varF x) T

  | tm_lam : forall {G t T U},
      closed 0 (length G) (TAll T U) ->
      closed 1 (length G) t ->
      Tm (G ;; T) (t ^ varF (length G)) (U ^ varF (length G)) ->
      Tm G (tLam t) (TAll T U)

  | tm_app: forall {G t u T U},
      closed 0 (length G) U ->
      Tm G t (TAll T U) ->
      Tm G u T ->
      Tm G (tApp t u) U

  | tm_dapp : forall {G t x T U},
      Tm G t (TAll T U) ->
      Tm G (varF x) T ->
      Tm G (tApp t (varF x)) (U ^ varF x)

  | tm_typ : forall {G T}, Ty G T -> Tm G (tTyp T) (TTyp T T)

  | tm_sub : forall {G t c T},
      Tm G (tApp c t) T ->
      coercion c ->
      Tm G t T.

Definition hdCx {G T} (cxGT : Cx (G ;; T)) : Ty G T.
Proof.
  inversion cxGT. subst. assumption.
Qed.

Definition tlCx {G T} (cxGT : Cx (G ;; T)) : Cx G.
Proof.
  inversion cxGT. subst. assumption.
Defined.

Fixpoint Ty_Cx {G T} (tyT : Ty G T) : Cx G :=
  match tyT in Ty G T return Cx G with
  | ty_bot cxG | ty_top cxG => cxG
  | ty_all _ tyU _ | ty_typ tyU _ => Ty_Cx tyU
  | ty_sel tmx => Tm_Cx tmx
  end

  with Tm_Cx {G e T} (tme : Tm G e T) : Cx G :=
  match tme in Tm G e T return Cx G with
  | tm_var _ cxG _ => cxG
  | tm_lam _ _ tmt => tlCx (Tm_Cx tmt)
  | tm_app _ tmt _ | tm_dapp tmt _ => Tm_Cx tmt
  | tm_typ tyT => Ty_Cx tyT
  | tm_sub tmct _ => Tm_Cx tmct
  end.

Fixpoint Tm_Ty {G e T} (tme : Tm G e T) : Ty G T.
Admitted.

Fixpoint Tm_expr {G e T} (tme : Tm G e T) : expr :=
  match tme with
  | tm_var x _ _ => varF x
  | tm_lam _ _ tmt => tLam (Tm_expr tmt \ length G)
  | tm_app _ tmt tmu => tApp (Tm_expr tmt) (Tm_expr tmu)
  | tm_dapp tmt tmx => tApp (Tm_expr tmt) (Tm_expr tmx)
  | tm_typ tyT => tTyp (Ty_expr tyT)
  | tm_sub tmce _ => Tm_expr tmce
  end

  with Ty_expr {G T} (tyT : Ty G T) : expr :=
  match tyT with
  | ty_bot _ => TBot
  | ty_top _ => TTop
  | ty_all _ tyT tyU => TAll (Ty_expr tyT) (Ty_expr tyU \ length G)
  | ty_typ tyU tyW => TTyp (Ty_expr tyU) (Ty_expr tyW)
  | ty_sel tmx => TSel (Tm_expr tmx)
  end. 

Fixpoint Cx_cx {G} (cxG : Cx G) : cx :=
  match cxG with
  | cx_nil => nil
  | cx_snoc cxG' tyT => Cx_cx cxG' ;; Ty_expr tyT
  end.

Fixpoint Cx_cc {G} (cxG : Cx G) : 
  let G' := Cx_cx cxG in CC.wfCx G'

  with Ty_cc {G T} (tyT : Ty G T) : 
  let G' := Cx_cx (Ty_Cx tyT) in
  let T' := Ty_expr tyT in
  CC.hasType G' T' prop

  with Tm_cc {G e T} (tme : Tm G e T) : 
  let G' := Cx_cx (Tm_Cx tme) in
  let e' := Tm_expr tme in 
  let T' := Ty_expr (Tm_Ty tme) in
  CC.hasType G e' T.
Proof.
  * destruct cxG; simpl; econstructor. admit.

  * admit.

  * destruct tme; simpl.
    - constructor. apply Cx_cc. assumption. assumption.
    - econstructor. admit. admit. admit. admit.
    - assert (U = U ^ Tm_expr tme2). admit. rewrite H. 
      econstructor. apply Tm_cc. apply Tm_cc.
    -
