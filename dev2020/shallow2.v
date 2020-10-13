Module Shallow.
  Require Import Coq.Logic.StrictProp.

  Definition Bot := sEmpty.

  Definition Top := sUnit.

  Record Typ (S T : Type) : SProp :=
    typ { Sel : Type; Sel1 : Squash (S -> Sel); Sel2 : Squash (Sel -> T) }.

  Definition widen {S1 S2 T1 T2 : Type}
             (S : Squash (S2 -> S1)) (T : Squash (T1 -> T2))
             (ST1 : Typ S1 T1) : Typ S2 T2 :=
    match S, T, ST1 with
    | squash fs', squash ft', typ _ _ X (squash fs) (squash ft) =>
      typ S2 T2 X (squash (fun (s : S2) => fs (fs' s))) (squash (fun (x : X) => ft' (ft x)))
    end.

  Set Cumulative StrictProp. (* Is this okay? *)
  Definition subtype (S T : SProp) := Squash (S -> T).
  Notation "S '<:' T" := (subtype S T) (at level 90).

  Definition sqapp {A B : SProp} (sf : Squash (A -> B)) (sa : Squash A) : Squash B :=
    match sf, sa with
    | squash f, squash a => squash (f a)
    end.

  Definition S_bot {S : SProp} : Bot <: S :=
    squash (sEmpty_rect (fun _ => S)).

  Definition S_top {S : SProp} : S <: Top :=
    squash (fun (v : S) => stt).

  Definition S_typ {S1 S2 T1 T2 : SProp}
             (fS : S2 <: S1) (fT : T1 <: T2) : Typ S1 T1 <: Typ S2 T2 :=
                                                              squash (widen fS fT).

  Definition S_pi {S1 S2 : SProp} {T1 : Squash S1 -> SProp} {T2 : Squash S2 -> SProp}
             (fS : S2 <: S1) (fT : forall {s : Squash S2}, T1 (sqapp fS s) <: T2 s)
    : (forall s, T1 s) <: (forall s, T2 s) :=
      squash (fun f s => sqapp fT (f (sqapp fS s))).
