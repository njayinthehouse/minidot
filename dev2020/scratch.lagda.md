D<:> Sy-22-ntax
-----------
```eg
Type ∋ S, T ::= ⊥ | ⊤ | S ⋯ T | x·Type | Π S T
Term ∋ e ::= x | λe | e e | Type S
Var  ∋ x ::= z | s x
Cx   ∋ Γ ::= · | Γ, S
```
CC Syntax
---------
```eg
Sort ∋ s ::= * | ▢
Expression ∋ A, B, e ::= x | λ:A.e | e e | ∀:A.e | s
```

D<:> WF
-------
```eg
---- WF-nil
· ⊢

Γ ⊢
Γ ⊢ S type
----------- WF-snoc
Γ, S ⊢

--------------- WF-{bot, top}
Γ ⊢ {⊥, ⊤} type

Γ ⊢ {S, T} type
---------------- WF-typ
Γ ⊢ S ⋯ T type

Γ ⊢ x : S
-------------- WF-sel
Γ ⊢ Sel x type

Γ ⊢ S type
Γ, S ⊢ T type
-------------- WF-pi
Γ ⊢ Π S T type
```

I write ⟦ Γ ⟧(P) to denote the translation of a context in System D<:>, where P is a
judgment that Γ is well formed. I write πᵢ P to denote the iᵗʰ premise of P. I write
R {P₁, P₂...}, where R is a rule name, to denote that you can derive a proof of this
rule given these proofs.

⟦ · ⟧(P) = ·
⟦ Γ, S ⟧(P) = ⟦ Γ ⟧(π₁ P), ⟦ S ⟧(π₂ P)

⟦ ⊥ ⟧(P) = ∀(X : *). X
⟦ ⊤ ⟧(P) = ∃(X : *). X
⟦ S ⋯ T ⟧(P) = ∃(X : *), ⟦ S ⟧(π₁ P) -> S ∧ ⟦ T ⟧(π₂ P)
⟦ x·Type ⟧(P) = ⟦ x ⟧(π₁ P)
⟦ Π S T ⟧(P) = ∀(x : ⟦ S ⟧(π₁ P)). ⟦ T ⟧(π₂ P)

D<:> Typechecking
-----------------
```eg
Γ ∋ x : S
--------- T-var
Γ ⊢ x : S

Γ, S ⊢ e : T
-------------- T-fun
Γ ⊢ λe : Π S T

Γ ⊢ e : Π S T
Γ ⊢ e' : S
z ∉ fv(T)
--------------- T-app
Γ ⊢ e e' : T[x]

Γ ⊢ e : Π S T
Γ ⊢ x : S
-------------- T-dapp
Γ ⊢ e x : T[x]

------------------ T-typ
Γ ⊢ Type S : S ⋯ S
```

Translation into CC
-------------------
```eg
-------------
⟦ x ⟧(P) = x

P :: (Γ ⊢ λx.e : Π S T)           <- to bind S
WF-S :: Γ ★ S
---------------------------------------------
⟦ λx.e ⟧(P) = λ(x : ⟦ S ⟧(WF-S)). ⟦ e ⟧(π₁ P)

--------------------------------------
⟦ e e' ⟧(P) = ⟦ e ⟧(π₁ P) ⟦ e' ⟧(π₂ P)

------------------------------------
⟦ Type S ⟧(P) = ⟦ S ⟧(π₁ P), id, id
```

D<:> Subtyping
---------------
```eg

----------------------
⟦ ⊥ <: S ⟧(P) = magic

------------------------
⟦ _ <: ⊤ ⟧(P) = λ_. unit

WF₁ :: Γ ★ S₁ ⋯ T₁                     <- needed?
----------------------------------------------------------
⟦ S₁ ⋯ T₁ <: S₂ ⋯ T₂ ⟧(P) =
    λ ((x, from, to) : ⟦ S₁ ⋯ T₁ ⟧(WF₁)).
      x, ⟦ S₂ <: S₁ ⟧(π₁ P) ∘ from, to ∘ ⟦ T₁ <: T₂ ⟧(π₂ P)

P :: Γ ⊢ x : S ⋯ T
⟦ x ⟧(P) = _, from, to
--------------------------
⟦ S <: x·Type ⟧(P) = from
⟦ x·Type <: T ⟧(P) = to

WF₁ :: Γ ★ Π S₁ T₁
------------------------------------------------------------------------
⟦ Π S₁ T₁ <: Π S₂ T₂ ⟧(P) =
    λ (f : ⟦ Π S₁ T₁ ⟧(WF₁)). ⟦ S₂ <: S₁ ⟧(π₁ P) ∘ f ∘ ⟦ T₁ <: T₂ ⟧(π₂ P)
```
