module S4WithoutTerms where

open import Prelude public


--------------------------------------------------------------------------------
--
-- Syntax


-- Type variables
data TVar : Set where
  tvar : String → TVar

injtvar : ∀ {s₁ s₂} → tvar s₁ ≡ tvar s₂ → s₁ ≡ s₂
injtvar refl = refl

_≟ₜᵥ_ : (x₁ x₂ : TVar) → Dec (x₁ ≡ x₂)
tvar s₁ ≟ₜᵥ tvar s₂ = mapDec (tvar &_) injtvar (s₁ ≟ₛ s₂)

instance
  tvarIsString : IsString TVar
  tvarIsString =
    record
      { Constraint = λ s → ⊤
      ; fromString = λ s → tvar s
      }


-- Types
infixl 9 _∧_
infixr 7 _⊃_
data 𝒯 : Set where
  ᵗᵛ  : (x : TVar) → 𝒯
  _⊃_ : (A B : 𝒯) → 𝒯
  _∧_ : (A B : 𝒯) → 𝒯
  𝕋   : 𝒯
  □_  : (A : 𝒯) → 𝒯

instance
  typeIsString : IsString 𝒯
  typeIsString =
    record
      { Constraint = λ s → ⊤
      ; fromString = λ s → ᵗᵛ (tvar s)
      }


-- Contexts
𝒞 : Set
𝒞 = List² 𝒯 𝒯


-- Syntactic entailment
infix 3 _⊢_
data _⊢_ : 𝒞 → 𝒯 → Set
  where
    ᵐᵛ  : ∀ {A Δ Γ} → (i : Δ ∋ A)
                    → Δ ⁏ Γ ⊢ A

    ʳᵛ  : ∀ {A Δ Γ} → (i : Γ ∋ A)
                    → Δ ⁏ Γ ⊢ A

    ƛ   : ∀ {A B Δ Γ} → (M : Δ ⁏ Γ , A ⊢ B)
                      → Δ ⁏ Γ ⊢ A ⊃ B

    _$_ : ∀ {A B Δ Γ} → (M : Δ ⁏ Γ ⊢ A ⊃ B) (N : Δ ⁏ Γ ⊢ A)
                      → Δ ⁏ Γ ⊢ B

    _,_ : ∀ {A B Δ Γ} → (M : Δ ⁏ Γ ⊢ A) (N : Δ ⁏ Γ ⊢ B)
                      → Δ ⁏ Γ ⊢ A ∧ B

    π₁  : ∀ {A B Δ Γ} → (M : Δ ⁏ Γ ⊢ A ∧ B)
                      → Δ ⁏ Γ ⊢ A

    π₂  : ∀ {A B Δ Γ} → (M : Δ ⁏ Γ ⊢ A ∧ B)
                      → Δ ⁏ Γ ⊢ B

    tt  : ∀ {Δ Γ} → Δ ⁏ Γ ⊢ 𝕋

    ⌜_⌝ : ∀ {A Δ Γ} → (M : Δ ⁏ ∅ ⊢ A)
                    → Δ ⁏ Γ ⊢ □ A

    ⌞_⌟ : ∀ {A C Δ Γ} → (M : Δ ⁏ Γ ⊢ □ A) (N : Δ , A ⁏ Γ ⊢ C)
                      → Δ ⁏ Γ ⊢ C


-- Normal and neutral forms
mutual
  infix 3 _⊢ₙₘ_
  data _⊢ₙₘ_ : 𝒞 → 𝒯 → Set
    where
      ƛ   : ∀ {A B Δ Γ} → (M : Δ ⁏ Γ , A ⊢ₙₘ B)
                        → Δ ⁏ Γ ⊢ₙₘ A ⊃ B

      _,_ : ∀ {A B Δ Γ} → (M : Δ ⁏ Γ ⊢ₙₘ A) (N : Δ ⁏ Γ ⊢ₙₘ B)
                        → Δ ⁏ Γ ⊢ₙₘ A ∧ B

      tt  : ∀ {Δ Γ} → Δ ⁏ Γ ⊢ₙₘ 𝕋

      ⌜_⌝ : ∀ {A Δ Γ} → (M : Δ ⁏ ∅ ⊢ A)
                      → Δ ⁏ Γ ⊢ₙₘ □ A

      ⌞_⌟ : ∀ {A C Δ Γ} → (M : Δ ⁏ Γ ⊢ₙₜ □ A) (N : Δ , A ⁏ Γ ⊢ₙₘ C)
                        → Δ ⁏ Γ ⊢ₙₘ C

      ⁿᵗ  : ∀ {x Δ Γ} → (M : Δ ⁏ Γ ⊢ₙₜ ᵗᵛ x)
                      → Δ ⁏ Γ ⊢ₙₘ ᵗᵛ x

  infix 3 _⊢ₙₜ_
  data _⊢ₙₜ_ : 𝒞 → 𝒯 → Set
    where
      ᵐᵛ  : ∀ {A Δ Γ} → (i : Δ ∋ A)
                      → Δ ⁏ Γ ⊢ₙₜ A

      ʳᵛ  : ∀ {A Δ Γ} → (i : Γ ∋ A)
                      → Δ ⁏ Γ ⊢ₙₜ A

      _$_ : ∀ {A B Δ Γ} → (M : Δ ⁏ Γ ⊢ₙₜ A ⊃ B) (N : Δ ⁏ Γ ⊢ₙₘ A)
                        → Δ ⁏ Γ ⊢ₙₜ B

      π₁  : ∀ {A B Δ Γ} → (M : Δ ⁏ Γ ⊢ₙₜ A ∧ B)
                        → Δ ⁏ Γ ⊢ₙₜ A

      π₂  : ∀ {A B Δ Γ} → (M : Δ ⁏ Γ ⊢ₙₜ A ∧ B)
                        → Δ ⁏ Γ ⊢ₙₜ B


mutual
  embₙₘ : ∀ {Δ Γ A} → Δ ⁏ Γ ⊢ₙₘ A → Δ ⁏ Γ ⊢ A
  embₙₘ (ƛ M)     = ƛ (embₙₘ M)
  embₙₘ (M , N)   = embₙₘ M , embₙₘ N
  embₙₘ tt        = tt
  embₙₘ (⌜ M ⌝)   = ⌜ M ⌝
  embₙₘ (⌞ M ⌟ N) = ⌞ embₙₜ M ⌟ (embₙₘ N)
  embₙₘ (ⁿᵗ M)    = embₙₜ M

  embₙₜ : ∀ {Δ Γ A} → Δ ⁏ Γ ⊢ₙₜ A → Δ ⁏ Γ ⊢ A
  embₙₜ (ᵐᵛ i)  = ᵐᵛ i
  embₙₜ (ʳᵛ i)  = ʳᵛ i
  embₙₜ (M $ N) = embₙₜ M $ embₙₘ N
  embₙₜ (π₁ M)  = π₁ (embₙₜ M)
  embₙₜ (π₂ M)  = π₂ (embₙₜ M)


--------------------------------------------------------------------------------
--
-- Renaming


mren : ∀ {Δ Δ′ Γ A} → Δ′ ⊇ Δ → Δ ⁏ Γ ⊢ A
                    → Δ′ ⁏ Γ ⊢ A
mren η (ᵐᵛ i)    = ᵐᵛ (lookupᵣ η i)
mren η (ʳᵛ i)    = ʳᵛ i
mren η (ƛ M)     = ƛ (mren η M)
mren η (M $ N)   = mren η M $ mren η N
mren η (M , N)   = mren η M , mren η N
mren η (π₁ M)    = π₁ (mren η M)
mren η (π₂ M)    = π₂ (mren η M)
mren η tt        = tt
mren η (⌜ M ⌝)   = ⌜ mren η M ⌝
mren η (⌞ M ⌟ N) = ⌞ mren η M ⌟ (mren (liftᵣ η) N)

rren : ∀ {Δ Γ Γ′ A} → Γ′ ⊇ Γ → Δ ⁏ Γ ⊢ A
                   → Δ ⁏ Γ′ ⊢ A
rren η (ᵐᵛ i)    = ᵐᵛ i
rren η (ʳᵛ i)    = ʳᵛ (lookupᵣ η i)
rren η (ƛ M)     = ƛ (rren (liftᵣ η) M)
rren η (M $ N)   = rren η M $ rren η N
rren η (M , N)   = rren η M , rren η N
rren η (π₁ M)    = π₁ (rren η M)
rren η (π₂ M)    = π₂ (rren η M)
rren η tt        = tt
rren η (⌜ M ⌝)   = ⌜ M ⌝
rren η (⌞ M ⌟ N) = ⌞ rren η M ⌟ (rren η N)


mutual
  mrenₙₘ : ∀ {Δ Δ′ Γ A} → Δ′ ⊇ Δ → Δ ⁏ Γ ⊢ₙₘ A
                        → Δ′ ⁏ Γ ⊢ₙₘ A
  mrenₙₘ η (ƛ M)     = ƛ (mrenₙₘ η M)
  mrenₙₘ η (M , N)   = mrenₙₘ η M , mrenₙₘ η N
  mrenₙₘ η tt        = tt
  mrenₙₘ η (⌜ M ⌝)   = ⌜ mren η M ⌝
  mrenₙₘ η (⌞ M ⌟ N) = ⌞ mrenₙₜ η M ⌟ (mrenₙₘ (liftᵣ η) N)
  mrenₙₘ η (ⁿᵗ M)    = ⁿᵗ (mrenₙₜ η M)

  mrenₙₜ : ∀ {Δ Δ′ Γ A} → Δ′ ⊇ Δ → Δ ⁏ Γ ⊢ₙₜ A
                        → Δ′ ⁏ Γ ⊢ₙₜ A
  mrenₙₜ η (ᵐᵛ i)  = ᵐᵛ (lookupᵣ η i)
  mrenₙₜ η (ʳᵛ i ) = ʳᵛ i
  mrenₙₜ η (M $ N) = mrenₙₜ η M $ mrenₙₘ η N
  mrenₙₜ η (π₁ M)  = π₁ (mrenₙₜ η M)
  mrenₙₜ η (π₂ M)  = π₂ (mrenₙₜ η M)


mutual
  rrenₙₘ : ∀ {Δ Γ Γ′ A} → Γ′ ⊇ Γ → Δ ⁏ Γ ⊢ₙₘ A
                       → Δ ⁏ Γ′ ⊢ₙₘ A
  rrenₙₘ η (ƛ M)     = ƛ (rrenₙₘ (liftᵣ η) M)
  rrenₙₘ η (M , N)   = rrenₙₘ η M , rrenₙₘ η N
  rrenₙₘ η tt        = tt
  rrenₙₘ η (⌜ M ⌝)   = ⌜ M ⌝
  rrenₙₘ η (⌞ M ⌟ N) = ⌞ rrenₙₜ η M ⌟ (rrenₙₘ η N)
  rrenₙₘ η (ⁿᵗ M)    = ⁿᵗ (rrenₙₜ η M)

  rrenₙₜ : ∀ {Δ Γ Γ′ A} → Γ′ ⊇ Γ → Δ ⁏ Γ ⊢ₙₜ A
                       → Δ ⁏ Γ′ ⊢ₙₜ A
  rrenₙₜ η (ᵐᵛ i)  = ᵐᵛ i
  rrenₙₜ η (ʳᵛ i)  = ʳᵛ (lookupᵣ η i)
  rrenₙₜ η (M $ N) = rrenₙₜ η M $ rrenₙₘ η N
  rrenₙₜ η (π₁ M)  = π₁ (rrenₙₜ η M)
  rrenₙₜ η (π₂ M)  = π₂ (rrenₙₜ η M)


renₙₘ : ∀ {Δ Δ′ Γ Γ′ A} → Δ′ ⁏ Γ′ ⊇² Δ ⁏ Γ → Δ ⁏ Γ ⊢ₙₘ A
                        → Δ′ ⁏ Γ′ ⊢ₙₘ A
renₙₘ η M = (mrenₙₘ (proj₁ η) ∘ rrenₙₘ (proj₂ η)) M

renₙₜ : ∀ {Δ Δ′ Γ Γ′ A} → Δ′ ⁏ Γ′ ⊇² Δ ⁏ Γ → Δ ⁏ Γ ⊢ₙₜ A
                        → Δ′ ⁏ Γ′ ⊢ₙₜ A
renₙₜ η M = (mrenₙₜ (proj₁ η) ∘ rrenₙₜ (proj₂ η)) M


--------------------------------------------------------------------------------
--
-- Substitution


-- Simultaneous substitutions
infix 3 _⊢⋆_
_⊢⋆_ : 𝒞 → List 𝒯 → Set
Δ ⁏ Γ ⊢⋆ Ξ = All (Δ ⁏ Γ ⊢_) Ξ


mren⋆ : ∀ {Δ Δ′ Γ Ξ} → Δ′ ⊇ Δ → Δ ⁏ Γ ⊢⋆ Ξ
                     → Δ′ ⁏ Γ ⊢⋆ Ξ
mren⋆ η σ = mapAll (mren η) σ

rren⋆ : ∀ {Δ Γ Γ′ Ξ} → Γ′ ⊇ Γ → Δ ⁏ Γ ⊢⋆ Ξ
                     → Δ ⁏ Γ′ ⊢⋆ Ξ
rren⋆ η σ = mapAll (rren η) σ


mwkₛ : ∀ {Δ Γ Ξ A} → Δ ⁏ Γ ⊢⋆ Ξ
                   → Δ , A ⁏ Γ ⊢⋆ Ξ
mwkₛ σ = mren⋆ (wkᵣ idᵣ) σ

rwkₛ : ∀ {Δ Γ Ξ A} → Δ ⁏ Γ ⊢⋆ Ξ
                   → Δ ⁏ Γ , A ⊢⋆ Ξ
rwkₛ σ = rren⋆ (wkᵣ idᵣ) σ

mliftₛ : ∀ {Δ Γ Ξ A} → Δ ⁏ Γ ⊢⋆ Ξ
                     → Δ , A ⁏ Γ ⊢⋆ Ξ , A
mliftₛ σ = mwkₛ σ , ᵐᵛ zero

rliftₛ : ∀ {Δ Γ Ξ A} → Δ ⁏ Γ ⊢⋆ Ξ
                     → Δ ⁏ Γ , A ⊢⋆ Ξ , A
rliftₛ σ = rwkₛ σ , ʳᵛ zero


midₛ : ∀ {Δ Γ} → Δ ⁏ Γ ⊢⋆ Δ
midₛ {∅}     = ∅
midₛ {Γ , A} = mliftₛ midₛ

ridₛ : ∀ {Γ Δ} → Δ ⁏ Γ ⊢⋆ Γ
ridₛ {∅}     = ∅
ridₛ {Γ , A} = rliftₛ ridₛ


lookupₛ : ∀ {Δ Γ Ξ A} → Δ ⁏ Γ ⊢⋆ Ξ → Ξ ∋ A
                      → Δ ⁏ Γ ⊢ A
lookupₛ σ i = lookupAll σ i


-- Substitution
msub : ∀ {Δ Γ Ξ A} → Δ ⁏ ∅ ⊢⋆ Ξ → Ξ ⁏ Γ ⊢ A
                   → Δ ⁏ Γ ⊢ A
msub σ (ᵐᵛ i)    = rren infᵣ (lookupₛ σ i)
msub σ (ʳᵛ i)    = ʳᵛ i
msub σ (ƛ M)     = ƛ (msub σ M)
msub σ (M $ N)   = msub σ M $ msub σ N
msub η (M , N)   = msub η M , msub η N
msub η (π₁ M)    = π₁ (msub η M)
msub η (π₂ M)    = π₂ (msub η M)
msub η tt        = tt
msub σ ⌜ M ⌝     = ⌜ msub σ M ⌝
msub σ (⌞ M ⌟ N) = ⌞ msub σ M ⌟ (msub (mliftₛ σ) N)

rsub : ∀ {Δ Γ Ξ A} → Δ ⁏ Γ ⊢⋆ Ξ → Δ ⁏ Ξ ⊢ A
                  → Δ ⁏ Γ ⊢ A
rsub σ (ᵐᵛ i)    = ᵐᵛ i
rsub σ (ʳᵛ i)    = lookupₛ σ i
rsub σ (ƛ M)     = ƛ (rsub (rliftₛ σ) M)
rsub σ (M $ N)   = rsub σ M $ rsub σ N
rsub η (M , N)   = rsub η M , rsub η N
rsub η (π₁ M)    = π₁ (rsub η M)
rsub η (π₂ M)    = π₂ (rsub η M)
rsub η tt        = tt
rsub σ ⌜ M ⌝     = ⌜ M ⌝
rsub σ (⌞ M ⌟ N) = ⌞ rsub σ M ⌟ (rsub (mwkₛ σ) N)


--------------------------------------------------------------------------------
--
-- Semantics


-- Introspective Kripke models
record 𝔎 : Set₁ where
  field
    𝒲    : Set

    𝒱    : 𝒲 → TVar → Set

    _≥_  : 𝒲 → 𝒲 → Set

    idₐ  : ∀ {w} → w ≥ w

    _∘ₐ_ : ∀ {w w′ w″} → w′ ≥ w → w″ ≥ w′
                       → w″ ≥ w

    accᵥ : ∀ {x w w′} → w′ ≥ w → 𝒱 w x
                      → 𝒱 w′ x

    ⌊_⌋  : 𝒲 → 𝒞

    ⌊_⌋ₐ : ∀ {w w′} → w′ ≥ w
                    → ⌊ w′ ⌋ ⊇² ⌊ w ⌋

open 𝔎 {{…}} public


ᵐ⌊_⌋ : ∀ {{𝔐 : 𝔎}} → 𝒲 → List 𝒯
ᵐ⌊ w ⌋ = proj₁ ⌊ w ⌋

ʳ⌊_⌋ : ∀ {{𝔐 : 𝔎}} → 𝒲 → List 𝒯
ʳ⌊ w ⌋ = proj₂ ⌊ w ⌋

ᵐ⌊_⌋ₐ : ∀ {{𝔐 : 𝔎}} {w w′} → w′ ≥ w
                           → ᵐ⌊ w′ ⌋ ⊇ ᵐ⌊ w ⌋
ᵐ⌊ η ⌋ₐ = proj₁ ⌊ η ⌋ₐ

ʳ⌊_⌋ₐ : ∀ {{𝔐 : 𝔎}} {w w′} → w′ ≥ w
                           → ʳ⌊ w′ ⌋ ⊇ ʳ⌊ w ⌋
ʳ⌊ w ⌋ₐ = proj₂ ⌊ w ⌋ₐ


-- Values
mutual
  infix 3 _⊩_
  _⊩_ : ∀ {{𝔐 : 𝔎}} → 𝒲 → 𝒯 → Set

  w ⊩ ᵗᵛ x  = 𝒱 w x

  w ⊩ A ⊃ B = ∀ {w′} → (η : w′ ≥ w) (k : w′ ᵏ⊩ A)
                       → w′ ᵏ⊩ B

  w ⊩ A ∧ B = w ᵏ⊩ A × w ᵏ⊩ B

  w ⊩ 𝕋     = ⊤

  w ⊩ □ A   = ∀ {w′} → (η : w′ ≥ w)
                      → w′ ᵐᵏ⊩ A

  infix 3 _ᵏ⊩_
  _ᵏ⊩_ : ∀ {{𝔐 : 𝔎}} → 𝒲 → 𝒯 → Set
  w ᵏ⊩ A = ∀ {w′ C} → (η : w′ ≥ w) (f : ∀ {w″} → w″ ≥ w′ → w″ ⊩ A
                                                 → ⌊ w″ ⌋ ⊢ₙₘ C)
                     → ⌊ w′ ⌋ ⊢ₙₘ C

  infix 3 _ᵐᵏ⊩_
  _ᵐᵏ⊩_ : ∀ {{𝔐 : 𝔎}} → 𝒲 → 𝒯 → Set
  w ᵐᵏ⊩ A = ᵐ⌊ w ⌋ ⁏ ∅ ⊢ A × w ᵏ⊩ A


syn : ∀ {{𝔐 : 𝔎}} {w A} → w ᵐᵏ⊩ A
                        → ᵐ⌊ w ⌋ ⁏ ∅ ⊢ A
syn Mk = proj₁ Mk

sem : ∀ {{𝔐 : 𝔎}} {w A} → w ᵐᵏ⊩ A
                        → w ᵏ⊩ A
sem Mk = proj₂ Mk


-- Environments
infix 3 _ᵏ⊩⋆_
_ᵏ⊩⋆_ : ∀ {{𝔐 : 𝔎}} → 𝒲 → List 𝒯 → Set
w ᵏ⊩⋆ Ξ = All (w ᵏ⊩_) Ξ

infix 3 _ᵐᵏ⊩⋆_
_ᵐᵏ⊩⋆_ : ∀ {{𝔐 : 𝔎}} → 𝒲 → List 𝒯 → Set
w ᵐᵏ⊩⋆ Ξ = All (w ᵐᵏ⊩_) Ξ


syn⋆ : ∀ {{𝔐 : 𝔎}} {w Ξ} → w ᵐᵏ⊩⋆ Ξ
                         → ᵐ⌊ w ⌋ ⁏ ∅ ⊢⋆ Ξ
syn⋆ mρ = mapAll syn mρ

sem⋆ : ∀ {{𝔐 : 𝔎}} {w Ξ} → w ᵐᵏ⊩⋆ Ξ
                         → w ᵏ⊩⋆ Ξ
sem⋆ mρ = mapAll sem mρ


-- Semantic entailment
infix 3 _⊨_
_⊨_ : 𝒞 → 𝒯 → Set₁
Δ ⁏ Γ ⊨ A = ∀ {{𝔐 : 𝔎}} {w} → w ᵐᵏ⊩⋆ Δ → w ᵏ⊩⋆ Γ
                             → w ᵏ⊩ A


-- Accessibility
mutual
  acc : ∀ {{𝔐 : 𝔎}} {A w w′} → w′ ≥ w → w ⊩ A
                             → w′ ⊩ A
  acc {ᵗᵛ x}  η M = accᵥ η M
  acc {A ⊃ B} η f = λ η′ → f (η ∘ₐ η′)
  acc {A ∧ B} η p = kacc {A} η (proj₁ p) , kacc {B} η (proj₂ p)
  acc {𝕋}     η t = tt
  acc {□ A}   η f = λ η′ → f (η ∘ₐ η′)

  kacc : ∀ {{𝔐 : 𝔎}} {A w w′} → w′ ≥ w → w ᵏ⊩ A
                              → w′ ᵏ⊩ A
  kacc η k = λ η′ f → k (η ∘ₐ η′) f

mkacc : ∀ {{𝔐 : 𝔎}} {A w w′} → w′ ≥ w → w ᵐᵏ⊩ A
                             → w′ ᵐᵏ⊩ A
mkacc {A} η (M , k) = mren ᵐ⌊ η ⌋ₐ M , kacc {A} η k


kacc⋆ : ∀ {{𝔐 : 𝔎}} {Ξ w w′} → w′ ≥ w → w ᵏ⊩⋆ Ξ
                             → w′ ᵏ⊩⋆ Ξ
-- TODO: Why does Agda require me to add seemingly unused annotations here?
-- kacc⋆ η rρ = mapAll (kacc η) rρ
kacc⋆ η rρ = mapAll (λ {A} k {_} {_} → kacc {A} η (k {_})) rρ

mkacc⋆ : ∀ {{𝔐 : 𝔎}} {Ξ w w′} → w′ ≥ w → w ᵐᵏ⊩⋆ Ξ
                              → w′ ᵐᵏ⊩⋆ Ξ
mkacc⋆ η mρ = mapAll (mkacc η) mρ


-- Kripke continuation monad
return : ∀ {{𝔐 : 𝔎}} {A w} → w ⊩ A
                           → w ᵏ⊩ A
return {A} a = λ η f →
                 f idₐ (acc {A} η a)

bind : ∀ {{𝔐 : 𝔎}} {A C w} → w ᵏ⊩ A → (∀ {w′} → w′ ≥ w → w′ ⊩ A
                                                 → w′ ᵏ⊩ C)
                           → w ᵏ⊩ C
bind k f = λ η f′ →
             k η (λ η′ a →
               f (η ∘ₐ η′) a idₐ (λ η″ b →
                 f′ (η′ ∘ₐ η″) b))


klookupₑ : ∀ {{𝔐 : 𝔎}} {Ξ A w} → w ᵏ⊩⋆ Ξ → Ξ ∋ A
                               → w ᵏ⊩ A
klookupₑ rρ i = lookupAll rρ i


kƛ : ∀ {{𝔐 : 𝔎}} {A B w} → (∀ {w′} → w′ ≥ w → w′ ᵏ⊩ A
                                    → w′ ᵏ⊩ B)
                         → w ᵏ⊩ A ⊃ B
kƛ {A} {B} f = return {A ⊃ B} (λ η k → f η k)

k$ : ∀ {{𝔐 : 𝔎}} {A B w} → w ᵏ⊩ A ⊃ B → w ᵏ⊩ A
                         → w ᵏ⊩ B
k$ {A} {B} k₁ k₂ = bind {A ⊃ B} {B} k₁ (λ η f → f idₐ (kacc {A} η k₂))

k, : ∀ {{𝔐 : 𝔎}} {A B w} → w ᵏ⊩ A → w ᵏ⊩ B
                         → w ᵏ⊩ A ∧ B
k, {A} {B} k₁ k₂ = return {A ∧ B} (k₁ , k₂)

kπ₁ : ∀ {{𝔐 : 𝔎}} {A B w} → w ᵏ⊩ A ∧ B
                          → w ᵏ⊩ A
kπ₁ {A} {B} k = bind {A ∧ B} {A} k (λ η p → proj₁ p)

kπ₂ : ∀ {{𝔐 : 𝔎}} {A B w} → w ᵏ⊩ A ∧ B
                          → w ᵏ⊩ B
kπ₂ {A} {B} k = bind {A ∧ B} {B} k (λ η p → proj₂ p)

ktt : ∀ {{𝔐 : 𝔎}} {w} → w ᵏ⊩ 𝕋
ktt = return {𝕋} tt

k⌜⌝ : ∀ {{𝔐 : 𝔎}} {A w} → (∀ {w′} → w′ ≥ w
                                   → w′ ᵐᵏ⊩ A)
                        → w ᵏ⊩ □ A
k⌜⌝ {A} f = return {□ A} (λ η → f η)

k⌞⌟ : ∀ {{𝔐 : 𝔎}} {A C w} → w ᵏ⊩ □ A
                          → (∀ {w′} → w′ ≥ w → w′ ᵐᵏ⊩ A
                                     → w′ ᵏ⊩ C)
                          → w ᵏ⊩ C
k⌞⌟ {A} {C} k f = bind {□ A} {C} k (λ η f′ → f η (f′ idₐ))


-- Soundness
-- ↓ : ∀ {Δ Γ A} → Δ ⁏ Γ ⊢ A
--               → Δ ⁏ Γ ⊨ A
-- ↓ (ᵐᵛ i)            mρ rρ = klookupₑ (sem⋆ mρ) i
-- ↓ (ʳᵛ i)            mρ rρ = klookupₑ rρ i
-- ↓ (ƛ {A} {B} M)     mρ rρ = kƛ {A} {B} (λ η k →
--                               ↓ M (mkacc⋆ η mρ) (kacc⋆ η rρ , k))
-- ↓ (_$_ {A} {B} M N) mρ rρ = k$ {A} {B} (↓ M mρ rρ) (↓ N mρ rρ)
-- ↓ (_,_ {A} {B} M N) mρ rρ = k, {A} {B} (↓ M mρ rρ) (↓ N mρ rρ)
-- ↓ (π₁ {A} {B} M)    mρ rρ = kπ₁ {A} {B} (↓ M mρ rρ)
-- ↓ (π₂ {A} {B} M)    mρ rρ = kπ₂ {A} {B} (↓ M mρ rρ)
-- ↓ tt                mρ rρ = ktt
-- ↓ (⌜_⌝ {A} M)       mρ rρ = k⌜⌝ {A} (λ η →
--                               msub (syn⋆ (mkacc⋆ η mρ)) M , ↓ M (mkacc⋆ η mρ) ∅)
-- ↓ (⌞_⌟ {A} {C} M N) mρ rρ = k⌞⌟ {A} {C} (↓ M mρ rρ) (λ η Mk →
--                               ↓ N (mkacc⋆ η mρ , Mk) (kacc⋆ η rρ))


-- Soundness, inlined
↓ : ∀ {Δ Γ A} → Δ ⁏ Γ ⊢ A
              → Δ ⁏ Γ ⊨ A
↓ (ᵐᵛ i)            mρ rρ = klookupₑ (sem⋆ mρ) i
↓ (ʳᵛ i)            mρ rρ = klookupₑ rρ i
↓ (ƛ {A} {B} M)     mρ rρ = return {A ⊃ B} (λ η k →
                              ↓ M (mkacc⋆ η mρ) (kacc⋆ η rρ , k))
↓ (_$_ {A} {B} M N) mρ rρ = bind {A ⊃ B} {B} (↓ M mρ rρ) (λ η f →
                              f idₐ (↓ N (mkacc⋆ η mρ) (kacc⋆ η rρ)))
↓ (_,_ {A} {B} M N) mρ rρ = return {A ∧ B} (↓ M mρ rρ , ↓ N mρ rρ)
↓ (π₁ {A} {B} M)    mρ rρ = bind {A ∧ B} {A} (↓ M mρ rρ) (λ η p → proj₁ p)
↓ (π₂ {A} {B} M)    mρ rρ = bind {A ∧ B} {B} (↓ M mρ rρ) (λ η p → proj₂ p)
↓ tt                mρ rρ = return {𝕋} tt
↓ (⌜_⌝ {A} M)       mρ rρ = return {□ A} (λ η →
                              msub (syn⋆ (mkacc⋆ η mρ)) M , ↓ M (mkacc⋆ η mρ) ∅)
↓ (⌞_⌟ {A} {C} M N) mρ rρ = bind {□ A} {C} (↓ M mρ rρ) (λ η f →
                              ↓ N (mkacc⋆ η mρ , f idₐ) (kacc⋆ η rρ))


--------------------------------------------------------------------------------
--
-- Completeness


-- Canonical model
instance
  𝔐ᶜ : 𝔎
  𝔐ᶜ = record
         { 𝒲    = 𝒞
         ; 𝒱    = λ { (Δ ⁏ Γ) x → Δ ⁏ Γ ⊢ₙₘ ᵗᵛ x }
         ; _≥_  = _⊇²_
         ; idₐ  = idᵣᵣ
         ; _∘ₐ_ = _∘ᵣᵣ_
         ; accᵥ = renₙₘ
         ; ⌊_⌋  = id
         ; ⌊_⌋ₐ = id
         }


-- Canonical soundness and completeness
mutual
  ↑ᶜ : ∀ {A Δ Γ} → Δ ⁏ Γ ᵏ⊩ A
                 → Δ ⁏ Γ ⊢ₙₘ A
  ↑ᶜ {ᵗᵛ x}  k = k idᵣᵣ (λ η M → M)
  ↑ᶜ {A ⊃ B} k = k idᵣᵣ (λ η f → ƛ (↑ᶜ (f (rwkᵣᵣ idᵣᵣ) (↓ᶜ (ʳᵛ zero)))))
  ↑ᶜ {A ∧ B} k = k idᵣᵣ (λ η p → ↑ᶜ (proj₁ p) , ↑ᶜ (proj₂ p))
  ↑ᶜ {𝕋}     k = k idᵣᵣ (λ η t → tt)
  ↑ᶜ {□ A}   k = k idᵣᵣ (λ η f → ⌜ syn (f idᵣᵣ) ⌝)

  ↓ᶜ : ∀ {A Δ Γ} → Δ ⁏ Γ ⊢ₙₜ A
                 → Δ ⁏ Γ ᵏ⊩ A
  ↓ᶜ {ᵗᵛ x}  M = return {ᵗᵛ x} (ⁿᵗ M)
  ↓ᶜ {A ⊃ B} M = return {A ⊃ B} (λ η k → ↓ᶜ (renₙₜ η M $ ↑ᶜ k))
  ↓ᶜ {A ∧ B} M = return {A ∧ B} (↓ᶜ (π₁ M) , ↓ᶜ (π₂ M))
  ↓ᶜ {𝕋}     M = return {𝕋} tt
  ↓ᶜ {□ A}   M = λ η f → ⌞ renₙₜ η M ⌟ (f (mwkᵣᵣ idᵣᵣ) (λ η′ →
                   ᵐᵛ (mlookupᵣᵣ η′ zero) , ↓ᶜ (ᵐᵛ (mlookupᵣᵣ η′ zero))))


mkidₑ : ∀ {Δ Γ} → Δ ⁏ Γ ᵐᵏ⊩⋆ Δ
mkidₑ {∅}     = ∅
mkidₑ {Δ , A} = mkacc⋆ (mwkᵣᵣ idᵣᵣ) mkidₑ , (ᵐᵛ zero , ↓ᶜ (ᵐᵛ zero))

kidₑ : ∀ {Γ Δ} → Δ ⁏ Γ ᵏ⊩⋆ Γ
kidₑ {∅}     = ∅
kidₑ {Γ , A} = kacc⋆ (rwkᵣᵣ idᵣᵣ) kidₑ , ↓ᶜ (ʳᵛ zero)


-- Completeness
↑ : ∀ {Δ Γ A} → Δ ⁏ Γ ⊨ A
              → Δ ⁏ Γ ⊢ₙₘ A
↑ 𝔞 = ↑ᶜ (𝔞 mkidₑ kidₑ)


-- Normalisation
nm : ∀ {Δ Γ A} → Δ ⁏ Γ ⊢ A
               → Δ ⁏ Γ ⊢ₙₘ A
nm = ↑ ∘ ↓


--------------------------------------------------------------------------------
--
-- Examples


ᵐᵛ0 : ∀ {Δ Γ A} → Δ , A ⁏ Γ ⊢ A
ᵐᵛ0 = ᵐᵛ zero

ᵐᵛ1 : ∀ {Δ Γ A B} → Δ , A , B ⁏ Γ ⊢ A
ᵐᵛ1 = ᵐᵛ (suc zero)

ᵐᵛ2 : ∀ {Δ Γ A B C} → Δ , A , B , C ⁏ Γ ⊢ A
ᵐᵛ2 = ᵐᵛ (suc (suc zero))


ʳᵛ0 : ∀ {Δ Γ A} → Δ ⁏ Γ , A ⊢ A
ʳᵛ0 = ʳᵛ zero

ʳᵛ1 : ∀ {Δ Γ A B} → Δ ⁏ Γ , A , B ⊢ A
ʳᵛ1 = ʳᵛ (suc zero)

ʳᵛ2 : ∀ {Δ Γ A B C} → Δ ⁏ Γ , A , B , C ⊢ A
ʳᵛ2 = ʳᵛ (suc (suc zero))


axI : ∀ {A Δ Γ}
    → Δ ⁏ Γ ⊢ A ⊃ A
axI = ƛ ʳᵛ0

axK : ∀ {A B Δ Γ}
    → Δ ⁏ Γ ⊢ A ⊃ B ⊃ A
axK = ƛ (ƛ ʳᵛ1)

axS : ∀ {A B C Δ Γ}
    → Δ ⁏ Γ ⊢ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
axS = ƛ (ƛ (ƛ ((ʳᵛ2 $ ʳᵛ0) $ (ʳᵛ1 $ ʳᵛ0))))


axD : ∀ {A B Δ Γ}
    → Δ ⁏ Γ ⊢ □ (A ⊃ B) ⊃ □ A ⊃ □ B
axD = ƛ (ƛ (⌞ ʳᵛ1 ⌟ (⌞ ʳᵛ0 ⌟ ⌜ ᵐᵛ1 $ ᵐᵛ0 ⌝)))

axT : ∀ {A Δ Γ}
    → Δ ⁏ Γ ⊢ □ A ⊃ A
axT = ƛ (⌞ ʳᵛ0 ⌟ ᵐᵛ0)

ax4 : ∀ {A Δ Γ}
    → Δ ⁏ Γ ⊢ □ A ⊃ □ □ A
ax4 = ƛ (⌞ ʳᵛ0 ⌟ ⌜ ⌜ ᵐᵛ0 ⌝ ⌝)


--------------------------------------------------------------------------------
--
-- Conversion tests


test∼ : ∀ {Δ Γ A} → Δ ⁏ Γ ⊢ A → Δ ⁏ Γ ⊢ A → Set
test∼ M₁ M₂ = embₙₘ (nm M₁) ≡ M₂


-- red⊃ : ∀ {Δ Γ A B} → (M : Δ ⁏ Γ , A ⊢ B) (N : Δ ⁏ Γ ⊢ A)
--                    → ƛ M $ N ∼ rsub (ridₛ , N) M

test∼red⊃ : test∼ {∅} {∅ , "A"}
                  ((ƛ ʳᵛ0) $ ʳᵛ0)
                  ʳᵛ0
test∼red⊃ = refl


-- red∧₁ : ∀ {Δ Γ A B} → (M : Δ ⁏ Γ ⊢ A) (N : Δ ⁏ Γ ⊢ B)
--                     → π₁ (M , N) ∼ M

test∼red∧₁ : test∼ {∅} {∅ , "A" , "B"}
                   (π₁ (ʳᵛ1 , ʳᵛ0))
                   ʳᵛ1
test∼red∧₁ = refl


-- red∧₂ : ∀ {Δ Γ A B} → (M : Δ ⁏ Γ ⊢ A) (N : Δ ⁏ Γ ⊢ B)
--                     → π₂ (M , N) ∼ N

test∼red∧₂ : test∼ {∅} {∅ , "A" , "B"}
                   (π₂ (ʳᵛ1 , ʳᵛ0))
                   ʳᵛ0
test∼red∧₂ = refl


-- red□ : ∀ {Δ Γ A C} → (M : Δ ⁏ ∅ ⊢ A) (N : Δ , A ⁏ Γ ⊢ C)
--                    → ⌞ ⌜ M ⌝ ⌟ N ∼ msub (midₛ , M) N

test∼red□ : test∼ {∅ , "A"} {∅}
                  (⌞ ⌜ ᵐᵛ0 ⌝ ⌟ ᵐᵛ0)
                  ᵐᵛ0
test∼red□ = refl


-- exp⊃ : ∀ {Δ Γ A B} → (M : Δ ⁏ Γ ⊢ A ⊃ B)
--                    → M ∼ ƛ (rren (wkᵣ idᵣ) M $ ʳᵛ0)

test∼exp⊃ : test∼ {∅} {∅ , "A" ⊃ "B"}
                  ʳᵛ0
                  (ƛ (rren (wkᵣ idᵣ) ʳᵛ0 $ ʳᵛ0))
test∼exp⊃ = refl


-- exp∧ : ∀ {Δ Γ A B} → (M : Δ ⁏ Γ ⊢ A ∧ B)
--                    → M ∼ π₁ M , π₂ M

test∼exp∧ : test∼ {∅} {∅ , "A" ∧ "B"}
                  ʳᵛ0
                  (π₁ ʳᵛ0 , π₂ ʳᵛ0)
test∼exp∧ = refl


-- exp𝕋 : ∀ {Δ Γ} → (M : Δ ⁏ Γ ⊢ 𝕋)
--                → M ∼ tt

test∼exp𝕋 : test∼ {∅} {∅ , 𝕋}
                  ʳᵛ0
                  tt
test∼exp𝕋 = refl


-- exp□ : ∀ {Δ Γ} → (M : Δ ⁏ Γ ⊢ □ A)
--                → M ∼ ⌞ M ⌟ ⌜ ᵐᵛ0 ⌝

test∼exp□ : test∼ {∅} {∅ , □ "A"}
                  ʳᵛ0
                  (⌞ ʳᵛ0 ⌟ ⌜ ᵐᵛ0 ⌝)
test∼exp□ = refl


-- comm□$ : ∀ {Δ Γ A B} → (K : Δ ⁏ Γ ⊢ □ (A ⊃ B))
--                         (M : Δ , A ⊃ B ⁏ Γ ⊢ A ⊃ B) (N : Δ ⁏ Γ ⊢ A)
--                      → (⌞ K ⌟ M) $ N ∼ ⌞ K ⌟ (M $ (mren (wkᵣ idᵣ) N))

test∼comm□$ : test∼ {∅} {∅ , □ ("A" ⊃ "B") , "A"}
                    ((⌞ ʳᵛ1 ⌟ ᵐᵛ0) $ ʳᵛ0)
                    (⌞ ʳᵛ1 ⌟ (ᵐᵛ0 $ mren (wkᵣ idᵣ) ʳᵛ0))
test∼comm□$ = refl


-- comm□⌞⌟ : ∀ {Δ Γ A C} → (K : Δ ⁏ Γ ⊢ □ □ A)
--                          (M : Δ , □ A ⁏ Γ ⊢ □ A) (N : Δ , A ⁏ Γ ⊢ C)
--                       → ⌞ (⌞ K ⌟ M) ⌟ N ∼ ⌞ K ⌟ (⌞ M ⌟ (mren (wkᵣ idᵣ) N))

test∼comm□⌞⌟ : test∼ {∅} {∅ , □ □ "A"}
                     (⌞ ⌞ ʳᵛ0 ⌟ ᵐᵛ0 ⌟ ᵐᵛ0)
                     (⌞ ʳᵛ0 ⌟ (⌞ ᵐᵛ0 ⌟ ᵐᵛ0))
test∼comm□⌞⌟ = refl


-- comm□π₁ : ∀ {Δ Γ A B} → (K : Δ ⁏ Γ ⊢ □ (A ∧ B))
--                          (M : Δ , A ∧ B ⁏ Γ ⊢ A ∧ B)
--                       → π₁ (⌞ K ⌟ M) ∼ ⌞ K ⌟ (π₁ M)

test∼comm□π₁ : test∼ {∅} {∅ , □ ("A" ∧ "B")}
                     (π₁ (⌞ ʳᵛ0 ⌟ ᵐᵛ0))
                     (⌞ ʳᵛ0 ⌟ (π₁ ᵐᵛ0))
test∼comm□π₁ = refl


-- comm□π₂ : ∀ {Δ Γ A B} → (K : Δ ⁏ Γ ⊢ □ (A ∧ B))
--                          (M : Δ , A ∧ B ⁏ Γ ⊢ A ∧ B)
--                       → π₂ (⌞ K ⌟ M) ∼ ⌞ K ⌟ (π₂ M)

test∼comm□π₂ : test∼ {∅} {∅ , □ ("A" ∧ "B")}
                     (π₂ (⌞ ʳᵛ0 ⌟ ᵐᵛ0))
                     (⌞ ʳᵛ0 ⌟ (π₂ ᵐᵛ0))
test∼comm□π₂ = refl


--------------------------------------------------------------------------------
--
-- Self-interpretation


-- weakBP : ∀ {Δ Γ A B} → (M : Δ ⁏ Γ ⊢ A)
--                      → 𝕋 $ ⌜ M ⌝ ∼ ⌜ M ⌝

test∼weakBP : test∼ {∅ , "A"} {∅}
                    (axT $ ⌜ ᵐᵛ0 ⌝)
                    ᵐᵛ0
test∼weakBP = refl


-- Andrej : ∀ {Δ Γ A B} → (M : Δ ⁏ Γ ⊢ A ⊃ B) (N : Δ ⁏ Γ ⊢ A)
--                      → (𝔻 $ ⌜ M ⌝) $ ⌜ N ⌝ ∼ ⌜ M $ N ⌝

test∼Andrej : test∼ {∅ , "A" ⊃ "B" , "A"} {∅}
                    ((axD $ ⌜ ᵐᵛ1 ⌝) $ ⌜ ᵐᵛ0 ⌝)
                    (⌜ ᵐᵛ1 $ ᵐᵛ0 ⌝)
test∼Andrej = refl


--------------------------------------------------------------------------------
