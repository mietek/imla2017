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
data Tp : Set where
  ᵗᵛ  : (x : TVar) → Tp
  _⊃_ : (A B : Tp) → Tp
  _∧_ : (A B : Tp) → Tp
  𝕋   : Tp
  □_  : (A : Tp) → Tp

instance
  typeIsString : IsString Tp
  typeIsString =
    record
      { Constraint = λ s → ⊤
      ; fromString = λ s → ᵗᵛ (tvar s)
      }


-- Contexts
Cx : Set
Cx = List² Tp Tp


-- Syntactic entailment
infix 3 _⊢_
data _⊢_ : Cx → Tp → Set
  where
    ᵐᵛ  : ∀ {A Δ Γ} → (i : Δ ∋ A)
                    → Δ ⁏ Γ ⊢ A

    ʳᵛ  : ∀ {A Δ Γ} → (i : Γ ∋ A)
                    → Δ ⁏ Γ ⊢ A

    ƛ   : ∀ {A B Δ Γ} → (𝒟 : Δ ⁏ Γ , A ⊢ B)
                      → Δ ⁏ Γ ⊢ A ⊃ B

    _$_ : ∀ {A B Δ Γ} → (𝒟 : Δ ⁏ Γ ⊢ A ⊃ B) (ℰ : Δ ⁏ Γ ⊢ A)
                      → Δ ⁏ Γ ⊢ B

    _,_ : ∀ {A B Δ Γ} → (𝒟 : Δ ⁏ Γ ⊢ A) (ℰ : Δ ⁏ Γ ⊢ B)
                      → Δ ⁏ Γ ⊢ A ∧ B

    π₁  : ∀ {A B Δ Γ} → (𝒟 : Δ ⁏ Γ ⊢ A ∧ B)
                      → Δ ⁏ Γ ⊢ A

    π₂  : ∀ {A B Δ Γ} → (𝒟 : Δ ⁏ Γ ⊢ A ∧ B)
                      → Δ ⁏ Γ ⊢ B

    tt  : ∀ {Δ Γ} → Δ ⁏ Γ ⊢ 𝕋

    ⌜_⌝ : ∀ {A Δ Γ} → (𝒟 : Δ ⁏ ∅ ⊢ A)
                    → Δ ⁏ Γ ⊢ □ A

    ⌞_⌟ : ∀ {A C Δ Γ} → (𝒟 : Δ ⁏ Γ ⊢ □ A) (ℰ : Δ , A ⁏ Γ ⊢ C)
                      → Δ ⁏ Γ ⊢ C


-- Normal and neutral forms
mutual
  infix 3 _⊢ₙₘ_
  data _⊢ₙₘ_ : Cx → Tp → Set
    where
      ƛ   : ∀ {A B Δ Γ} → (𝒟 : Δ ⁏ Γ , A ⊢ₙₘ B)
                        → Δ ⁏ Γ ⊢ₙₘ A ⊃ B

      _,_ : ∀ {A B Δ Γ} → (𝒟 : Δ ⁏ Γ ⊢ₙₘ A) (ℰ : Δ ⁏ Γ ⊢ₙₘ B)
                        → Δ ⁏ Γ ⊢ₙₘ A ∧ B

      tt  : ∀ {Δ Γ} → Δ ⁏ Γ ⊢ₙₘ 𝕋

      ⌜_⌝ : ∀ {A Δ Γ} → (𝒟 : Δ ⁏ ∅ ⊢ A)
                      → Δ ⁏ Γ ⊢ₙₘ □ A

      ⌞_⌟ : ∀ {A C Δ Γ} → (𝒟 : Δ ⁏ Γ ⊢ₙₜ □ A) (ℰ : Δ , A ⁏ Γ ⊢ₙₘ C)
                        → Δ ⁏ Γ ⊢ₙₘ C

      ⁿᵗ  : ∀ {x Δ Γ} → (𝒟 : Δ ⁏ Γ ⊢ₙₜ ᵗᵛ x)
                      → Δ ⁏ Γ ⊢ₙₘ ᵗᵛ x

  infix 3 _⊢ₙₜ_
  data _⊢ₙₜ_ : Cx → Tp → Set
    where
      ᵐᵛ  : ∀ {A Δ Γ} → (i : Δ ∋ A)
                      → Δ ⁏ Γ ⊢ₙₜ A

      ʳᵛ  : ∀ {A Δ Γ} → (i : Γ ∋ A)
                      → Δ ⁏ Γ ⊢ₙₜ A

      _$_ : ∀ {A B Δ Γ} → (𝒟 : Δ ⁏ Γ ⊢ₙₜ A ⊃ B) (ℰ : Δ ⁏ Γ ⊢ₙₘ A)
                        → Δ ⁏ Γ ⊢ₙₜ B

      π₁  : ∀ {A B Δ Γ} → (𝒟 : Δ ⁏ Γ ⊢ₙₜ A ∧ B)
                        → Δ ⁏ Γ ⊢ₙₜ A

      π₂  : ∀ {A B Δ Γ} → (𝒟 : Δ ⁏ Γ ⊢ₙₜ A ∧ B)
                        → Δ ⁏ Γ ⊢ₙₜ B


mutual
  embₙₘ : ∀ {Δ Γ A} → Δ ⁏ Γ ⊢ₙₘ A → Δ ⁏ Γ ⊢ A
  embₙₘ (ƛ 𝒟)     = ƛ (embₙₘ 𝒟)
  embₙₘ (𝒟 , ℰ)   = embₙₘ 𝒟 , embₙₘ ℰ
  embₙₘ tt        = tt
  embₙₘ (⌜ 𝒟 ⌝)   = ⌜ 𝒟 ⌝
  embₙₘ (⌞ 𝒟 ⌟ ℰ) = ⌞ embₙₜ 𝒟 ⌟ (embₙₘ ℰ)
  embₙₘ (ⁿᵗ 𝒟)    = embₙₜ 𝒟

  embₙₜ : ∀ {Δ Γ A} → Δ ⁏ Γ ⊢ₙₜ A → Δ ⁏ Γ ⊢ A
  embₙₜ (ᵐᵛ i)  = ᵐᵛ i
  embₙₜ (ʳᵛ i)  = ʳᵛ i
  embₙₜ (𝒟 $ ℰ) = embₙₜ 𝒟 $ embₙₘ ℰ
  embₙₜ (π₁ 𝒟)  = π₁ (embₙₜ 𝒟)
  embₙₜ (π₂ 𝒟)  = π₂ (embₙₜ 𝒟)


--------------------------------------------------------------------------------
--
-- Renaming


mren : ∀ {Δ Δ′ Γ A} → Δ′ ⊇ Δ → Δ ⁏ Γ ⊢ A
                    → Δ′ ⁏ Γ ⊢ A
mren η (ᵐᵛ i)    = ᵐᵛ (lookupᵣ η i)
mren η (ʳᵛ i)    = ʳᵛ i
mren η (ƛ 𝒟)     = ƛ (mren η 𝒟)
mren η (𝒟 $ ℰ)   = mren η 𝒟 $ mren η ℰ
mren η (𝒟 , ℰ)   = mren η 𝒟 , mren η ℰ
mren η (π₁ 𝒟)    = π₁ (mren η 𝒟)
mren η (π₂ 𝒟)    = π₂ (mren η 𝒟)
mren η tt        = tt
mren η (⌜ 𝒟 ⌝)   = ⌜ mren η 𝒟 ⌝
mren η (⌞ 𝒟 ⌟ ℰ) = ⌞ mren η 𝒟 ⌟ (mren (liftᵣ η) ℰ)

rren : ∀ {Δ Γ Γ′ A} → Γ′ ⊇ Γ → Δ ⁏ Γ ⊢ A
                    → Δ ⁏ Γ′ ⊢ A
rren η (ᵐᵛ i)    = ᵐᵛ i
rren η (ʳᵛ i)    = ʳᵛ (lookupᵣ η i)
rren η (ƛ 𝒟)     = ƛ (rren (liftᵣ η) 𝒟)
rren η (𝒟 $ ℰ)   = rren η 𝒟 $ rren η ℰ
rren η (𝒟 , ℰ)   = rren η 𝒟 , rren η ℰ
rren η (π₁ 𝒟)    = π₁ (rren η 𝒟)
rren η (π₂ 𝒟)    = π₂ (rren η 𝒟)
rren η tt        = tt
rren η (⌜ 𝒟 ⌝)   = ⌜ 𝒟 ⌝
rren η (⌞ 𝒟 ⌟ ℰ) = ⌞ rren η 𝒟 ⌟ (rren η ℰ)


mutual
  mrenₙₘ : ∀ {Δ Δ′ Γ A} → Δ′ ⊇ Δ → Δ ⁏ Γ ⊢ₙₘ A
                        → Δ′ ⁏ Γ ⊢ₙₘ A
  mrenₙₘ η (ƛ 𝒟)     = ƛ (mrenₙₘ η 𝒟)
  mrenₙₘ η (𝒟 , ℰ)   = mrenₙₘ η 𝒟 , mrenₙₘ η ℰ
  mrenₙₘ η tt        = tt
  mrenₙₘ η (⌜ 𝒟 ⌝)   = ⌜ mren η 𝒟 ⌝
  mrenₙₘ η (⌞ 𝒟 ⌟ ℰ) = ⌞ mrenₙₜ η 𝒟 ⌟ (mrenₙₘ (liftᵣ η) ℰ)
  mrenₙₘ η (ⁿᵗ 𝒟)    = ⁿᵗ (mrenₙₜ η 𝒟)

  mrenₙₜ : ∀ {Δ Δ′ Γ A} → Δ′ ⊇ Δ → Δ ⁏ Γ ⊢ₙₜ A
                        → Δ′ ⁏ Γ ⊢ₙₜ A
  mrenₙₜ η (ᵐᵛ i)  = ᵐᵛ (lookupᵣ η i)
  mrenₙₜ η (ʳᵛ i ) = ʳᵛ i
  mrenₙₜ η (𝒟 $ ℰ) = mrenₙₜ η 𝒟 $ mrenₙₘ η ℰ
  mrenₙₜ η (π₁ 𝒟)  = π₁ (mrenₙₜ η 𝒟)
  mrenₙₜ η (π₂ 𝒟)  = π₂ (mrenₙₜ η 𝒟)


mutual
  rrenₙₘ : ∀ {Δ Γ Γ′ A} → Γ′ ⊇ Γ → Δ ⁏ Γ ⊢ₙₘ A
                        → Δ ⁏ Γ′ ⊢ₙₘ A
  rrenₙₘ η (ƛ 𝒟)     = ƛ (rrenₙₘ (liftᵣ η) 𝒟)
  rrenₙₘ η (𝒟 , ℰ)   = rrenₙₘ η 𝒟 , rrenₙₘ η ℰ
  rrenₙₘ η tt        = tt
  rrenₙₘ η (⌜ 𝒟 ⌝)   = ⌜ 𝒟 ⌝
  rrenₙₘ η (⌞ 𝒟 ⌟ ℰ) = ⌞ rrenₙₜ η 𝒟 ⌟ (rrenₙₘ η ℰ)
  rrenₙₘ η (ⁿᵗ 𝒟)    = ⁿᵗ (rrenₙₜ η 𝒟)

  rrenₙₜ : ∀ {Δ Γ Γ′ A} → Γ′ ⊇ Γ → Δ ⁏ Γ ⊢ₙₜ A
                        → Δ ⁏ Γ′ ⊢ₙₜ A
  rrenₙₜ η (ᵐᵛ i)  = ᵐᵛ i
  rrenₙₜ η (ʳᵛ i)  = ʳᵛ (lookupᵣ η i)
  rrenₙₜ η (𝒟 $ ℰ) = rrenₙₜ η 𝒟 $ rrenₙₘ η ℰ
  rrenₙₜ η (π₁ 𝒟)  = π₁ (rrenₙₜ η 𝒟)
  rrenₙₜ η (π₂ 𝒟)  = π₂ (rrenₙₜ η 𝒟)


renₙₘ : ∀ {Δ Δ′ Γ Γ′ A} → Δ′ ⁏ Γ′ ⊇² Δ ⁏ Γ → Δ ⁏ Γ ⊢ₙₘ A
                        → Δ′ ⁏ Γ′ ⊢ₙₘ A
renₙₘ η 𝒟 = (mrenₙₘ (proj₁ η) ∘ rrenₙₘ (proj₂ η)) 𝒟

renₙₜ : ∀ {Δ Δ′ Γ Γ′ A} → Δ′ ⁏ Γ′ ⊇² Δ ⁏ Γ → Δ ⁏ Γ ⊢ₙₜ A
                        → Δ′ ⁏ Γ′ ⊢ₙₜ A
renₙₜ η 𝒟 = (mrenₙₜ (proj₁ η) ∘ rrenₙₜ (proj₂ η)) 𝒟


--------------------------------------------------------------------------------
--
-- Substitution


-- Simultaneous substitutions
infix 3 _⊢⋆_
_⊢⋆_ : Cx → List Tp → Set
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
msub σ (ƛ 𝒟)     = ƛ (msub σ 𝒟)
msub σ (𝒟 $ ℰ)   = msub σ 𝒟 $ msub σ ℰ
msub η (𝒟 , ℰ)   = msub η 𝒟 , msub η ℰ
msub η (π₁ 𝒟)    = π₁ (msub η 𝒟)
msub η (π₂ 𝒟)    = π₂ (msub η 𝒟)
msub η tt        = tt
msub σ ⌜ 𝒟 ⌝     = ⌜ msub σ 𝒟 ⌝
msub σ (⌞ 𝒟 ⌟ ℰ) = ⌞ msub σ 𝒟 ⌟ (msub (mliftₛ σ) ℰ)

rsub : ∀ {Δ Γ Ξ A} → Δ ⁏ Γ ⊢⋆ Ξ → Δ ⁏ Ξ ⊢ A
                   → Δ ⁏ Γ ⊢ A
rsub σ (ᵐᵛ i)    = ᵐᵛ i
rsub σ (ʳᵛ i)    = lookupₛ σ i
rsub σ (ƛ 𝒟)     = ƛ (rsub (rliftₛ σ) 𝒟)
rsub σ (𝒟 $ ℰ)   = rsub σ 𝒟 $ rsub σ ℰ
rsub η (𝒟 , ℰ)   = rsub η 𝒟 , rsub η ℰ
rsub η (π₁ 𝒟)    = π₁ (rsub η 𝒟)
rsub η (π₂ 𝒟)    = π₂ (rsub η 𝒟)
rsub η tt        = tt
rsub σ ⌜ 𝒟 ⌝     = ⌜ 𝒟 ⌝
rsub σ (⌞ 𝒟 ⌟ ℰ) = ⌞ rsub σ 𝒟 ⌟ (rsub (mwkₛ σ) ℰ)


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

    ⌊_⌋  : 𝒲 → Cx

    ⌊_⌋ₐ : ∀ {w w′} → w′ ≥ w
                    → ⌊ w′ ⌋ ⊇² ⌊ w ⌋

open 𝔎 {{…}} public


ᵐ⌊_⌋ : ∀ {{𝔐 : 𝔎}} → 𝒲 → List Tp
ᵐ⌊ w ⌋ = proj₁ ⌊ w ⌋

ʳ⌊_⌋ : ∀ {{𝔐 : 𝔎}} → 𝒲 → List Tp
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
  _⊩_ : ∀ {{𝔐 : 𝔎}} → 𝒲 → Tp → Set

  w ⊩ ᵗᵛ x  = 𝒱 w x

  w ⊩ A ⊃ B = ∀ {w′} → (η : w′ ≥ w) (k : w′ ᵏ⊩ A)
                      → w′ ᵏ⊩ B

  w ⊩ A ∧ B = w ᵏ⊩ A × w ᵏ⊩ B

  w ⊩ 𝕋     = ⊤

  w ⊩ □ A   = ∀ {w′} → (η : w′ ≥ w)
                      → w′ ᵐᵏ⊩ A

  infix 3 _ᵏ⊩_
  _ᵏ⊩_ : ∀ {{𝔐 : 𝔎}} → 𝒲 → Tp → Set
  w ᵏ⊩ A = ∀ {w′ C} → (η : w′ ≥ w) (f : ∀ {w″} → w″ ≥ w′ → w″ ⊩ A
                                                 → ⌊ w″ ⌋ ⊢ₙₘ C)
                     → ⌊ w′ ⌋ ⊢ₙₘ C

  infix 3 _ᵐᵏ⊩_
  _ᵐᵏ⊩_ : ∀ {{𝔐 : 𝔎}} → 𝒲 → Tp → Set
  w ᵐᵏ⊩ A = ᵐ⌊ w ⌋ ⁏ ∅ ⊢ A × w ᵏ⊩ A


syn : ∀ {{𝔐 : 𝔎}} {w A} → w ᵐᵏ⊩ A
                        → ᵐ⌊ w ⌋ ⁏ ∅ ⊢ A
syn 𝒟k = proj₁ 𝒟k

sem : ∀ {{𝔐 : 𝔎}} {w A} → w ᵐᵏ⊩ A
                        → w ᵏ⊩ A
sem 𝒟k = proj₂ 𝒟k


-- Environments
infix 3 _ᵏ⊩⋆_
_ᵏ⊩⋆_ : ∀ {{𝔐 : 𝔎}} → 𝒲 → List Tp → Set
w ᵏ⊩⋆ Ξ = All (w ᵏ⊩_) Ξ

infix 3 _ᵐᵏ⊩⋆_
_ᵐᵏ⊩⋆_ : ∀ {{𝔐 : 𝔎}} → 𝒲 → List Tp → Set
w ᵐᵏ⊩⋆ Ξ = All (w ᵐᵏ⊩_) Ξ


syn⋆ : ∀ {{𝔐 : 𝔎}} {w Ξ} → w ᵐᵏ⊩⋆ Ξ
                         → ᵐ⌊ w ⌋ ⁏ ∅ ⊢⋆ Ξ
syn⋆ mρ = mapAll syn mρ

sem⋆ : ∀ {{𝔐 : 𝔎}} {w Ξ} → w ᵐᵏ⊩⋆ Ξ
                         → w ᵏ⊩⋆ Ξ
sem⋆ mρ = mapAll sem mρ


-- Semantic entailment
infix 3 _⊨_
_⊨_ : Cx → Tp → Set₁
Δ ⁏ Γ ⊨ A = ∀ {{𝔐 : 𝔎}} {w} → w ᵐᵏ⊩⋆ Δ → w ᵏ⊩⋆ Γ
                             → w ᵏ⊩ A


-- Accessibility
mutual
  acc : ∀ {{𝔐 : 𝔎}} {A w w′} → w′ ≥ w → w ⊩ A
                             → w′ ⊩ A
  acc {ᵗᵛ x}  η 𝒟 = accᵥ η 𝒟
  acc {A ⊃ B} η f = λ η′ → f (η ∘ₐ η′)
  acc {A ∧ B} η p = kacc {A} η (proj₁ p) , kacc {B} η (proj₂ p)
  acc {𝕋}     η t = tt
  acc {□ A}   η f = λ η′ → f (η ∘ₐ η′)

  kacc : ∀ {{𝔐 : 𝔎}} {A w w′} → w′ ≥ w → w ᵏ⊩ A
                              → w′ ᵏ⊩ A
  kacc η k = λ η′ f → k (η ∘ₐ η′) f

mkacc : ∀ {{𝔐 : 𝔎}} {A w w′} → w′ ≥ w → w ᵐᵏ⊩ A
                             → w′ ᵐᵏ⊩ A
mkacc {A} η (𝒟 , k) = mren ᵐ⌊ η ⌋ₐ 𝒟 , kacc {A} η k


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
-- ↓ (ƛ {A} {B} 𝒟)     mρ rρ = kƛ {A} {B} (λ η k →
--                               ↓ 𝒟 (mkacc⋆ η mρ) (kacc⋆ η rρ , k))
-- ↓ (_$_ {A} {B} 𝒟 ℰ) mρ rρ = k$ {A} {B} (↓ 𝒟 mρ rρ) (↓ ℰ mρ rρ)
-- ↓ (_,_ {A} {B} 𝒟 ℰ) mρ rρ = k, {A} {B} (↓ 𝒟 mρ rρ) (↓ ℰ mρ rρ)
-- ↓ (π₁ {A} {B} 𝒟)    mρ rρ = kπ₁ {A} {B} (↓ 𝒟 mρ rρ)
-- ↓ (π₂ {A} {B} 𝒟)    mρ rρ = kπ₂ {A} {B} (↓ 𝒟 mρ rρ)
-- ↓ tt                mρ rρ = ktt
-- ↓ (⌜_⌝ {A} 𝒟)       mρ rρ = k⌜⌝ {A} (λ η →
--                               msub (syn⋆ (mkacc⋆ η mρ)) 𝒟 , ↓ 𝒟 (mkacc⋆ η mρ) ∅)
-- ↓ (⌞_⌟ {A} {C} 𝒟 ℰ) mρ rρ = k⌞⌟ {A} {C} (↓ 𝒟 mρ rρ) (λ η 𝒟k →
--                               ↓ ℰ (mkacc⋆ η mρ , 𝒟k) (kacc⋆ η rρ))


-- Soundness, inlined
↓ : ∀ {Δ Γ A} → Δ ⁏ Γ ⊢ A
              → Δ ⁏ Γ ⊨ A
↓ (ᵐᵛ i)            mρ rρ = klookupₑ (sem⋆ mρ) i
↓ (ʳᵛ i)            mρ rρ = klookupₑ rρ i
↓ (ƛ {A} {B} 𝒟)     mρ rρ = return {A ⊃ B} (λ η k →
                              ↓ 𝒟 (mkacc⋆ η mρ) (kacc⋆ η rρ , k))
↓ (_$_ {A} {B} 𝒟 ℰ) mρ rρ = bind {A ⊃ B} {B} (↓ 𝒟 mρ rρ) (λ η f →
                              f idₐ (↓ ℰ (mkacc⋆ η mρ) (kacc⋆ η rρ)))
↓ (_,_ {A} {B} 𝒟 ℰ) mρ rρ = return {A ∧ B} (↓ 𝒟 mρ rρ , ↓ ℰ mρ rρ)
↓ (π₁ {A} {B} 𝒟)    mρ rρ = bind {A ∧ B} {A} (↓ 𝒟 mρ rρ) (λ η p → proj₁ p)
↓ (π₂ {A} {B} 𝒟)    mρ rρ = bind {A ∧ B} {B} (↓ 𝒟 mρ rρ) (λ η p → proj₂ p)
↓ tt                mρ rρ = return {𝕋} tt
↓ (⌜_⌝ {A} 𝒟)       mρ rρ = return {□ A} (λ η →
                              msub (syn⋆ (mkacc⋆ η mρ)) 𝒟 , ↓ 𝒟 (mkacc⋆ η mρ) ∅)
↓ (⌞_⌟ {A} {C} 𝒟 ℰ) mρ rρ = bind {□ A} {C} (↓ 𝒟 mρ rρ) (λ η f →
                              ↓ ℰ (mkacc⋆ η mρ , f idₐ) (kacc⋆ η rρ))


--------------------------------------------------------------------------------
--
-- Completeness


-- Universal model
instance
  𝔐ᵤ : 𝔎
  𝔐ᵤ = record
         { 𝒲    = Cx
         ; 𝒱    = λ { (Δ ⁏ Γ) x → Δ ⁏ Γ ⊢ₙₘ ᵗᵛ x }
         ; _≥_  = _⊇²_
         ; idₐ  = idᵣ²
         ; _∘ₐ_ = _∘ᵣ²_
         ; accᵥ = renₙₘ
         ; ⌊_⌋  = id
         ; ⌊_⌋ₐ = id
         }


-- Soundness and completeness with respect to the universal model
mutual
  ↑ᵤ : ∀ {A Δ Γ} → Δ ⁏ Γ ᵏ⊩ A
                 → Δ ⁏ Γ ⊢ₙₘ A
  ↑ᵤ {ᵗᵛ x}  k = k idᵣ² (λ η 𝒟 → 𝒟)
  ↑ᵤ {A ⊃ B} k = k idᵣ² (λ η f → ƛ (↑ᵤ (f (rwkᵣ idᵣ²) (↓ᵤ (ʳᵛ zero)))))
  ↑ᵤ {A ∧ B} k = k idᵣ² (λ η p → ↑ᵤ (proj₁ p) , ↑ᵤ (proj₂ p))
  ↑ᵤ {𝕋}     k = k idᵣ² (λ η t → tt)
  ↑ᵤ {□ A}   k = k idᵣ² (λ η f → ⌜ syn (f idᵣ²) ⌝)

  ↓ᵤ : ∀ {A Δ Γ} → Δ ⁏ Γ ⊢ₙₜ A
                 → Δ ⁏ Γ ᵏ⊩ A
  ↓ᵤ {ᵗᵛ x}  𝒟 = return {ᵗᵛ x} (ⁿᵗ 𝒟)
  ↓ᵤ {A ⊃ B} 𝒟 = return {A ⊃ B} (λ η k → ↓ᵤ (renₙₜ η 𝒟 $ ↑ᵤ k))
  ↓ᵤ {A ∧ B} 𝒟 = return {A ∧ B} (↓ᵤ (π₁ 𝒟) , ↓ᵤ (π₂ 𝒟))
  ↓ᵤ {𝕋}     𝒟 = return {𝕋} tt
  ↓ᵤ {□ A}   𝒟 = λ η f → ⌞ renₙₜ η 𝒟 ⌟ (f (mwkᵣ idᵣ²) (λ η′ →
                   ᵐᵛ (mlookupᵣ η′ zero) , ↓ᵤ (ᵐᵛ (mlookupᵣ η′ zero))))


mkidₑ : ∀ {Δ Γ} → Δ ⁏ Γ ᵐᵏ⊩⋆ Δ
mkidₑ {∅}     = ∅
mkidₑ {Δ , A} = mkacc⋆ (mwkᵣ idᵣ²) mkidₑ , (ᵐᵛ zero , ↓ᵤ (ᵐᵛ zero))

kidₑ : ∀ {Γ Δ} → Δ ⁏ Γ ᵏ⊩⋆ Γ
kidₑ {∅}     = ∅
kidₑ {Γ , A} = kacc⋆ (rwkᵣ idᵣ²) kidₑ , ↓ᵤ (ʳᵛ zero)


-- Completeness
↑ : ∀ {Δ Γ A} → Δ ⁏ Γ ⊨ A
              → Δ ⁏ Γ ⊢ₙₘ A
↑ f = ↑ᵤ (f mkidₑ kidₑ)


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


axI : ∀ {A Δ Γ} → Δ ⁏ Γ ⊢ A ⊃ A
axI = ƛ ʳᵛ0

axK : ∀ {A B Δ Γ} → Δ ⁏ Γ ⊢ A ⊃ B ⊃ A
axK = ƛ (ƛ ʳᵛ1)

axS : ∀ {A B C Δ Γ} → Δ ⁏ Γ ⊢ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
axS = ƛ (ƛ (ƛ ((ʳᵛ2 $ ʳᵛ0) $ (ʳᵛ1 $ ʳᵛ0))))


axD : ∀ {A B Δ Γ} → Δ ⁏ Γ ⊢ □ (A ⊃ B) ⊃ □ A ⊃ □ B
axD = ƛ (ƛ (⌞ ʳᵛ1 ⌟ (⌞ ʳᵛ0 ⌟ ⌜ ᵐᵛ1 $ ᵐᵛ0 ⌝)))

axT : ∀ {A Δ Γ} → Δ ⁏ Γ ⊢ □ A ⊃ A
axT = ƛ (⌞ ʳᵛ0 ⌟ ᵐᵛ0)

ax4 : ∀ {A Δ Γ} → Δ ⁏ Γ ⊢ □ A ⊃ □ □ A
ax4 = ƛ (⌞ ʳᵛ0 ⌟ ⌜ ⌜ ᵐᵛ0 ⌝ ⌝)


--------------------------------------------------------------------------------
--
-- Conversion tests


test∼ : ∀ {Δ Γ A} → Δ ⁏ Γ ⊢ A → Δ ⁏ Γ ⊢ A → Set
test∼ 𝒟₁ 𝒟₂ = embₙₘ (nm 𝒟₁) ≡ 𝒟₂


-- red⊃ : ∀ {Δ Γ A B} → (𝒟 : Δ ⁏ Γ , A ⊢ B) (ℰ : Δ ⁏ Γ ⊢ A)
--                    → ƛ 𝒟 $ ℰ ∼ rsub (ridₛ , ℰ) 𝒟

test∼red⊃ : test∼ {∅} {∅ , "A"}
                  ((ƛ ʳᵛ0) $ ʳᵛ0)
                  ʳᵛ0
test∼red⊃ = refl


-- red∧₁ : ∀ {Δ Γ A B} → (𝒟 : Δ ⁏ Γ ⊢ A) (ℰ : Δ ⁏ Γ ⊢ B)
--                     → π₁ (𝒟 , ℰ) ∼ 𝒟

test∼red∧₁ : test∼ {∅} {∅ , "A" , "B"}
                   (π₁ (ʳᵛ1 , ʳᵛ0))
                   ʳᵛ1
test∼red∧₁ = refl


-- red∧₂ : ∀ {Δ Γ A B} → (𝒟 : Δ ⁏ Γ ⊢ A) (ℰ : Δ ⁏ Γ ⊢ B)
--                     → π₂ (𝒟 , ℰ) ∼ ℰ

test∼red∧₂ : test∼ {∅} {∅ , "A" , "B"}
                   (π₂ (ʳᵛ1 , ʳᵛ0))
                   ʳᵛ0
test∼red∧₂ = refl


-- red□ : ∀ {Δ Γ A C} → (𝒟 : Δ ⁏ ∅ ⊢ A) (ℰ : Δ , A ⁏ Γ ⊢ C)
--                    → ⌞ ⌜ 𝒟 ⌝ ⌟ ℰ ∼ msub (midₛ , 𝒟) ℰ

test∼red□ : test∼ {∅ , "A"} {∅}
                  (⌞ ⌜ ᵐᵛ0 ⌝ ⌟ ᵐᵛ0)
                  ᵐᵛ0
test∼red□ = refl


-- exp⊃ : ∀ {Δ Γ A B} → (𝒟 : Δ ⁏ Γ ⊢ A ⊃ B)
--                    → 𝒟 ∼ ƛ (rren (wkᵣ idᵣ) 𝒟 $ ʳᵛ0)

test∼exp⊃ : test∼ {∅} {∅ , "A" ⊃ "B"}
                  ʳᵛ0
                  (ƛ (rren (wkᵣ idᵣ) ʳᵛ0 $ ʳᵛ0))
test∼exp⊃ = refl


-- exp∧ : ∀ {Δ Γ A B} → (𝒟 : Δ ⁏ Γ ⊢ A ∧ B)
--                    → 𝒟 ∼ π₁ 𝒟 , π₂ 𝒟

test∼exp∧ : test∼ {∅} {∅ , "A" ∧ "B"}
                  ʳᵛ0
                  (π₁ ʳᵛ0 , π₂ ʳᵛ0)
test∼exp∧ = refl


-- exp𝕋 : ∀ {Δ Γ} → (𝒟 : Δ ⁏ Γ ⊢ 𝕋)
--                → 𝒟 ∼ tt

test∼exp𝕋 : test∼ {∅} {∅ , 𝕋}
                  ʳᵛ0
                  tt
test∼exp𝕋 = refl


-- exp□ : ∀ {Δ Γ} → (𝒟 : Δ ⁏ Γ ⊢ □ A)
--                → 𝒟 ∼ ⌞ 𝒟 ⌟ ⌜ ᵐᵛ0 ⌝

test∼exp□ : test∼ {∅} {∅ , □ "A"}
                  ʳᵛ0
                  (⌞ ʳᵛ0 ⌟ ⌜ ᵐᵛ0 ⌝)
test∼exp□ = refl


-- comm□$ : ∀ {Δ Γ A B} → (Q : Δ ⁏ Γ ⊢ □ (A ⊃ B))
--                         (𝒟 : Δ , A ⊃ B ⁏ Γ ⊢ A ⊃ B) (ℰ : Δ ⁏ Γ ⊢ A)
--                      → (⌞ Q ⌟ 𝒟) $ ℰ ∼ ⌞ Q ⌟ (𝒟 $ (mren (wkᵣ idᵣ) ℰ))

test∼comm□$ : test∼ {∅} {∅ , □ ("A" ⊃ "B") , "A"}
                    ((⌞ ʳᵛ1 ⌟ ᵐᵛ0) $ ʳᵛ0)
                    (⌞ ʳᵛ1 ⌟ (ᵐᵛ0 $ mren (wkᵣ idᵣ) ʳᵛ0))
test∼comm□$ = refl


-- comm□⌞⌟ : ∀ {Δ Γ A C} → (Q : Δ ⁏ Γ ⊢ □ □ A)
--                          (𝒟 : Δ , □ A ⁏ Γ ⊢ □ A) (ℰ : Δ , A ⁏ Γ ⊢ C)
--                       → ⌞ (⌞ Q ⌟ 𝒟) ⌟ ℰ ∼ ⌞ Q ⌟ (⌞ 𝒟 ⌟ (mren (wkᵣ idᵣ) ℰ))

test∼comm□⌞⌟ : test∼ {∅} {∅ , □ □ "A"}
                     (⌞ ⌞ ʳᵛ0 ⌟ ᵐᵛ0 ⌟ ᵐᵛ0)
                     (⌞ ʳᵛ0 ⌟ (⌞ ᵐᵛ0 ⌟ ᵐᵛ0))
test∼comm□⌞⌟ = refl


-- comm□π₁ : ∀ {Δ Γ A B} → (Q : Δ ⁏ Γ ⊢ □ (A ∧ B))
--                          (𝒟 : Δ , A ∧ B ⁏ Γ ⊢ A ∧ B)
--                       → π₁ (⌞ Q ⌟ 𝒟) ∼ ⌞ Q ⌟ (π₁ 𝒟)

test∼comm□π₁ : test∼ {∅} {∅ , □ ("A" ∧ "B")}
                     (π₁ (⌞ ʳᵛ0 ⌟ ᵐᵛ0))
                     (⌞ ʳᵛ0 ⌟ (π₁ ᵐᵛ0))
test∼comm□π₁ = refl


-- comm□π₂ : ∀ {Δ Γ A B} → (Q : Δ ⁏ Γ ⊢ □ (A ∧ B))
--                          (𝒟 : Δ , A ∧ B ⁏ Γ ⊢ A ∧ B)
--                       → π₂ (⌞ Q ⌟ 𝒟) ∼ ⌞ Q ⌟ (π₂ 𝒟)

test∼comm□π₂ : test∼ {∅} {∅ , □ ("A" ∧ "B")}
                     (π₂ (⌞ ʳᵛ0 ⌟ ᵐᵛ0))
                     (⌞ ʳᵛ0 ⌟ (π₂ ᵐᵛ0))
test∼comm□π₂ = refl


--------------------------------------------------------------------------------
--
-- Self-interpretation


-- weakBP : ∀ {Δ Γ A B} → (𝒟 : Δ ⁏ Γ ⊢ A)
--                      → 𝕋 $ ⌜ 𝒟 ⌝ ∼ ⌜ 𝒟 ⌝

test∼weakBP : test∼ {∅ , "A"} {∅}
                    (axT $ ⌜ ᵐᵛ0 ⌝)
                    ᵐᵛ0
test∼weakBP = refl


-- Andrej : ∀ {Δ Γ A B} → (𝒟 : Δ ⁏ Γ ⊢ A ⊃ B) (ℰ : Δ ⁏ Γ ⊢ A)
--                      → (𝔻 $ ⌜ 𝒟 ⌝) $ ⌜ ℰ ⌝ ∼ ⌜ 𝒟 $ ℰ ⌝

test∼Andrej : test∼ {∅ , "A" ⊃ "B" , "A"} {∅}
                    ((axD $ ⌜ ᵐᵛ1 ⌝) $ ⌜ ᵐᵛ0 ⌝)
                    (⌜ ᵐᵛ1 $ ᵐᵛ0 ⌝)
test∼Andrej = refl


--------------------------------------------------------------------------------
