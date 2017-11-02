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
  𝒯   : Tp
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

    ᵛ   : ∀ {A Δ Γ} → (i : Γ ∋ A)
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

    tt  : ∀ {Δ Γ} → Δ ⁏ Γ ⊢ 𝒯

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

      tt  : ∀ {Δ Γ} → Δ ⁏ Γ ⊢ₙₘ 𝒯

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

      ᵛ   : ∀ {A Δ Γ} → (i : Γ ∋ A)
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
  embₙₜ (ᵛ i)   = ᵛ i
  embₙₜ (𝒟 $ ℰ) = embₙₜ 𝒟 $ embₙₘ ℰ
  embₙₜ (π₁ 𝒟)  = π₁ (embₙₜ 𝒟)
  embₙₜ (π₂ 𝒟)  = π₂ (embₙₜ 𝒟)


--------------------------------------------------------------------------------
--
-- Renaming


ᵐren : ∀ {Δ Δ′ Γ A} → Δ′ ⊇ Δ → Δ ⁏ Γ ⊢ A
                    → Δ′ ⁏ Γ ⊢ A
ᵐren η (ᵐᵛ i)    = ᵐᵛ (lookupₑ η i)
ᵐren η (ᵛ i)     = ᵛ i
ᵐren η (ƛ 𝒟)     = ƛ (ᵐren η 𝒟)
ᵐren η (𝒟 $ ℰ)   = ᵐren η 𝒟 $ ᵐren η ℰ
ᵐren η (𝒟 , ℰ)   = ᵐren η 𝒟 , ᵐren η ℰ
ᵐren η (π₁ 𝒟)    = π₁ (ᵐren η 𝒟)
ᵐren η (π₂ 𝒟)    = π₂ (ᵐren η 𝒟)
ᵐren η tt        = tt
ᵐren η (⌜ 𝒟 ⌝)   = ⌜ ᵐren η 𝒟 ⌝
ᵐren η (⌞ 𝒟 ⌟ ℰ) = ⌞ ᵐren η 𝒟 ⌟ (ᵐren (lift η) ℰ)

ren : ∀ {Δ Γ Γ′ A} → Γ′ ⊇ Γ → Δ ⁏ Γ ⊢ A
                   → Δ ⁏ Γ′ ⊢ A
ren η (ᵐᵛ i)    = ᵐᵛ i
ren η (ᵛ i)     = ᵛ (lookupₑ η i)
ren η (ƛ 𝒟)     = ƛ (ren (lift η) 𝒟)
ren η (𝒟 $ ℰ)   = ren η 𝒟 $ ren η ℰ
ren η (𝒟 , ℰ)   = ren η 𝒟 , ren η ℰ
ren η (π₁ 𝒟)    = π₁ (ren η 𝒟)
ren η (π₂ 𝒟)    = π₂ (ren η 𝒟)
ren η tt        = tt
ren η (⌜ 𝒟 ⌝)   = ⌜ 𝒟 ⌝
ren η (⌞ 𝒟 ⌟ ℰ) = ⌞ ren η 𝒟 ⌟ (ren η ℰ)


mutual
  ᵐrenₙₘ : ∀ {Δ Δ′ Γ A} → Δ′ ⊇ Δ → Δ ⁏ Γ ⊢ₙₘ A
                        → Δ′ ⁏ Γ ⊢ₙₘ A
  ᵐrenₙₘ η (ƛ 𝒟)     = ƛ (ᵐrenₙₘ η 𝒟)
  ᵐrenₙₘ η (𝒟 , ℰ)   = ᵐrenₙₘ η 𝒟 , ᵐrenₙₘ η ℰ
  ᵐrenₙₘ η tt        = tt
  ᵐrenₙₘ η (⌜ 𝒟 ⌝)   = ⌜ ᵐren η 𝒟 ⌝
  ᵐrenₙₘ η (⌞ 𝒟 ⌟ ℰ) = ⌞ ᵐrenₙₜ η 𝒟 ⌟ (ᵐrenₙₘ (lift η) ℰ)
  ᵐrenₙₘ η (ⁿᵗ 𝒟)    = ⁿᵗ (ᵐrenₙₜ η 𝒟)

  ᵐrenₙₜ : ∀ {Δ Δ′ Γ A} → Δ′ ⊇ Δ → Δ ⁏ Γ ⊢ₙₜ A
                        → Δ′ ⁏ Γ ⊢ₙₜ A
  ᵐrenₙₜ η (ᵐᵛ i)  = ᵐᵛ (lookupₑ η i)
  ᵐrenₙₜ η (ᵛ i )  = ᵛ i
  ᵐrenₙₜ η (𝒟 $ ℰ) = ᵐrenₙₜ η 𝒟 $ ᵐrenₙₘ η ℰ
  ᵐrenₙₜ η (π₁ 𝒟)  = π₁ (ᵐrenₙₜ η 𝒟)
  ᵐrenₙₜ η (π₂ 𝒟)  = π₂ (ᵐrenₙₜ η 𝒟)


mutual
  renₙₘ : ∀ {Δ Γ Γ′ A} → Γ′ ⊇ Γ → Δ ⁏ Γ ⊢ₙₘ A
                       → Δ ⁏ Γ′ ⊢ₙₘ A
  renₙₘ η (ƛ 𝒟)     = ƛ (renₙₘ (lift η) 𝒟)
  renₙₘ η (𝒟 , ℰ)   = renₙₘ η 𝒟 , renₙₘ η ℰ
  renₙₘ η tt        = tt
  renₙₘ η (⌜ 𝒟 ⌝)   = ⌜ 𝒟 ⌝
  renₙₘ η (⌞ 𝒟 ⌟ ℰ) = ⌞ renₙₜ η 𝒟 ⌟ (renₙₘ η ℰ)
  renₙₘ η (ⁿᵗ 𝒟)    = ⁿᵗ (renₙₜ η 𝒟)

  renₙₜ : ∀ {Δ Γ Γ′ A} → Γ′ ⊇ Γ → Δ ⁏ Γ ⊢ₙₜ A
                       → Δ ⁏ Γ′ ⊢ₙₜ A
  renₙₜ η (ᵐᵛ i)  = ᵐᵛ i
  renₙₜ η (ᵛ i)   = ᵛ (lookupₑ η i)
  renₙₜ η (𝒟 $ ℰ) = renₙₜ η 𝒟 $ renₙₘ η ℰ
  renₙₜ η (π₁ 𝒟)  = π₁ (renₙₜ η 𝒟)
  renₙₜ η (π₂ 𝒟)  = π₂ (renₙₜ η 𝒟)


renₙₘ² : ∀ {Δ Δ′ Γ Γ′ A} → Δ′ ⁏ Γ′ ⊇² Δ ⁏ Γ → Δ ⁏ Γ ⊢ₙₘ A
                         → Δ′ ⁏ Γ′ ⊢ₙₘ A
renₙₘ² η 𝒟 = (ᵐrenₙₘ (proj₁ η) ∘ renₙₘ (proj₂ η)) 𝒟

renₙₜ² : ∀ {Δ Δ′ Γ Γ′ A} → Δ′ ⁏ Γ′ ⊇² Δ ⁏ Γ → Δ ⁏ Γ ⊢ₙₜ A
                         → Δ′ ⁏ Γ′ ⊢ₙₜ A
renₙₜ² η 𝒟 = (ᵐrenₙₜ (proj₁ η) ∘ renₙₜ (proj₂ η)) 𝒟


--------------------------------------------------------------------------------
--
-- Substitution


-- Simultaneous substitutions
infix 3 _⊢⋆_
_⊢⋆_ : Cx → List Tp → Set
Δ ⁏ Γ ⊢⋆ Ξ = All (Δ ⁏ Γ ⊢_) Ξ


ᵐren⋆ : ∀ {Δ Δ′ Γ Ξ} → Δ′ ⊇ Δ → Δ ⁏ Γ ⊢⋆ Ξ
                     → Δ′ ⁏ Γ ⊢⋆ Ξ
ᵐren⋆ η σ = mapAll (ᵐren η) σ

ren⋆ : ∀ {Δ Γ Γ′ Ξ} → Γ′ ⊇ Γ → Δ ⁏ Γ ⊢⋆ Ξ
                     → Δ ⁏ Γ′ ⊢⋆ Ξ
ren⋆ η σ = mapAll (ren η) σ


ᵐwkₛ : ∀ {Δ Γ Ξ A} → Δ ⁏ Γ ⊢⋆ Ξ
                   → Δ , A ⁏ Γ ⊢⋆ Ξ
ᵐwkₛ σ = ᵐren⋆ (wk idₑ) σ

wkₛ : ∀ {Δ Γ Ξ A} → Δ ⁏ Γ ⊢⋆ Ξ
                  → Δ ⁏ Γ , A ⊢⋆ Ξ
wkₛ σ = ren⋆ (wk idₑ) σ

ᵐliftₛ : ∀ {Δ Γ Ξ A} → Δ ⁏ Γ ⊢⋆ Ξ
                     → Δ , A ⁏ Γ ⊢⋆ Ξ , A
ᵐliftₛ σ = ᵐwkₛ σ , ᵐᵛ zero

liftₛ : ∀ {Δ Γ Ξ A} → Δ ⁏ Γ ⊢⋆ Ξ
                    → Δ ⁏ Γ , A ⊢⋆ Ξ , A
liftₛ σ = wkₛ σ , ᵛ zero


ᵐidₛ : ∀ {Δ Γ} → Δ ⁏ Γ ⊢⋆ Δ
ᵐidₛ {∅}     = ∅
ᵐidₛ {Γ , A} = ᵐliftₛ ᵐidₛ

idₛ : ∀ {Γ Δ} → Δ ⁏ Γ ⊢⋆ Γ
idₛ {∅}     = ∅
idₛ {Γ , A} = liftₛ idₛ


lookupₛ : ∀ {Δ Γ Ξ A} → Δ ⁏ Γ ⊢⋆ Ξ → Ξ ∋ A
                      → Δ ⁏ Γ ⊢ A
lookupₛ σ i = lookupAll σ i


-- Substitution
ᵐsub : ∀ {Δ Γ Ξ A} → Δ ⁏ ∅ ⊢⋆ Ξ → Ξ ⁏ Γ ⊢ A
                   → Δ ⁏ Γ ⊢ A
ᵐsub σ (ᵐᵛ i)    = ren infₑ (lookupₛ σ i)
ᵐsub σ (ᵛ i)     = ᵛ i
ᵐsub σ (ƛ 𝒟)     = ƛ (ᵐsub σ 𝒟)
ᵐsub σ (𝒟 $ ℰ)   = ᵐsub σ 𝒟 $ ᵐsub σ ℰ
ᵐsub η (𝒟 , ℰ)   = ᵐsub η 𝒟 , ᵐsub η ℰ
ᵐsub η (π₁ 𝒟)    = π₁ (ᵐsub η 𝒟)
ᵐsub η (π₂ 𝒟)    = π₂ (ᵐsub η 𝒟)
ᵐsub η tt        = tt
ᵐsub σ ⌜ 𝒟 ⌝     = ⌜ ᵐsub σ 𝒟 ⌝
ᵐsub σ (⌞ 𝒟 ⌟ ℰ) = ⌞ ᵐsub σ 𝒟 ⌟ (ᵐsub (ᵐliftₛ σ) ℰ)

sub : ∀ {Δ Γ Ξ A} → Δ ⁏ Γ ⊢⋆ Ξ → Δ ⁏ Ξ ⊢ A
                  → Δ ⁏ Γ ⊢ A
sub σ (ᵐᵛ i)    = ᵐᵛ i
sub σ (ᵛ i)     = lookupₛ σ i
sub σ (ƛ 𝒟)     = ƛ (sub (liftₛ σ) 𝒟)
sub σ (𝒟 $ ℰ)   = sub σ 𝒟 $ sub σ ℰ
sub η (𝒟 , ℰ)   = sub η 𝒟 , sub η ℰ
sub η (π₁ 𝒟)    = π₁ (sub η 𝒟)
sub η (π₂ 𝒟)    = π₂ (sub η 𝒟)
sub η tt        = tt
sub σ ⌜ 𝒟 ⌝     = ⌜ 𝒟 ⌝
sub σ (⌞ 𝒟 ⌟ ℰ) = ⌞ sub σ 𝒟 ⌟ (sub (ᵐwkₛ σ) ℰ)


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

ᵐ⌊_⌋ₐ : ∀ {{𝔐 : 𝔎}} {w w′} → w′ ≥ w
                           → ᵐ⌊ w′ ⌋ ⊇ ᵐ⌊ w ⌋
ᵐ⌊ η ⌋ₐ = proj₁ ⌊ η ⌋ₐ


-- Values
mutual
  infix 3 _⊩_
  _⊩_ : ∀ {{𝔐 : 𝔎}} → 𝒲 → Tp → Set

  w ⊩ ᵗᵛ x  = 𝒱 w x

  w ⊩ A ⊃ B = ∀ {w′} → (η : w′ ≥ w) (k : w′ ᵏ⊩ A)
                      → w′ ᵏ⊩ B

  w ⊩ A ∧ B = w ᵏ⊩ A × w ᵏ⊩ B

  w ⊩ 𝒯     = ⊤

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
syn⋆ ᵐρ = mapAll syn ᵐρ

sem⋆ : ∀ {{𝔐 : 𝔎}} {w Ξ} → w ᵐᵏ⊩⋆ Ξ
                         → w ᵏ⊩⋆ Ξ
sem⋆ ᵐρ = mapAll sem ᵐρ


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
  acc {A ∧ B} η p = ᵏacc {A} η (proj₁ p) , ᵏacc {B} η (proj₂ p)
  acc {𝒯}     η t = tt
  acc {□ A}   η f = λ η′ → f (η ∘ₐ η′)

  ᵏacc : ∀ {{𝔐 : 𝔎}} {A w w′} → w′ ≥ w → w ᵏ⊩ A
                              → w′ ᵏ⊩ A
  ᵏacc η k = λ η′ f → k (η ∘ₐ η′) f

ᵐᵏacc : ∀ {{𝔐 : 𝔎}} {A w w′} → w′ ≥ w → w ᵐᵏ⊩ A
                             → w′ ᵐᵏ⊩ A
ᵐᵏacc {A} η (𝒟 , k) = ᵐren ᵐ⌊ η ⌋ₐ 𝒟 , ᵏacc {A} η k


ᵏacc⋆ : ∀ {{𝔐 : 𝔎}} {Ξ w w′} → w′ ≥ w → w ᵏ⊩⋆ Ξ
                             → w′ ᵏ⊩⋆ Ξ
-- TODO: Why does Agda require me to add seemingly unused annotations here?
-- ᵏacc⋆ η ρ = mapAll (ᵏacc η) ρ
ᵏacc⋆ η ρ = mapAll (λ {A} k {_} {_} → ᵏacc {A} η (k {_})) ρ

ᵐᵏacc⋆ : ∀ {{𝔐 : 𝔎}} {Ξ w w′} → w′ ≥ w → w ᵐᵏ⊩⋆ Ξ
                              → w′ ᵐᵏ⊩⋆ Ξ
ᵐᵏacc⋆ η ᵐρ = mapAll (ᵐᵏacc η) ᵐρ


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


-- Soundness kit
ᵏlookupᵨ : ∀ {{𝔐 : 𝔎}} {Ξ A w} → w ᵏ⊩⋆ Ξ → Ξ ∋ A
                               → w ᵏ⊩ A
ᵏlookupᵨ ρ i = lookupAll ρ i


ᵏƛ : ∀ {{𝔐 : 𝔎}} {A B w} → (∀ {w′} → w′ ≥ w → w′ ᵏ⊩ A
                                    → w′ ᵏ⊩ B)
                         → w ᵏ⊩ A ⊃ B
ᵏƛ {A} {B} f = return {A ⊃ B} (λ η k → f η k)

ᵏ$ : ∀ {{𝔐 : 𝔎}} {A B w} → w ᵏ⊩ A ⊃ B → w ᵏ⊩ A
                         → w ᵏ⊩ B
ᵏ$ {A} {B} k₁ k₂ = bind {A ⊃ B} {B} k₁ (λ η f → f idₐ (ᵏacc {A} η k₂))

ᵏ, : ∀ {{𝔐 : 𝔎}} {A B w} → w ᵏ⊩ A → w ᵏ⊩ B
                         → w ᵏ⊩ A ∧ B
ᵏ, {A} {B} k₁ k₂ = return {A ∧ B} (k₁ , k₂)

ᵏπ₁ : ∀ {{𝔐 : 𝔎}} {A B w} → w ᵏ⊩ A ∧ B
                          → w ᵏ⊩ A
ᵏπ₁ {A} {B} k = bind {A ∧ B} {A} k (λ η p → proj₁ p)

ᵏπ₂ : ∀ {{𝔐 : 𝔎}} {A B w} → w ᵏ⊩ A ∧ B
                          → w ᵏ⊩ B
ᵏπ₂ {A} {B} k = bind {A ∧ B} {B} k (λ η p → proj₂ p)

ᵏtt : ∀ {{𝔐 : 𝔎}} {w} → w ᵏ⊩ 𝒯
ᵏtt = return {𝒯} tt

ᵏ⌜⌝ : ∀ {{𝔐 : 𝔎}} {A w} → (∀ {w′} → w′ ≥ w
                                   → w′ ᵐᵏ⊩ A)
                        → w ᵏ⊩ □ A
ᵏ⌜⌝ {A} f = return {□ A} (λ η → f η)

ᵏ⌞⌟ : ∀ {{𝔐 : 𝔎}} {A C w} → w ᵏ⊩ □ A
                          → (∀ {w′} → w′ ≥ w → w′ ᵐᵏ⊩ A
                                     → w′ ᵏ⊩ C)
                          → w ᵏ⊩ C
ᵏ⌞⌟ {A} {C} k f = bind {□ A} {C} k (λ η f′ → f η (f′ idₐ))


-- -- Soundness
-- ↓ : ∀ {Δ Γ A} → Δ ⁏ Γ ⊢ A
--               → Δ ⁏ Γ ⊨ A
-- ↓ (ᵐᵛ i)            ᵐρ ρ = ᵏlookupᵨ (sem⋆ ᵐρ) i
-- ↓ (ᵛ i)             ᵐρ ρ = ᵏlookupᵨ ρ i
-- ↓ (ƛ {A} {B} 𝒟)     ᵐρ ρ = ᵏƛ {A} {B} (λ η k →
--                              ↓ 𝒟 (ᵐᵏacc⋆ η ᵐρ) (ᵏacc⋆ η ρ , k))
-- ↓ (_$_ {A} {B} 𝒟 ℰ) ᵐρ ρ = ᵏ$ {A} {B} (↓ 𝒟 ᵐρ ρ) (↓ ℰ ᵐρ ρ)
-- ↓ (_,_ {A} {B} 𝒟 ℰ) ᵐρ ρ = ᵏ, {A} {B} (↓ 𝒟 ᵐρ ρ) (↓ ℰ ᵐρ ρ)
-- ↓ (π₁ {A} {B} 𝒟)    ᵐρ ρ = ᵏπ₁ {A} {B} (↓ 𝒟 ᵐρ ρ)
-- ↓ (π₂ {A} {B} 𝒟)    ᵐρ ρ = ᵏπ₂ {A} {B} (↓ 𝒟 ᵐρ ρ)
-- ↓ tt                ᵐρ ρ = ᵏtt
-- ↓ (⌜_⌝ {A} 𝒟)       ᵐρ ρ = ᵏ⌜⌝ {A} (λ η →
--                              ᵐsub (syn⋆ (ᵐᵏacc⋆ η ᵐρ)) 𝒟 , ↓ 𝒟 (ᵐᵏacc⋆ η ᵐρ) ∅)
-- ↓ (⌞_⌟ {A} {C} 𝒟 ℰ) ᵐρ ρ = ᵏ⌞⌟ {A} {C} (↓ 𝒟 ᵐρ ρ) (λ η 𝒟k →
--                              ↓ ℰ (ᵐᵏacc⋆ η ᵐρ , 𝒟k) (ᵏacc⋆ η ρ))


-- Soundness, inlined
↓ : ∀ {Δ Γ A} → Δ ⁏ Γ ⊢ A
              → Δ ⁏ Γ ⊨ A
↓ (ᵐᵛ i)            ᵐρ ρ = ᵏlookupᵨ (sem⋆ ᵐρ) i
↓ (ᵛ i)             ᵐρ ρ = ᵏlookupᵨ ρ i
↓ (ƛ {A} {B} 𝒟)     ᵐρ ρ = return {A ⊃ B} (λ η k →
                             ↓ 𝒟 (ᵐᵏacc⋆ η ᵐρ) (ᵏacc⋆ η ρ , k))
↓ (_$_ {A} {B} 𝒟 ℰ) ᵐρ ρ = bind {A ⊃ B} {B} (↓ 𝒟 ᵐρ ρ) (λ η f →
                             f idₐ (↓ ℰ (ᵐᵏacc⋆ η ᵐρ) (ᵏacc⋆ η ρ)))
↓ (_,_ {A} {B} 𝒟 ℰ) ᵐρ ρ = return {A ∧ B} (↓ 𝒟 ᵐρ ρ , ↓ ℰ ᵐρ ρ)
↓ (π₁ {A} {B} 𝒟)    ᵐρ ρ = bind {A ∧ B} {A} (↓ 𝒟 ᵐρ ρ) (λ η p → proj₁ p)
↓ (π₂ {A} {B} 𝒟)    ᵐρ ρ = bind {A ∧ B} {B} (↓ 𝒟 ᵐρ ρ) (λ η p → proj₂ p)
↓ tt                ᵐρ ρ = return {𝒯} tt
↓ (⌜_⌝ {A} 𝒟)       ᵐρ ρ = return {□ A} (λ η →
                             ᵐsub (syn⋆ (ᵐᵏacc⋆ η ᵐρ)) 𝒟 , ↓ 𝒟 (ᵐᵏacc⋆ η ᵐρ) ∅)
↓ (⌞_⌟ {A} {C} 𝒟 ℰ) ᵐρ ρ = bind {□ A} {C} (↓ 𝒟 ᵐρ ρ) (λ η f →
                             ↓ ℰ (ᵐᵏacc⋆ η ᵐρ , f idₐ) (ᵏacc⋆ η ρ))


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
         ; idₐ  = idₑ²
         ; _∘ₐ_ = _∘ₑ²_
         ; accᵥ = renₙₘ²
         ; ⌊_⌋  = id
         ; ⌊_⌋ₐ = id
         }


-- Soundness and completeness with respect to the universal model
mutual
  ↓ᵤ : ∀ {A Δ Γ} → Δ ⁏ Γ ⊢ₙₜ A
                 → Δ ⁏ Γ ᵏ⊩ A
  ↓ᵤ {ᵗᵛ x}  𝒟 = return {ᵗᵛ x} (ⁿᵗ 𝒟)
  ↓ᵤ {A ⊃ B} 𝒟 = return {A ⊃ B} (λ η k → ↓ᵤ (renₙₜ² η 𝒟 $ ↑ᵤ k))
  ↓ᵤ {A ∧ B} 𝒟 = return {A ∧ B} (↓ᵤ (π₁ 𝒟) , ↓ᵤ (π₂ 𝒟))
  ↓ᵤ {𝒯}     𝒟 = return {𝒯} tt
  ↓ᵤ {□ A}   𝒟 = λ η f → ⌞ renₙₜ² η 𝒟 ⌟ (f (ᵐwk² idₑ²) (λ η′ →
                   ᵐᵛ (ᵐlookupₑ² η′ zero) , ↓ᵤ (ᵐᵛ (ᵐlookupₑ² η′ zero))))

  ↑ᵤ : ∀ {A Δ Γ} → Δ ⁏ Γ ᵏ⊩ A
                 → Δ ⁏ Γ ⊢ₙₘ A
  ↑ᵤ {ᵗᵛ x}  k = k idₑ² (λ η 𝒟 → 𝒟)
  ↑ᵤ {A ⊃ B} k = k idₑ² (λ η f → ƛ (↑ᵤ (f (wk² idₑ²) (↓ᵤ (ᵛ zero)))))
  ↑ᵤ {A ∧ B} k = k idₑ² (λ η p → ↑ᵤ (proj₁ p) , ↑ᵤ (proj₂ p))
  ↑ᵤ {𝒯}     k = k idₑ² (λ η t → tt)
  ↑ᵤ {□ A}   k = k idₑ² (λ η f → ⌜ syn (f idₑ²) ⌝)


ᵐᵏidᵨ : ∀ {Δ Γ} → Δ ⁏ Γ ᵐᵏ⊩⋆ Δ
ᵐᵏidᵨ {∅}     = ∅
ᵐᵏidᵨ {Δ , A} = ᵐᵏacc⋆ (ᵐwk² idₑ²) ᵐᵏidᵨ , (ᵐᵛ zero , ↓ᵤ (ᵐᵛ zero))

ᵏidᵨ : ∀ {Γ Δ} → Δ ⁏ Γ ᵏ⊩⋆ Γ
ᵏidᵨ {∅}     = ∅
ᵏidᵨ {Γ , A} = ᵏacc⋆ (wk² idₑ²) ᵏidᵨ , ↓ᵤ (ᵛ zero)


-- Completeness
↑ : ∀ {Δ Γ A} → Δ ⁏ Γ ⊨ A
              → Δ ⁏ Γ ⊢ₙₘ A
↑ f = ↑ᵤ (f ᵐᵏidᵨ ᵏidᵨ)


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


ᵛ0 : ∀ {Δ Γ A} → Δ ⁏ Γ , A ⊢ A
ᵛ0 = ᵛ zero

ᵛ1 : ∀ {Δ Γ A B} → Δ ⁏ Γ , A , B ⊢ A
ᵛ1 = ᵛ (suc zero)

ᵛ2 : ∀ {Δ Γ A B C} → Δ ⁏ Γ , A , B , C ⊢ A
ᵛ2 = ᵛ (suc (suc zero))


ᵃˣI : ∀ {A Δ Γ} → Δ ⁏ Γ ⊢ A ⊃ A
ᵃˣI = ƛ ᵛ0

ᵃˣK : ∀ {A B Δ Γ} → Δ ⁏ Γ ⊢ A ⊃ B ⊃ A
ᵃˣK = ƛ (ƛ ᵛ1)

ᵃˣS : ∀ {A B C Δ Γ} → Δ ⁏ Γ ⊢ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
ᵃˣS = ƛ (ƛ (ƛ ((ᵛ2 $ ᵛ0) $ (ᵛ1 $ ᵛ0))))


ᵃˣD : ∀ {A B Δ Γ} → Δ ⁏ Γ ⊢ □ (A ⊃ B) ⊃ □ A ⊃ □ B
ᵃˣD = ƛ (ƛ (⌞ ᵛ1 ⌟ (⌞ ᵛ0 ⌟ ⌜ ᵐᵛ1 $ ᵐᵛ0 ⌝)))

ᵃˣT : ∀ {A Δ Γ} → Δ ⁏ Γ ⊢ □ A ⊃ A
ᵃˣT = ƛ (⌞ ᵛ0 ⌟ ᵐᵛ0)

ᵃˣ4 : ∀ {A Δ Γ} → Δ ⁏ Γ ⊢ □ A ⊃ □ □ A
ᵃˣ4 = ƛ (⌞ ᵛ0 ⌟ ⌜ ⌜ ᵐᵛ0 ⌝ ⌝)


--------------------------------------------------------------------------------
--
-- Conversion tests


test∼ : ∀ {Δ Γ A} → Δ ⁏ Γ ⊢ A → Δ ⁏ Γ ⊢ A → Set
test∼ 𝒟₁ 𝒟₂ = embₙₘ (nm 𝒟₁) ≡ 𝒟₂


-- red⊃ : ∀ {Δ Γ A B} → (𝒟 : Δ ⁏ Γ , A ⊢ B) (ℰ : Δ ⁏ Γ ⊢ A)
--                    → ƛ 𝒟 $ ℰ ∼ sub (idₛ , ℰ) 𝒟

test∼red⊃ : test∼ {∅} {∅ , "A"}
                  ((ƛ ᵛ0) $ ᵛ0)
                  ᵛ0
test∼red⊃ = refl


-- red∧₁ : ∀ {Δ Γ A B} → (𝒟 : Δ ⁏ Γ ⊢ A) (ℰ : Δ ⁏ Γ ⊢ B)
--                     → π₁ (𝒟 , ℰ) ∼ 𝒟

test∼red∧₁ : test∼ {∅} {∅ , "A" , "B"}
                   (π₁ (ᵛ1 , ᵛ0))
                   ᵛ1
test∼red∧₁ = refl


-- red∧₂ : ∀ {Δ Γ A B} → (𝒟 : Δ ⁏ Γ ⊢ A) (ℰ : Δ ⁏ Γ ⊢ B)
--                     → π₂ (𝒟 , ℰ) ∼ ℰ

test∼red∧₂ : test∼ {∅} {∅ , "A" , "B"}
                   (π₂ (ᵛ1 , ᵛ0))
                   ᵛ0
test∼red∧₂ = refl


-- red□ : ∀ {Δ Γ A C} → (𝒟 : Δ ⁏ ∅ ⊢ A) (ℰ : Δ , A ⁏ Γ ⊢ C)
--                    → ⌞ ⌜ 𝒟 ⌝ ⌟ ℰ ∼ ᵐsub (ᵐidₛ , 𝒟) ℰ

test∼red□ : test∼ {∅ , "A"} {∅}
                  (⌞ ⌜ ᵐᵛ0 ⌝ ⌟ ᵐᵛ0)
                  ᵐᵛ0
test∼red□ = refl


-- exp⊃ : ∀ {Δ Γ A B} → (𝒟 : Δ ⁏ Γ ⊢ A ⊃ B)
--                    → 𝒟 ∼ ƛ (ren (wk idₑ) 𝒟 $ ᵛ0)

test∼exp⊃ : test∼ {∅} {∅ , "A" ⊃ "B"}
                  ᵛ0
                  (ƛ (ren (wk idₑ) ᵛ0 $ ᵛ0))
test∼exp⊃ = refl


-- exp∧ : ∀ {Δ Γ A B} → (𝒟 : Δ ⁏ Γ ⊢ A ∧ B)
--                    → 𝒟 ∼ π₁ 𝒟 , π₂ 𝒟

test∼exp∧ : test∼ {∅} {∅ , "A" ∧ "B"}
                  ᵛ0
                  (π₁ ᵛ0 , π₂ ᵛ0)
test∼exp∧ = refl


-- exp𝒯 : ∀ {Δ Γ} → (𝒟 : Δ ⁏ Γ ⊢ 𝒯)
--                → 𝒟 ∼ tt

test∼exp𝒯 : test∼ {∅} {∅ , 𝒯}
                  ᵛ0
                  tt
test∼exp𝒯 = refl


-- exp□ : ∀ {Δ Γ} → (𝒟 : Δ ⁏ Γ ⊢ □ A)
--                → 𝒟 ∼ ⌞ 𝒟 ⌟ ⌜ ᵐᵛ0 ⌝

test∼exp□ : test∼ {∅} {∅ , □ "A"}
                  ᵛ0
                  (⌞ ᵛ0 ⌟ ⌜ ᵐᵛ0 ⌝)
test∼exp□ = refl


-- comm□$ : ∀ {Δ Γ A B} → (𝒬 : Δ ⁏ Γ ⊢ □ (A ⊃ B))
--                         (𝒟 : Δ , A ⊃ B ⁏ Γ ⊢ A ⊃ B) (ℰ : Δ ⁏ Γ ⊢ A)
--                      → (⌞ 𝒬 ⌟ 𝒟) $ ℰ ∼ ⌞ 𝒬 ⌟ (𝒟 $ (ᵐren (wk idₑ) ℰ))

test∼comm□$ : test∼ {∅} {∅ , □ ("A" ⊃ "B") , "A"}
                    ((⌞ ᵛ1 ⌟ ᵐᵛ0) $ ᵛ0)
                    (⌞ ᵛ1 ⌟ (ᵐᵛ0 $ ᵐren (wk idₑ) ᵛ0))
test∼comm□$ = refl


-- comm□⌞⌟ : ∀ {Δ Γ A C} → (𝒬 : Δ ⁏ Γ ⊢ □ □ A)
--                          (𝒟 : Δ , □ A ⁏ Γ ⊢ □ A) (ℰ : Δ , A ⁏ Γ ⊢ C)
--                       → ⌞ (⌞ 𝒬 ⌟ 𝒟) ⌟ ℰ ∼ ⌞ 𝒬 ⌟ (⌞ 𝒟 ⌟ (ᵐren (wk idₑ) ℰ))

test∼comm□⌞⌟ : test∼ {∅} {∅ , □ □ "A"}
                     (⌞ ⌞ ᵛ0 ⌟ ᵐᵛ0 ⌟ ᵐᵛ0)
                     (⌞ ᵛ0 ⌟ (⌞ ᵐᵛ0 ⌟ ᵐᵛ0))
test∼comm□⌞⌟ = refl


-- comm□π₁ : ∀ {Δ Γ A B} → (𝒬 : Δ ⁏ Γ ⊢ □ (A ∧ B))
--                          (𝒟 : Δ , A ∧ B ⁏ Γ ⊢ A ∧ B)
--                       → π₁ (⌞ 𝒬 ⌟ 𝒟) ∼ ⌞ 𝒬 ⌟ (π₁ 𝒟)

test∼comm□π₁ : test∼ {∅} {∅ , □ ("A" ∧ "B")}
                     (π₁ (⌞ ᵛ0 ⌟ ᵐᵛ0))
                     (⌞ ᵛ0 ⌟ (π₁ ᵐᵛ0))
test∼comm□π₁ = refl


-- comm□π₂ : ∀ {Δ Γ A B} → (𝒬 : Δ ⁏ Γ ⊢ □ (A ∧ B))
--                          (𝒟 : Δ , A ∧ B ⁏ Γ ⊢ A ∧ B)
--                       → π₂ (⌞ 𝒬 ⌟ 𝒟) ∼ ⌞ 𝒬 ⌟ (π₂ 𝒟)

test∼comm□π₂ : test∼ {∅} {∅ , □ ("A" ∧ "B")}
                     (π₂ (⌞ ᵛ0 ⌟ ᵐᵛ0))
                     (⌞ ᵛ0 ⌟ (π₂ ᵐᵛ0))
test∼comm□π₂ = refl


--------------------------------------------------------------------------------
--
-- Self-interpretation


-- weakBP : ∀ {Δ Γ A B} → (𝒟 : Δ ⁏ Γ ⊢ A)
--                      → 𝒯 $ ⌜ 𝒟 ⌝ ∼ ⌜ 𝒟 ⌝

test∼weakBP : test∼ {∅ , "A"} {∅}
                    (ᵃˣT $ ⌜ ᵐᵛ0 ⌝)
                    ᵐᵛ0
test∼weakBP = refl


-- Andrej : ∀ {Δ Γ A B} → (𝒟 : Δ ⁏ Γ ⊢ A ⊃ B) (ℰ : Δ ⁏ Γ ⊢ A)
--                      → (𝔻 $ ⌜ 𝒟 ⌝) $ ⌜ ℰ ⌝ ∼ ⌜ 𝒟 $ ℰ ⌝

test∼Andrej : test∼ {∅ , "A" ⊃ "B" , "A"} {∅}
                    ((ᵃˣD $ ⌜ ᵐᵛ1 ⌝) $ ⌜ ᵐᵛ0 ⌝)
                    (⌜ ᵐᵛ1 $ ᵐᵛ0 ⌝)
test∼Andrej = refl


--------------------------------------------------------------------------------
