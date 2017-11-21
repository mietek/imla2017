module S4WithoutTerms where

open import Prelude public


--------------------------------------------------------------------------------
--
-- Syntax


-- Type variables
data TVar : Set where
  mkTV : String → TVar

injmkTV : ∀ {s₁ s₂} → mkTV s₁ ≡ mkTV s₂ → s₁ ≡ s₂
injmkTV refl = refl

_≟ₜᵥ_ : (x₁ x₂ : TVar) → Dec (x₁ ≡ x₂)
mkTV s₁ ≟ₜᵥ mkTV s₂ = mapDec (mkTV &_) injmkTV (s₁ ≟ₛ s₂)

instance
  TVarIsString : IsString TVar
  TVarIsString =
    record
      { Constraint = λ s → ⊤
      ; fromString = λ s → mkTV s
      }


-- Types
infixl 9 _∧_
infixr 7 _⊃_
data Tp : Set where
  ᵗᵛ  : (x : TVar) → Tp
  _⊃_ : (A B : Tp) → Tp
  _∧_ : (A B : Tp) → Tp
  TT  : Tp
  □_  : (A : Tp) → Tp

instance
  typeIsString : IsString Tp
  typeIsString =
    record
      { Constraint = λ s → ⊤
      ; fromString = λ s → ᵗᵛ (mkTV s)
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

    tt  : ∀ {Δ Γ} → Δ ⁏ Γ ⊢ TT

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

      tt  : ∀ {Δ Γ} → Δ ⁏ Γ ⊢ₙₘ TT

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
ᵐren η (ᵐᵛ i)    = ᵐᵛ (lookupᵣ η i)
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
ren η (ᵛ i)     = ᵛ (lookupᵣ η i)
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
  ᵐrenₙₜ η (ᵐᵛ i)  = ᵐᵛ (lookupᵣ η i)
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
  renₙₜ η (ᵛ i)   = ᵛ (lookupᵣ η i)
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
ᵐren⋆ η σ = mapₐ (ᵐren η) σ

ren⋆ : ∀ {Δ Γ Γ′ Ξ} → Γ′ ⊇ Γ → Δ ⁏ Γ ⊢⋆ Ξ
                     → Δ ⁏ Γ′ ⊢⋆ Ξ
ren⋆ η σ = mapₐ (ren η) σ


ᵐwkₛ : ∀ {Δ Γ Ξ A} → Δ ⁏ Γ ⊢⋆ Ξ
                   → Δ , A ⁏ Γ ⊢⋆ Ξ
ᵐwkₛ σ = ᵐren⋆ (wk idᵣ) σ

wkₛ : ∀ {Δ Γ Ξ A} → Δ ⁏ Γ ⊢⋆ Ξ
                  → Δ ⁏ Γ , A ⊢⋆ Ξ
wkₛ σ = ren⋆ (wk idᵣ) σ

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
lookupₛ σ i = lookupₐ σ i


-- Substitution
ᵐsub : ∀ {Δ Γ Ξ A} → Δ ⁏ ∅ ⊢⋆ Ξ → Ξ ⁏ Γ ⊢ A
                   → Δ ⁏ Γ ⊢ A
ᵐsub σ (ᵐᵛ i)    = ren infᵣ (lookupₛ σ i)
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

    _𝒱_  : 𝒲 → TVar → Set

    _≥_  : 𝒲 → 𝒲 → Set

    idₐ  : ∀ {w} → w ≥ w

    _∘ₐ_ : ∀ {w w′ w″} → w′ ≥ w → w″ ≥ w′
                       → w″ ≥ w

    relᵥ : ∀ {x w w′} → w′ ≥ w → w 𝒱 x
                      → w′ 𝒱 x

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

  w ⊩ ᵗᵛ x  = w 𝒱 x

  w ⊩ A ⊃ B = ∀ {w′} → (η : w′ ≥ w) (k : w′ ⊩ₖ A)
                      → w′ ⊩ₖ B

  w ⊩ A ∧ B = w ⊩ₖ A × w ⊩ₖ B

  w ⊩ TT    = ⊤

  w ⊩ □ A   = w ᵐ⊩ₖ A

  infix 3 _⊩ₖ_
  _⊩ₖ_ : ∀ {{𝔐 : 𝔎}} → 𝒲 → Tp → Set
  w ⊩ₖ A = ∀ {w′ C} → (η : w′ ≥ w) (f : ∀ {w″} → w″ ≥ w′ → w″ ⊩ A
                                                 → ⌊ w″ ⌋ ⊢ₙₘ C)
                     → ⌊ w′ ⌋ ⊢ₙₘ C

  infix 3 _ᵐ⊩ₖ_
  _ᵐ⊩ₖ_ : ∀ {{𝔐 : 𝔎}} → 𝒲 → Tp → Set
  w ᵐ⊩ₖ A = ᵐ⌊ w ⌋ ⁏ ∅ ⊢ A × w ⊩ₖ A


syn : ∀ {{𝔐 : 𝔎}} {w A} → w ᵐ⊩ₖ A
                        → ᵐ⌊ w ⌋ ⁏ ∅ ⊢ A
syn p = proj₁ p

sem : ∀ {{𝔐 : 𝔎}} {w A} → w ᵐ⊩ₖ A
                        → w ⊩ₖ A
sem p = proj₂ p


-- Environments
infix 3 _⊩ₖ⋆_
_⊩ₖ⋆_ : ∀ {{𝔐 : 𝔎}} → 𝒲 → List Tp → Set
w ⊩ₖ⋆ Ξ = All (w ⊩ₖ_) Ξ

infix 3 _ᵐ⊩ₖ⋆_
_ᵐ⊩ₖ⋆_ : ∀ {{𝔐 : 𝔎}} → 𝒲 → List Tp → Set
w ᵐ⊩ₖ⋆ Ξ = All (w ᵐ⊩ₖ_) Ξ


syn⋆ : ∀ {{𝔐 : 𝔎}} {w Ξ} → w ᵐ⊩ₖ⋆ Ξ
                         → ᵐ⌊ w ⌋ ⁏ ∅ ⊢⋆ Ξ
syn⋆ δ = mapₐ syn δ

sem⋆ : ∀ {{𝔐 : 𝔎}} {w Ξ} → w ᵐ⊩ₖ⋆ Ξ
                         → w ⊩ₖ⋆ Ξ
sem⋆ δ = mapₐ sem δ


-- Semantic entailment
infix 3 _⊨_
_⊨_ : Cx → Tp → Set₁
Δ ⁏ Γ ⊨ A = ∀ {{𝔐 : 𝔎}} {w} → w ᵐ⊩ₖ⋆ Δ → w ⊩ₖ⋆ Γ
                             → w ⊩ₖ A


-- Accessibility
mutual
  rel : ∀ {{𝔐 : 𝔎}} {A w w′} → w′ ≥ w → w ⊩ A
                             → w′ ⊩ A
  rel {ᵗᵛ x}  η v = relᵥ η v
  rel {A ⊃ B} η f = λ η′ → f (η ∘ₐ η′)
  rel {A ∧ B} η p = relₖ {A} η (proj₁ p) , relₖ {B} η (proj₂ p)
  rel {TT}    η t = tt
  rel {□ A}   η p = ᵐrelₖ η p

  relₖ : ∀ {{𝔐 : 𝔎}} {A w w′} → w′ ≥ w → w ⊩ₖ A
                              → w′ ⊩ₖ A
  relₖ η k = λ η′ f → k (η ∘ₐ η′) f

  ᵐrelₖ : ∀ {{𝔐 : 𝔎}} {A w w′} → w′ ≥ w → w ᵐ⊩ₖ A
                               → w′ ᵐ⊩ₖ A
  ᵐrelₖ {A} η p = ᵐren ᵐ⌊ η ⌋ₐ (syn p) , relₖ {A} η (sem p)


relₖ⋆ : ∀ {{𝔐 : 𝔎}} {Ξ w w′} → w′ ≥ w → w ⊩ₖ⋆ Ξ
                             → w′ ⊩ₖ⋆ Ξ
-- TODO: Why does Agda require me to add seemingly unused annotations here?
-- relₖ⋆ η γ = mapAll (relₖ η) γ
relₖ⋆ η γ = mapₐ (λ {A} k {_} {_} → relₖ {A} η (k {_})) γ

ᵐrelₖ⋆ : ∀ {{𝔐 : 𝔎}} {Ξ w w′} → w′ ≥ w → w ᵐ⊩ₖ⋆ Ξ
                              → w′ ᵐ⊩ₖ⋆ Ξ
ᵐrelₖ⋆ η δ = mapₐ (ᵐrelₖ η) δ


-- Kripke continuation monad
unit : ∀ {{𝔐 : 𝔎}} {A w} → w ⊩ A
                           → w ⊩ₖ A
unit {A} a = λ η f →
               f idₐ (rel {A} η a)

bind : ∀ {{𝔐 : 𝔎}} {A C w} → w ⊩ₖ A → (∀ {w′} → w′ ≥ w → w′ ⊩ A
                                                 → w′ ⊩ₖ C)
                           → w ⊩ₖ C
bind k f = λ η f′ →
             k η (λ η′ a →
               f (η ∘ₐ η′) a idₐ (λ η″ b →
                 f′ (η′ ∘ₐ η″) b))


lookup : ∀ {{𝔐 : 𝔎}} {Ξ A w} → w ⊩ₖ⋆ Ξ → Ξ ∋ A
                             → w ⊩ₖ A
lookup γ i = lookupₐ γ i


-- Soundness
↓ : ∀ {Δ Γ A} → Δ ⁏ Γ ⊢ A
              → Δ ⁏ Γ ⊨ A
↓ (ᵐᵛ i)            = λ δ γ → lookup (sem⋆ δ) i
↓ (ᵛ i)             = λ δ γ → lookup γ i
↓ (ƛ {A} {B} 𝒟)     = λ δ γ → unit {A ⊃ B} (λ η k →
                        ↓ 𝒟 (ᵐrelₖ⋆ η δ) (relₖ⋆ η γ , k))
↓ (_$_ {A} {B} 𝒟 ℰ) = λ δ γ → bind {A ⊃ B} {B} (↓ 𝒟 δ γ) (λ η f →
                        f idₐ (↓ ℰ (ᵐrelₖ⋆ η δ) (relₖ⋆ η γ)))
↓ (_,_ {A} {B} 𝒟 ℰ) = λ δ γ → unit {A ∧ B} (↓ 𝒟 δ γ , ↓ ℰ δ γ)
↓ (π₁ {A} {B} 𝒟)    = λ δ γ → bind {A ∧ B} {A} (↓ 𝒟 δ γ) (λ η p →
                        proj₁ p)
↓ (π₂ {A} {B} 𝒟)    = λ δ γ → bind {A ∧ B} {B} (↓ 𝒟 δ γ) (λ η p →
                        proj₂ p)
↓ tt                = λ δ γ → unit {TT} tt
↓ (⌜_⌝ {A} 𝒟)       = λ δ γ → unit {□ A} (ᵐsub (syn⋆ δ) 𝒟 , ↓ 𝒟 δ ∅)
↓ (⌞_⌟ {A} {C} 𝒟 ℰ) = λ δ γ → bind {□ A} {C} (↓ 𝒟 δ γ) (λ η p →
                        ↓ ℰ (ᵐrelₖ⋆ η δ , p) (relₖ⋆ η γ))


--------------------------------------------------------------------------------
--
-- Completeness


-- Universal model
instance
  𝔐ᵤ : 𝔎
  𝔐ᵤ = record
         { 𝒲    = Cx
         ; _𝒱_  = _𝒱ᵤ_
         ; _≥_  = _⊇²_
         ; idₐ  = idᵣ²
         ; _∘ₐ_ = _∘ᵣ²_
         ; relᵥ = renₙₘ²
         ; ⌊_⌋  = id
         ; ⌊_⌋ₐ = id
         }
    where
      infix 3 _𝒱ᵤ_
      _𝒱ᵤ_ : Cx → TVar → Set
      Δ ⁏ Γ 𝒱ᵤ x = Δ ⁏ Γ ⊢ₙₘ ᵗᵛ x


-- Soundness and completeness with respect to the universal model
mutual
  ↓ᵤ : ∀ {A Δ Γ} → Δ ⁏ Γ ⊢ₙₜ A
                 → Δ ⁏ Γ ⊩ₖ A
  ↓ᵤ {ᵗᵛ x}  𝒟 = unit {ᵗᵛ x} (ⁿᵗ 𝒟)
  ↓ᵤ {A ⊃ B} 𝒟 = unit {A ⊃ B} (λ η k → ↓ᵤ (renₙₜ² η 𝒟 $ ↑ᵤ k))
  ↓ᵤ {A ∧ B} 𝒟 = unit {A ∧ B} (↓ᵤ (π₁ 𝒟) , ↓ᵤ (π₂ 𝒟))
  ↓ᵤ {TT}    𝒟 = unit {TT} tt
  ↓ᵤ {□ A}   𝒟 = λ η f → ⌞ renₙₜ² η 𝒟 ⌟ (f (ᵐwk² idᵣ²) (ᵐᵛ zero , ↓ᵤ (ᵐᵛ zero)))

  ↑ᵤ : ∀ {A Δ Γ} → Δ ⁏ Γ ⊩ₖ A
                 → Δ ⁏ Γ ⊢ₙₘ A
  ↑ᵤ {ᵗᵛ x}  k = k idᵣ² (λ η v → v)
  ↑ᵤ {A ⊃ B} k = k idᵣ² (λ η f → ƛ (↑ᵤ (f (wk² idᵣ²) (↓ᵤ (ᵛ zero)))))
  ↑ᵤ {A ∧ B} k = k idᵣ² (λ η p → ↑ᵤ (proj₁ p) , ↑ᵤ (proj₂ p))
  ↑ᵤ {TT}    k = k idᵣ² (λ η t → tt)
  ↑ᵤ {□ A}   k = k idᵣ² (λ η p → ⌜ syn p ⌝)


ᵐidₑ : ∀ {Δ Γ} → Δ ⁏ Γ ᵐ⊩ₖ⋆ Δ
ᵐidₑ {∅}     = ∅
ᵐidₑ {Δ , A} = ᵐrelₖ⋆ (ᵐwk² idᵣ²) ᵐidₑ , (ᵐᵛ zero , ↓ᵤ (ᵐᵛ zero))

idₑ : ∀ {Γ Δ} → Δ ⁏ Γ ⊩ₖ⋆ Γ
idₑ {∅}     = ∅
idₑ {Γ , A} = relₖ⋆ (wk² idᵣ²) idₑ , ↓ᵤ (ᵛ zero)


-- Completeness
↑ : ∀ {Δ Γ A} → Δ ⁏ Γ ⊨ A
              → Δ ⁏ Γ ⊢ₙₘ A
↑ f = ↑ᵤ (f ᵐidₑ idₑ)


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
--                    → 𝒟 ∼ ƛ (ren (wk idᵣ) 𝒟 $ ᵛ0)

test∼exp⊃ : test∼ {∅} {∅ , "A" ⊃ "B"}
                  ᵛ0
                  (ƛ (ren (wk idᵣ) ᵛ0 $ ᵛ0))
test∼exp⊃ = refl


-- exp∧ : ∀ {Δ Γ A B} → (𝒟 : Δ ⁏ Γ ⊢ A ∧ B)
--                    → 𝒟 ∼ π₁ 𝒟 , π₂ 𝒟

test∼exp∧ : test∼ {∅} {∅ , "A" ∧ "B"}
                  ᵛ0
                  (π₁ ᵛ0 , π₂ ᵛ0)
test∼exp∧ = refl


-- expTT : ∀ {Δ Γ} → (𝒟 : Δ ⁏ Γ ⊢ 𝔗)
--                 → 𝒟 ∼ tt

test∼expTT : test∼ {∅} {∅ , TT}
                   ᵛ0
                   tt
test∼expTT = refl


-- exp□ : ∀ {Δ Γ} → (𝒟 : Δ ⁏ Γ ⊢ □ A)
--                → 𝒟 ∼ ⌞ 𝒟 ⌟ ⌜ ᵐᵛ0 ⌝

test∼exp□ : test∼ {∅} {∅ , □ "A"}
                  ᵛ0
                  (⌞ ᵛ0 ⌟ ⌜ ᵐᵛ0 ⌝)
test∼exp□ = refl


-- comm□$ : ∀ {Δ Γ A B} → (𝒬 : Δ ⁏ Γ ⊢ □ (A ⊃ B))
--                         (𝒟 : Δ , A ⊃ B ⁏ Γ ⊢ A ⊃ B) (ℰ : Δ ⁏ Γ ⊢ A)
--                      → (⌞ 𝒬 ⌟ 𝒟) $ ℰ ∼ ⌞ 𝒬 ⌟ (𝒟 $ (ᵐren (wk idᵣ) ℰ))

test∼comm□$ : test∼ {∅} {∅ , □ ("A" ⊃ "B") , "A"}
                    ((⌞ ᵛ1 ⌟ ᵐᵛ0) $ ᵛ0)
                    (⌞ ᵛ1 ⌟ (ᵐᵛ0 $ ᵐren (wk idᵣ) ᵛ0))
test∼comm□$ = refl


-- comm□⌞⌟ : ∀ {Δ Γ A C} → (𝒬 : Δ ⁏ Γ ⊢ □ □ A)
--                          (𝒟 : Δ , □ A ⁏ Γ ⊢ □ A) (ℰ : Δ , A ⁏ Γ ⊢ C)
--                       → ⌞ (⌞ 𝒬 ⌟ 𝒟) ⌟ ℰ ∼ ⌞ 𝒬 ⌟ (⌞ 𝒟 ⌟ (ᵐren (wk idᵣ) ℰ))

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
--                      → TT $ ⌜ 𝒟 ⌝ ∼ ⌜ 𝒟 ⌝

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
