{-# OPTIONS --rewriting #-}

module S4WithTerms where

open import Prelude public


--------------------------------------------------------------------------------
--
-- Syntax


-- Type variables
data TVar : Set where
  tvar : String → TVar

{-# COMPILE GHC TVar = data TVar (TVar) #-}

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

{-# COMPILE GHC Tp = data Tp (TV | (:=>) | (:&&) | Top | Box) #-}

instance
  typeIsString : IsString Tp
  typeIsString =
    record
      { Constraint = λ s → ⊤
      ; fromString = λ s → ᵗᵛ (tvar s)
      }


injᵗᵛ : ∀ {x₁ x₂} → ᵗᵛ x₁ ≡ ᵗᵛ x₂ → x₁ ≡ x₂
injᵗᵛ refl = refl

inj⊃₁ : ∀ {A₁ A₂ B₁ B₂} → A₁ ⊃ B₁ ≡ A₂ ⊃ B₂ → A₁ ≡ A₂
inj⊃₁ refl = refl

inj⊃₂ : ∀ {A₁ A₂ B₁ B₂} → A₁ ⊃ B₁ ≡ A₂ ⊃ B₂ → B₁ ≡ B₂
inj⊃₂ refl = refl

inj∧₁ : ∀ {A₁ A₂ B₁ B₂} → A₁ ∧ B₁ ≡ A₂ ∧ B₂ → A₁ ≡ A₂
inj∧₁ refl = refl

inj∧₂ : ∀ {A₁ A₂ B₁ B₂} → A₁ ∧ B₁ ≡ A₂ ∧ B₂ → B₁ ≡ B₂
inj∧₂ refl = refl

inj□ : ∀ {A₁ A₂} → □ A₁ ≡ □ A₂ → A₁ ≡ A₂
inj□ refl = refl


_≟ₜₚ_ : (A₁ A₂ : Tp) → Dec (A₁ ≡ A₂)

ᵗᵛ x₁ ≟ₜₚ ᵗᵛ x₂     with x₁ ≟ₜᵥ x₂
...                 | yes refl = yes refl
...                 | no x₁≢x₂ = no (x₁≢x₂ ∘ injᵗᵛ)
ᵗᵛ x₁ ≟ₜₚ (A₂ ⊃ B₂) = no (λ ())
ᵗᵛ x₁ ≟ₜₚ (A₂ ∧ B₂) = no (λ ())
ᵗᵛ x₁ ≟ₜₚ 𝕋         = no (λ ())
ᵗᵛ x₁ ≟ₜₚ (□ A₂)    = no (λ ())

(A₁ ⊃ B₁) ≟ₜₚ ᵗᵛ x₂     = no (λ ())
(A₁ ⊃ B₁) ≟ₜₚ (A₂ ⊃ B₂) with A₁ ≟ₜₚ A₂ | B₁ ≟ₜₚ B₂
...                     | yes refl | yes refl = yes refl
...                     | yes refl | no B₁≢B₂ = no (B₁≢B₂ ∘ inj⊃₂)
...                     | no A₁≢A₂ | _        = no (A₁≢A₂ ∘ inj⊃₁)
(A₁ ⊃ B₁) ≟ₜₚ (A₂ ∧ B₂) = no (λ ())
(A₁ ⊃ B₁) ≟ₜₚ 𝕋         = no (λ ())
(A₁ ⊃ B₁) ≟ₜₚ (□ A₂)    = no (λ ())

(A₁ ∧ B₁) ≟ₜₚ ᵗᵛ x₂     = no (λ ())
(A₁ ∧ B₁) ≟ₜₚ (A₂ ⊃ B₂) = no (λ ())
(A₁ ∧ B₁) ≟ₜₚ (A₂ ∧ B₂) with A₁ ≟ₜₚ A₂ | B₁ ≟ₜₚ B₂
...                     | yes refl | yes refl = yes refl
...                     | yes refl | no B₁≢B₂ = no (B₁≢B₂ ∘ inj∧₂)
...                     | no A₁≢A₂ | _        = no (A₁≢A₂ ∘ inj∧₁)
(A₁ ∧ B₁) ≟ₜₚ 𝕋         = no (λ ())
(A₁ ∧ B₁) ≟ₜₚ (□ A₂)    = no (λ ())

𝕋 ≟ₜₚ ᵗᵛ x₂     = no (λ ())
𝕋 ≟ₜₚ (A₂ ⊃ B₂) = no (λ ())
𝕋 ≟ₜₚ (A₂ ∧ B₂) = no (λ ())
𝕋 ≟ₜₚ 𝕋         = yes refl
𝕋 ≟ₜₚ (□ A₂)    = no (λ ())

(□ A₁) ≟ₜₚ ᵗᵛ x₂     = no (λ ())
(□ A₁) ≟ₜₚ (A₂ ⊃ B₂) = no (λ ())
(□ A₁) ≟ₜₚ (A₂ ∧ B₂) = no (λ ())
(□ A₁) ≟ₜₚ 𝕋         = no (λ ())
(□ A₁) ≟ₜₚ (□ A₂)    with A₁ ≟ₜₚ A₂
...                  | yes refl = yes refl
...                  | no A₁≢A₂ = no (A₁≢A₂ ∘ inj□)


-- Modal variables
data MVar : Set where
  mvar : String → MVar

{-# COMPILE GHC MVar = data MVar (MVar) #-}

injmvar : ∀ {s₁ s₂} → mvar s₁ ≡ mvar s₂ → s₁ ≡ s₂
injmvar refl = refl

_≟ₘᵥ_ : (x₁ x₂ : MVar) → Dec (x₁ ≡ x₂)
mvar s₁ ≟ₘᵥ mvar s₂ = mapDec (mvar &_) injmvar (s₁ ≟ₛ s₂)

instance
  mvarIsString : IsString MVar
  mvarIsString =
    record
      { Constraint = λ s → ⊤
      ; fromString = λ s → mvar s
      }


-- Regular variables
data RVar : Set where
  rvar : String → RVar

{-# COMPILE GHC RVar = data RVar (RVar) #-}

injrvar : ∀ {s₁ s₂} → rvar s₁ ≡ rvar s₂ → s₁ ≡ s₂
injrvar refl = refl

_≟ᵣᵥ_ : (x₁ x₂ : RVar) → Dec (x₁ ≡ x₂)
rvar s₁ ≟ᵣᵥ rvar s₂ = mapDec (rvar &_) injrvar (s₁ ≟ₛ s₂)

instance
  rvarIsString : IsString RVar
  rvarIsString =
    record
      { Constraint = λ s → ⊤
      ; fromString = λ s → rvar s
      }


-- Terms
infixl 10 _⦂_
data Tm : Set where
  ᵐᵛ     : (x : MVar) → Tm
  ʳᵛ     : (x : RVar) → Tm
  ƛ_∙_   : (x : RVar) (M : Tm) → Tm
  _$_    : (M N : Tm) → Tm
  _,_    : (M N : Tm) → Tm
  π₁     : (M : Tm) → Tm
  π₂     : (M : Tm) → Tm
  tt     : Tm
  ⌜_⌝    : (M : Tm) → Tm
  ⌞_⌟_∙_ : (M : Tm) (x : MVar) (N : Tm) → Tm
  _⦂_    : (M : Tm) (A : Tp) → Tm

{-# COMPILE GHC Tm = data Tm (MV | RV | Lam | (:$) | (:,) | Pi1 | Pi2 | TT | Quo | Unq | (:::)) #-}

injᵐᵛ : ∀ {x₁ x₂} → ᵐᵛ x₁ ≡ ᵐᵛ x₂ → x₁ ≡ x₂
injᵐᵛ refl = refl

injʳᵛ : ∀ {x₁ x₂} → ʳᵛ x₁ ≡ ʳᵛ x₂ → x₁ ≡ x₂
injʳᵛ refl = refl

injƛ₁ : ∀ {x₁ x₂ M₁ M₂} → ƛ x₁ ∙ M₁ ≡ ƛ x₂ ∙ M₂ → x₁ ≡ x₂
injƛ₁ refl = refl

injƛ₂ : ∀ {x₁ x₂ M₁ M₂} → ƛ x₁ ∙ M₁ ≡ ƛ x₂ ∙ M₂ → M₁ ≡ M₂
injƛ₂ refl = refl

inj$₁ : ∀ {M₁ M₂ N₁ N₂} → M₁ $ N₁ ≡ M₂ $ N₂ → M₁ ≡ M₂
inj$₁ refl = refl

inj$₂ : ∀ {M₁ M₂ N₁ N₂} → M₁ $ N₁ ≡ M₂ $ N₂ → N₁ ≡ N₂
inj$₂ refl = refl

inj,₁ : ∀ {M₁ M₂ N₁ N₂} → M₁ Tm., N₁ ≡ M₂ , N₂ → M₁ ≡ M₂
inj,₁ refl = refl

inj,₂ : ∀ {M₁ M₂ N₁ N₂} → M₁ Tm., N₁ ≡ M₂ , N₂ → N₁ ≡ N₂
inj,₂ refl = refl

injπ₁ : ∀ {M₁ M₂} → π₁ M₁ ≡ π₁ M₂ → M₁ ≡ M₂
injπ₁ refl = refl

injπ₂ : ∀ {M₁ M₂} → π₂ M₁ ≡ π₂ M₂ → M₁ ≡ M₂
injπ₂ refl = refl

inj⌜⌝ : ∀ {M₁ M₂} → ⌜ M₁ ⌝ ≡ ⌜ M₂ ⌝ → M₁ ≡ M₂
inj⌜⌝ refl = refl

inj⌞⌟₁ : ∀ {M₁ M₂ x₁ x₂ N₁ N₂} → ⌞ M₁ ⌟ x₁ ∙ N₁ ≡ ⌞ M₂ ⌟ x₂ ∙ N₂ → M₁ ≡ M₂
inj⌞⌟₁ refl = refl

inj⌞⌟₂ : ∀ {M₁ M₂ x₁ x₂ N₁ N₂} → ⌞ M₁ ⌟ x₁ ∙ N₁ ≡ ⌞ M₂ ⌟ x₂ ∙ N₂ → x₁ ≡ x₂
inj⌞⌟₂ refl = refl

inj⌞⌟₃ : ∀ {M₁ M₂ x₁ x₂ N₁ N₂} → ⌞ M₁ ⌟ x₁ ∙ N₁ ≡ ⌞ M₂ ⌟ x₂ ∙ N₂ → N₁ ≡ N₂
inj⌞⌟₃ refl = refl

inj⦂₁ : ∀ {M₁ M₂ A₁ A₂} → M₁ ⦂ A₁ ≡ M₂ ⦂ A₂ → M₁ ≡ M₂
inj⦂₁ refl = refl

inj⦂₂ : ∀ {M₁ M₂ A₁ A₂} → M₁ ⦂ A₁ ≡ M₂ ⦂ A₂ → A₁ ≡ A₂
inj⦂₂ refl = refl


_≟ₜₘ_ : (M₁ M₂ : Tm) → Dec (M₁ ≡ M₂)

(ᵐᵛ x₁) ≟ₜₘ (ᵐᵛ x₂)          with x₁ ≟ₘᵥ x₂
...                          | yes refl = yes refl
...                          | no x₁≢x₂ = no (x₁≢x₂ ∘ injᵐᵛ)
(ᵐᵛ x₁) ≟ₜₘ (ʳᵛ x₂)          = no (λ ())
(ᵐᵛ x₁) ≟ₜₘ (ƛ x₂ ∙ M₂)      = no (λ ())
(ᵐᵛ x₁) ≟ₜₘ (M₂ $ N₂)        = no (λ ())
(ᵐᵛ x₁) ≟ₜₘ (M₂ , ℕ₂)        = no (λ ())
(ᵐᵛ x₁) ≟ₜₘ (π₁ M₂)          = no (λ ())
(ᵐᵛ x₁) ≟ₜₘ (π₂ M₂)          = no (λ ())
(ᵐᵛ x₁) ≟ₜₘ tt               = no (λ ())
(ᵐᵛ x₁) ≟ₜₘ ⌜ M₂ ⌝           = no (λ ())
(ᵐᵛ x₁) ≟ₜₘ (⌞ M₂ ⌟ x₂ ∙ N₂) = no (λ ())
(ᵐᵛ x₁) ≟ₜₘ (M₂ ⦂ A₂)        = no (λ ())

(ʳᵛ x₁) ≟ₜₘ (ᵐᵛ x₂)          = no (λ ())
(ʳᵛ x₁) ≟ₜₘ (ʳᵛ x₂)          with x₁ ≟ᵣᵥ x₂
...                          | yes refl = yes refl
...                          | no x₁≢x₂ = no (x₁≢x₂ ∘ injʳᵛ)
(ʳᵛ x₁) ≟ₜₘ (ƛ x₂ ∙ M₂)      = no (λ ())
(ʳᵛ x₁) ≟ₜₘ (M₂ $ N₂)        = no (λ ())
(ʳᵛ x₁) ≟ₜₘ (M₂ , N₂)        = no (λ ())
(ʳᵛ x₁) ≟ₜₘ (π₁ M₂)          = no (λ ())
(ʳᵛ x₁) ≟ₜₘ (π₂ M₂)          = no (λ ())
(ʳᵛ x₁) ≟ₜₘ tt               = no (λ ())
(ʳᵛ x₁) ≟ₜₘ ⌜ M₂ ⌝           = no (λ ())
(ʳᵛ x₁) ≟ₜₘ (⌞ M₂ ⌟ x₂ ∙ N₂) = no (λ ())
(ʳᵛ x₁) ≟ₜₘ (M₂ ⦂ A₂)        = no (λ ())

(ƛ x₁ ∙ M₁) ≟ₜₘ (ᵐᵛ x₂)          = no (λ ())
(ƛ x₁ ∙ M₁) ≟ₜₘ (ʳᵛ x₂)          = no (λ ())
(ƛ x₁ ∙ M₁) ≟ₜₘ (ƛ x₂ ∙ M₂)      with x₁ ≟ᵣᵥ x₂ | M₁ ≟ₜₘ M₂
...                              | yes refl | yes refl = yes refl
...                              | yes refl | no M₁≢M₂ = no (M₁≢M₂ ∘ injƛ₂)
...                              | no x₁≢x₂ | _        = no (x₁≢x₂ ∘ injƛ₁)
(ƛ x₁ ∙ M₁) ≟ₜₘ (M₂ $ N₂)        = no (λ ())
(ƛ x₁ ∙ M₁) ≟ₜₘ (M₂ , N₂)        = no (λ ())
(ƛ x₁ ∙ M₁) ≟ₜₘ (π₁ M₂)          = no (λ ())
(ƛ x₁ ∙ M₁) ≟ₜₘ (π₂ M₂)          = no (λ ())
(ƛ x₁ ∙ M₁) ≟ₜₘ tt               = no (λ ())
(ƛ x₁ ∙ M₁) ≟ₜₘ ⌜ M₂ ⌝           = no (λ ())
(ƛ x₁ ∙ M₁) ≟ₜₘ (⌞ M₂ ⌟ x₂ ∙ N₂) = no (λ ())
(ƛ x₁ ∙ M₁) ≟ₜₘ (M₂ ⦂ A₂)        = no (λ ())

(M₁ $ N₁) ≟ₜₘ (ᵐᵛ x₂)          = no (λ ())
(M₁ $ N₁) ≟ₜₘ (ʳᵛ x₂)          = no (λ ())
(M₁ $ N₁) ≟ₜₘ (ƛ x₂ ∙ M₂)      = no (λ ())
(M₁ $ N₁) ≟ₜₘ (M₂ $ N₂)        with M₁ ≟ₜₘ M₂ | N₁ ≟ₜₘ N₂
...                            | yes refl | yes refl = yes refl
...                            | yes refl | no N₁≢N₂ = no (N₁≢N₂ ∘ inj$₂)
...                            | no M₁≢M₂ | _        = no (M₁≢M₂ ∘ inj$₁)
(M₁ $ N₁) ≟ₜₘ (M₂ , N₂)        = no (λ ())
(M₁ $ N₁) ≟ₜₘ (π₁ M₂)          = no (λ ())
(M₁ $ N₁) ≟ₜₘ (π₂ M₂)          = no (λ ())
(M₁ $ N₁) ≟ₜₘ tt               = no (λ ())
(M₁ $ N₁) ≟ₜₘ ⌜ M₂ ⌝           = no (λ ())
(M₁ $ N₁) ≟ₜₘ (⌞ M₂ ⌟ x₂ ∙ N₂) = no (λ ())
(M₁ $ N₁) ≟ₜₘ (M₂ ⦂ A₂)        = no (λ ())

(M₁ , N₁) ≟ₜₘ (ᵐᵛ x₂)          = no (λ ())
(M₁ , N₁) ≟ₜₘ (ʳᵛ x₂)          = no (λ ())
(M₁ , N₁) ≟ₜₘ (ƛ x₂ ∙ M₂)      = no (λ ())
(M₁ , N₁) ≟ₜₘ (M₂ $ N₂)        = no (λ ())
(M₁ , N₁) ≟ₜₘ (M₂ , N₂)        with M₁ ≟ₜₘ M₂ | N₁ ≟ₜₘ N₂
...                            | yes refl | yes refl = yes refl
...                            | yes refl | no N₁≢N₂ = no (N₁≢N₂ ∘ inj,₂)
...                            | no M₁≢M₂ | _        = no (M₁≢M₂ ∘ inj,₁)
(M₁ , N₁) ≟ₜₘ (π₁ M₂)          = no (λ ())
(M₁ , N₁) ≟ₜₘ (π₂ M₂)          = no (λ ())
(M₁ , N₁) ≟ₜₘ tt               = no (λ ())
(M₁ , N₁) ≟ₜₘ ⌜ M₂ ⌝           = no (λ ())
(M₁ , N₁) ≟ₜₘ (⌞ M₂ ⌟ x₂ ∙ N₂) = no (λ ())
(M₁ , N₁) ≟ₜₘ (M₂ ⦂ A₂)        = no (λ ())

(π₁ M₁) ≟ₜₘ (ᵐᵛ x₂)          = no (λ ())
(π₁ M₁) ≟ₜₘ (ʳᵛ x₂)          = no (λ ())
(π₁ M₁) ≟ₜₘ (ƛ x₂ ∙ M₂)      = no (λ ())
(π₁ M₁) ≟ₜₘ (M₂ $ N₂)        = no (λ ())
(π₁ M₁) ≟ₜₘ (M₂ , N₂)        = no (λ ())
(π₁ M₁) ≟ₜₘ (π₁ M₂)          with M₁ ≟ₜₘ M₂
...                          | yes refl = yes refl
...                          | no M₁≢M₂ = no (M₁≢M₂ ∘ injπ₁)
(π₁ M₁) ≟ₜₘ (π₂ M₂)          = no (λ ())
(π₁ M₁) ≟ₜₘ tt               = no (λ ())
(π₁ M₁) ≟ₜₘ ⌜ M₂ ⌝           = no (λ ())
(π₁ M₁) ≟ₜₘ (⌞ M₂ ⌟ x₂ ∙ N₂) = no (λ ())
(π₁ M₁) ≟ₜₘ (M₂ ⦂ A₂)        = no (λ ())

(π₂ M₁) ≟ₜₘ (ᵐᵛ x₂)          = no (λ ())
(π₂ M₁) ≟ₜₘ (ʳᵛ x₂)          = no (λ ())
(π₂ M₁) ≟ₜₘ (ƛ x₂ ∙ M₂)      = no (λ ())
(π₂ M₁) ≟ₜₘ (M₂ $ N₂)        = no (λ ())
(π₂ M₁) ≟ₜₘ (M₂ , N₂)        = no (λ ())
(π₂ M₁) ≟ₜₘ (π₁ M₂)          = no (λ ())
(π₂ M₁) ≟ₜₘ (π₂ M₂)          with M₁ ≟ₜₘ M₂
...                          | yes refl = yes refl
...                          | no M₁≢M₂ = no (M₁≢M₂ ∘ injπ₂)
(π₂ M₁) ≟ₜₘ tt               = no (λ ())
(π₂ M₁) ≟ₜₘ ⌜ M₂ ⌝           = no (λ ())
(π₂ M₁) ≟ₜₘ (⌞ M₂ ⌟ x₂ ∙ N₂) = no (λ ())
(π₂ M₁) ≟ₜₘ (M₂ ⦂ A₂)        = no (λ ())

tt ≟ₜₘ (ᵐᵛ x₂)          = no (λ ())
tt ≟ₜₘ (ʳᵛ x₂)          = no (λ ())
tt ≟ₜₘ (ƛ x₂ ∙ M₂)      = no (λ ())
tt ≟ₜₘ (M₂ $ N₂)        = no (λ ())
tt ≟ₜₘ (M₂ , N₂)        = no (λ ())
tt ≟ₜₘ (π₁ M₂)          = no (λ ())
tt ≟ₜₘ (π₂ M₂)          = no (λ ())
tt ≟ₜₘ tt               = yes refl
tt ≟ₜₘ ⌜ M₂ ⌝           = no (λ ())
tt ≟ₜₘ (⌞ M₂ ⌟ x₂ ∙ N₂) = no (λ ())
tt ≟ₜₘ (M₂ ⦂ A₂)        = no (λ ())

⌜ M₁ ⌝ ≟ₜₘ (ᵐᵛ x₂)          = no (λ ())
⌜ M₁ ⌝ ≟ₜₘ (ʳᵛ x₂)          = no (λ ())
⌜ M₁ ⌝ ≟ₜₘ (ƛ x₂ ∙ M₂)      = no (λ ())
⌜ M₁ ⌝ ≟ₜₘ (M₂ $ N₂)        = no (λ ())
⌜ M₁ ⌝ ≟ₜₘ (M₂ , N₂)        = no (λ ())
⌜ M₁ ⌝ ≟ₜₘ (π₁ M₂)          = no (λ ())
⌜ M₁ ⌝ ≟ₜₘ (π₂ M₂)          = no (λ ())
⌜ M₁ ⌝ ≟ₜₘ tt               = no (λ ())
⌜ M₁ ⌝ ≟ₜₘ ⌜ M₂ ⌝           with M₁ ≟ₜₘ M₂
...                         | yes refl = yes refl
...                         | no M₁≢M₂ = no (M₁≢M₂ ∘ inj⌜⌝)
⌜ M₁ ⌝ ≟ₜₘ (⌞ M₂ ⌟ x₂ ∙ N₂) = no (λ ())
⌜ M₁ ⌝ ≟ₜₘ (M₂ ⦂ A₂)        = no (λ ())

(⌞ M₁ ⌟ x₁ ∙ N₁) ≟ₜₘ (ᵐᵛ x₂)          = no (λ ())
(⌞ M₁ ⌟ x₁ ∙ N₁) ≟ₜₘ (ʳᵛ x₂)          = no (λ ())
(⌞ M₁ ⌟ x₁ ∙ N₁) ≟ₜₘ (ƛ x₂ ∙ M₂)      = no (λ ())
(⌞ M₁ ⌟ x₁ ∙ N₁) ≟ₜₘ (M₂ $ N₂)        = no (λ ())
(⌞ M₁ ⌟ x₁ ∙ N₁) ≟ₜₘ (M₂ , N₂)        = no (λ ())
(⌞ M₁ ⌟ x₁ ∙ N₁) ≟ₜₘ (π₁ M₂)          = no (λ ())
(⌞ M₁ ⌟ x₁ ∙ N₁) ≟ₜₘ (π₂ M₂)          = no (λ ())
(⌞ M₁ ⌟ x₁ ∙ N₁) ≟ₜₘ tt               = no (λ ())
(⌞ M₁ ⌟ x₁ ∙ N₁) ≟ₜₘ ⌜ M₂ ⌝           = no (λ ())
(⌞ M₁ ⌟ x₁ ∙ N₁) ≟ₜₘ (⌞ M₂ ⌟ x₂ ∙ N₂) with M₁ ≟ₜₘ M₂ | x₁ ≟ₘᵥ x₂ | N₁ ≟ₜₘ N₂
...                                   | yes refl | yes refl | yes refl = yes refl
...                                   | yes refl | yes refl | no N₁≢N₂ = no (N₁≢N₂ ∘ inj⌞⌟₃)
...                                   | yes refl | no x₁≢x₂ | _        = no (x₁≢x₂ ∘ inj⌞⌟₂)
...                                   | no M₁≢M₂ | _        | _        = no (M₁≢M₂ ∘ inj⌞⌟₁)
(⌞ M₁ ⌟ x₁ ∙ N₁) ≟ₜₘ (M₂ ⦂ A₂)        = no (λ ())

(M₁ ⦂ A₁) ≟ₜₘ (ᵐᵛ x₂)          = no (λ ())
(M₁ ⦂ A₁) ≟ₜₘ (ʳᵛ x₂)          = no (λ ())
(M₁ ⦂ A₁) ≟ₜₘ (ƛ x₂ ∙ M₂)      = no (λ ())
(M₁ ⦂ A₁) ≟ₜₘ (M₂ $ N₂)        = no (λ ())
(M₁ ⦂ A₁) ≟ₜₘ (M₂ , N₂)        = no (λ ())
(M₁ ⦂ A₁) ≟ₜₘ (π₁ M₂)          = no (λ ())
(M₁ ⦂ A₁) ≟ₜₘ (π₂ M₂)          = no (λ ())
(M₁ ⦂ A₁) ≟ₜₘ tt               = no (λ ())
(M₁ ⦂ A₁) ≟ₜₘ ⌜ M₂ ⌝           = no (λ ())
(M₁ ⦂ A₁) ≟ₜₘ (⌞ M₂ ⌟ x₂ ∙ N₂) = no (λ ())
(M₁ ⦂ A₁) ≟ₜₘ (M₂ ⦂ A₂)        with M₁ ≟ₜₘ M₂ | A₁ ≟ₜₚ A₂
...                            | yes refl | yes refl = yes refl
...                            | yes refl | no A₁≢A₂ = no (A₁≢A₂ ∘ inj⦂₂)
...                            | no M₁≢M₂ | _        = no (M₁≢M₂ ∘ inj⦂₁)


-- Contexts
Cx : Set
Cx = List (MVar × Tp) × List (RVar × Tp)


-- Syntactic entailment
infix 3 _⊢_∷_
data _⊢_∷_ : Cx → Tm → Tp → Set
  where
    ᵐᵛ_#_  : ∀ {A Δ Γ} → (x : MVar) (i : Δ ∋ (x , A))
                       → Δ ⁏ Γ ⊢ ᵐᵛ x ∷ A

    ʳᵛ_#_  : ∀ {A Δ Γ} → (x : RVar) (i : Γ ∋ (x , A))
                       → Δ ⁏ Γ ⊢ ʳᵛ x ∷ A

    ƛ_∙_   : ∀ {A B M Δ Γ} → (x : RVar) (𝒟 : Δ ⁏ Γ , (x , A) ⊢ M ∷ B)
                           → Δ ⁏ Γ ⊢ ƛ x ∙ M ∷ A ⊃ B

    _$_    : ∀ {A B M N Δ Γ} → (𝒟 : Δ ⁏ Γ ⊢ M ∷ A ⊃ B) (ℰ : Δ ⁏ Γ ⊢ N ∷ A)
                             → Δ ⁏ Γ ⊢ M $ N ∷ B

    _,_    : ∀ {A B M N Δ Γ} → (𝒟 : Δ ⁏ Γ ⊢ M ∷ A) (ℰ : Δ ⁏ Γ ⊢ N ∷ B)
                             → Δ ⁏ Γ ⊢ M , N ∷ A ∧ B

    π₁     : ∀ {A B M Δ Γ} → (𝒟 : Δ ⁏ Γ ⊢ M ∷ A ∧ B)
                           → Δ ⁏ Γ ⊢ π₁ M ∷ A

    π₂     : ∀ {A B M Δ Γ} → (𝒟 : Δ ⁏ Γ ⊢ M ∷ A ∧ B)
                           → Δ ⁏ Γ ⊢ π₂ M ∷ B

    tt     : ∀ {Δ Γ} → Δ ⁏ Γ ⊢ tt ∷ 𝕋

    ⌜_⌝    : ∀ {A M Δ Γ} → (𝒟 : Δ ⁏ ∅ ⊢ M ∷ A)
                         → Δ ⁏ Γ ⊢ ⌜ M ⌝ ∷ □ A

    ⌞_⌟_∙_ : ∀ {A C M N Δ Γ} → (𝒟 : Δ ⁏ Γ ⊢ M ∷ □ A) (x : MVar) (ℰ : Δ , (x , A) ⁏ Γ ⊢ N ∷ C)
                             → Δ ⁏ Γ ⊢ ⌞ M ⌟ x ∙ N ∷ C

    _⦂_    : ∀ {A M Δ Γ} → (𝒟 : Δ ⁏ Γ ⊢ M ∷ A) (A′ : Tp) {{_ : A ≡ A′}}
                         → Δ ⁏ Γ ⊢ M ⦂ A ∷ A


-- Normal and neutral forms
-- NOTE: Almost the same as bidirectional syntactic entailment
mutual
  infix 3 _⊢ₙₘ_∷_
  data _⊢ₙₘ_∷_ : Cx → Tm → Tp → Set
    where
      ƛ_∙_   : ∀ {A B M Δ Γ} → (x : RVar) (𝒟 : Δ ⁏ Γ , (x , A) ⊢ₙₘ M ∷ B)
                             → Δ ⁏ Γ ⊢ₙₘ ƛ x ∙ M ∷ A ⊃ B

      _,_    : ∀ {A B M N Δ Γ} → (𝒟 : Δ ⁏ Γ ⊢ₙₘ M ∷ A) (ℰ : Δ ⁏ Γ ⊢ₙₘ N ∷ B)
                               → Δ ⁏ Γ ⊢ₙₘ M , N ∷ A ∧ B

      tt     : ∀ {Δ Γ} → Δ ⁏ Γ ⊢ₙₘ tt ∷ 𝕋

      -- NOTE: We treat the premise of the □ introduction rule specially,
      -- in order to represet non-normal forms  (Davies-Pfenning 2001, p. 12)
      ⌜_⌝    : ∀ {A M Δ Γ} → (𝒟 : Δ ⁏ ∅ ⊢ M ∷ A)
                           → Δ ⁏ Γ ⊢ₙₘ ⌜ M ⌝ ∷ □ A

      ⌞_⌟_∙_ : ∀ {A C M N Δ Γ} → (𝒟 : Δ ⁏ Γ ⊢ₙₜ M ∷ □ A) (x : MVar) (ℰ : Δ , (x , A) ⁏ Γ ⊢ₙₘ N ∷ C)
                               → Δ ⁏ Γ ⊢ₙₘ ⌞ M ⌟ x ∙ N ∷ C

      -- NOTE: We embed neutral forms only at base types,
      -- in order to guarantee that normal forms are βη-normal
      ⁿᵗ     : ∀ {x M Δ Γ} → (𝒟 : Δ ⁏ Γ ⊢ₙₜ M ∷ ᵗᵛ x)
                           → Δ ⁏ Γ ⊢ₙₘ M ∷ ᵗᵛ x

  infix 3 _⊢ₙₜ_∷_
  data _⊢ₙₜ_∷_ : Cx → Tm → Tp → Set
    where
      ᵐᵛ_#_ : ∀ {A Δ Γ} → (x : MVar) (i : Δ ∋ (x , A))
                        → Δ ⁏ Γ ⊢ₙₜ ᵐᵛ x ∷ A

      ʳᵛ_#_ : ∀ {A Δ Γ} → (x : RVar) (i : Γ ∋ (x , A))
                        → Δ ⁏ Γ ⊢ₙₜ ʳᵛ x ∷ A

      _$_   : ∀ {A B M N Δ Γ} → (𝒟 : Δ ⁏ Γ ⊢ₙₜ M ∷ A ⊃ B) (ℰ : Δ ⁏ Γ ⊢ₙₘ N ∷ A)
                              → Δ ⁏ Γ ⊢ₙₜ M $ N ∷ B

      π₁    : ∀ {A B M Δ Γ} → (𝒟 : Δ ⁏ Γ ⊢ₙₜ M ∷ A ∧ B)
                            → Δ ⁏ Γ ⊢ₙₜ π₁ M ∷ A

      π₂    : ∀ {A B M Δ Γ} → (𝒟 : Δ ⁏ Γ ⊢ₙₜ M ∷ A ∧ B)
                            → Δ ⁏ Γ ⊢ₙₜ π₂ M ∷ B


mutual
  embₙₘ : ∀ {Δ Γ M A} → Δ ⁏ Γ ⊢ₙₘ M ∷ A → Δ ⁏ Γ ⊢ M ∷ A
  embₙₘ (ƛ x ∙ 𝒟)     = ƛ x ∙ embₙₘ 𝒟
  embₙₘ (𝒟 , ℰ)       = embₙₘ 𝒟 , embₙₘ ℰ
  embₙₘ tt            = tt
  embₙₘ (⌜ 𝒟 ⌝)       = ⌜ 𝒟 ⌝
  embₙₘ (⌞ 𝒟 ⌟ x ∙ ℰ) = ⌞ embₙₜ 𝒟 ⌟ x ∙ embₙₘ ℰ
  embₙₘ (ⁿᵗ 𝒟)        = embₙₜ 𝒟

  embₙₜ : ∀ {Δ Γ M A} → Δ ⁏ Γ ⊢ₙₜ M ∷ A → Δ ⁏ Γ ⊢ M ∷ A
  embₙₜ (ᵐᵛ x # i) = ᵐᵛ x # i
  embₙₜ (ʳᵛ x # i) = ʳᵛ x # i
  embₙₜ (𝒟 $ ℰ)    = embₙₜ 𝒟 $ embₙₘ ℰ
  embₙₜ (π₁ 𝒟)     = π₁ (embₙₜ 𝒟)
  embₙₜ (π₂ 𝒟)     = π₂ (embₙₜ 𝒟)


--------------------------------------------------------------------------------
--
-- Renaming


mren : ∀ {Δ Δ′ Γ M A} → Δ′ ⊇ Δ → Δ ⁏ Γ ⊢ M ∷ A
                      → Δ′ ⁏ Γ ⊢ M ∷ A
mren η (ᵐᵛ x # i)    = ᵐᵛ x # lookupᵣ η i
mren η (ʳᵛ x # i)    = ʳᵛ x #  i
mren η (ƛ x ∙ 𝒟)     = ƛ x ∙ mren η 𝒟
mren η (𝒟 $ ℰ)       = mren η 𝒟 $ mren η ℰ
mren η (𝒟 , ℰ)       = mren η 𝒟 , mren η ℰ
mren η (π₁ 𝒟)        = π₁ (mren η 𝒟)
mren η (π₂ 𝒟)        = π₂ (mren η 𝒟)
mren η tt            = tt
mren η ⌜ 𝒟 ⌝         = ⌜ mren η 𝒟 ⌝
mren η (⌞ 𝒟 ⌟ x ∙ ℰ) = ⌞ mren η 𝒟 ⌟ x ∙ mren (liftᵣ η) ℰ
mren η (𝒟 ⦂ A)       = mren η 𝒟 ⦂ A

rren : ∀ {Δ Γ Γ′ M A} → Γ′ ⊇ Γ → Δ ⁏ Γ ⊢ M ∷ A
                      → Δ ⁏ Γ′ ⊢ M ∷ A
rren η (ᵐᵛ x # i)    = ᵐᵛ x # i
rren η (ʳᵛ x # i)    = ʳᵛ x # lookupᵣ η i
rren η (ƛ x ∙ 𝒟)     = ƛ x ∙ rren (liftᵣ η) 𝒟
rren η (𝒟 $ ℰ)       = rren η 𝒟 $ rren η ℰ
rren η (𝒟 , ℰ)       = rren η 𝒟 , rren η ℰ
rren η (π₁ 𝒟)        = π₁ (rren η 𝒟)
rren η (π₂ 𝒟)        = π₂ (rren η 𝒟)
rren η tt            = tt
rren η ⌜ 𝒟 ⌝         = ⌜ 𝒟 ⌝
rren η (⌞ 𝒟 ⌟ x ∙ ℰ) = ⌞ rren η 𝒟 ⌟ x ∙ rren η ℰ
rren η (𝒟 ⦂ A)       = rren η 𝒟 ⦂ A


mutual
  mrenₙₘ : ∀ {Δ Δ′ Γ M A} → Δ′ ⊇ Δ → Δ ⁏ Γ ⊢ₙₘ M ∷ A
                          → Δ′ ⁏ Γ ⊢ₙₘ M ∷ A
  mrenₙₘ η (ƛ x ∙ 𝒟)     = ƛ x ∙ mrenₙₘ η 𝒟
  mrenₙₘ η (𝒟 , ℰ)       = mrenₙₘ η 𝒟 , mrenₙₘ η ℰ
  mrenₙₘ η tt            = tt
  mrenₙₘ η ⌜ 𝒟 ⌝         = ⌜ mren η 𝒟 ⌝
  mrenₙₘ η (⌞ 𝒟 ⌟ x ∙ ℰ) = ⌞ mrenₙₜ η 𝒟 ⌟ x ∙ mrenₙₘ (liftᵣ η) ℰ
  mrenₙₘ η (ⁿᵗ 𝒟)        = ⁿᵗ (mrenₙₜ η 𝒟)

  mrenₙₜ : ∀ {Δ Δ′ Γ M A} → Δ′ ⊇ Δ → Δ ⁏ Γ ⊢ₙₜ M ∷ A
                          → Δ′ ⁏ Γ ⊢ₙₜ M ∷ A
  mrenₙₜ η (ᵐᵛ x # i) = ᵐᵛ x # lookupᵣ η i
  mrenₙₜ η (ʳᵛ x # i) = ʳᵛ x # i
  mrenₙₜ η (𝒟 $ ℰ)    = mrenₙₜ η 𝒟 $ mrenₙₘ η ℰ
  mrenₙₜ η (π₁ 𝒟)     = π₁ (mrenₙₜ η 𝒟)
  mrenₙₜ η (π₂ 𝒟)     = π₂ (mrenₙₜ η 𝒟)


mutual
  rrenₙₘ : ∀ {Δ Γ Γ′ M A} → Γ′ ⊇ Γ → Δ ⁏ Γ ⊢ₙₘ M ∷ A
                          → Δ ⁏ Γ′ ⊢ₙₘ M ∷ A
  rrenₙₘ η (ƛ x ∙ 𝒟)     = ƛ x ∙ rrenₙₘ (liftᵣ η) 𝒟
  rrenₙₘ η (𝒟 , ℰ)       = rrenₙₘ η 𝒟 , rrenₙₘ η ℰ
  rrenₙₘ η tt            = tt
  rrenₙₘ η ⌜ 𝒟 ⌝         = ⌜ 𝒟 ⌝
  rrenₙₘ η (⌞ 𝒟 ⌟ x ∙ ℰ) = ⌞ rrenₙₜ η 𝒟 ⌟ x ∙ rrenₙₘ η ℰ
  rrenₙₘ η (ⁿᵗ 𝒟)        = ⁿᵗ (rrenₙₜ η 𝒟)

  rrenₙₜ : ∀ {Δ Γ Γ′ M A} → Γ′ ⊇ Γ → Δ ⁏ Γ ⊢ₙₜ M ∷ A
                          → Δ ⁏ Γ′ ⊢ₙₜ M ∷ A
  rrenₙₜ η (ᵐᵛ x # i) = ᵐᵛ x # i
  rrenₙₜ η (ʳᵛ x # i) = ʳᵛ x # lookupᵣ η i
  rrenₙₜ η (𝒟 $ ℰ)    = rrenₙₜ η 𝒟 $ rrenₙₘ η ℰ
  rrenₙₜ η (π₁ 𝒟)     = π₁ (rrenₙₜ η 𝒟)
  rrenₙₜ η (π₂ 𝒟)     = π₂ (rrenₙₜ η 𝒟)


renₙₘ : ∀ {Δ Δ′ Γ Γ′ M A} → Δ′ ⁏ Γ′ ⊇² Δ ⁏ Γ → Δ ⁏ Γ ⊢ₙₘ M ∷ A
                          → Δ′ ⁏ Γ′ ⊢ₙₘ M ∷ A
renₙₘ η 𝒟 = (mrenₙₘ (proj₁ η) ∘ rrenₙₘ (proj₂ η)) 𝒟

renₙₜ : ∀ {Δ Δ′ Γ Γ′ M A} → Δ′ ⁏ Γ′ ⊇² Δ ⁏ Γ → Δ ⁏ Γ ⊢ₙₜ M ∷ A
                          → Δ′ ⁏ Γ′ ⊢ₙₜ M ∷ A
renₙₜ η 𝒟 = (mrenₙₜ (proj₁ η) ∘ rrenₙₜ (proj₂ η)) 𝒟


--------------------------------------------------------------------------------
--
-- Substitution


-- Simultaneous substitutions
infix 3 _⊢⋆_
_⊢⋆_ : Cx → List Tp → Set
Δ ⁏ Γ ⊢⋆ Ξ = All (λ A → Σ Tm (λ M → Δ ⁏ Γ ⊢ M ∷ A)) Ξ


mren⋆ : ∀ {Δ Δ′ Γ Ξ} → Δ′ ⊇ Δ → Δ ⁏ Γ ⊢⋆ Ξ
                     → Δ′ ⁏ Γ ⊢⋆ Ξ
mren⋆ η σ = mapAll (mapΣ id (mren η)) σ

rren⋆ : ∀ {Δ Γ Γ′ Ξ} → Γ′ ⊇ Γ → Δ ⁏ Γ ⊢⋆ Ξ
                     → Δ ⁏ Γ′ ⊢⋆ Ξ
rren⋆ η σ = mapAll (mapΣ id (rren η)) σ


mwkₛ : ∀ {x A Δ Γ Ξ} → Δ ⁏ Γ ⊢⋆ Ξ
                     → Δ , (x , A) ⁏ Γ ⊢⋆ Ξ
mwkₛ σ = mren⋆ (wkᵣ idᵣ) σ

rwkₛ : ∀ {x A Δ Γ Ξ} → Δ ⁏ Γ ⊢⋆ Ξ
                     → Δ ⁏ Γ , (x , A) ⊢⋆ Ξ
rwkₛ σ = rren⋆ (wkᵣ idᵣ) σ


mliftₛ : ∀ {x A Δ Γ Ξ} → Δ ⁏ Γ ⊢⋆ Ξ
                       → Δ , (x , A) ⁏ Γ ⊢⋆ Ξ , A
mliftₛ {x} σ = mwkₛ σ , (ᵐᵛ x , (ᵐᵛ x # zero))

rliftₛ : ∀ {x A Δ Γ Ξ} → Δ ⁏ Γ ⊢⋆ Ξ
                       → Δ ⁏ Γ , (x , A) ⊢⋆ Ξ , A
rliftₛ {x} σ = rwkₛ σ , (ʳᵛ x , (ʳᵛ x # zero))


midₛ : ∀ {Δ Γ} → Δ ⁏ Γ ⊢⋆ map proj₂ Δ
midₛ {∅}     = ∅
midₛ {Δ , A} = mliftₛ midₛ

ridₛ : ∀ {Γ Δ} → Δ ⁏ Γ ⊢⋆ map proj₂ Γ
ridₛ {∅}     = ∅
ridₛ {Γ , A} = rliftₛ ridₛ


lookupₛ : ∀ {Δ Γ Ξ A} → Δ ⁏ Γ ⊢⋆ Ξ → Ξ ∋ A
                      → Σ Tm (λ M → Δ ⁏ Γ ⊢ M ∷ A)
lookupₛ σ i = lookupAll σ i


-- Substitution

msubₜₘ : ∀ {Δ Γ Ξ M A} → {ξ : List MVar} {{p : length ξ ≡ length Ξ}}
                       → Δ ⁏ ∅ ⊢⋆ Ξ → zip ξ Ξ ⁏ Γ ⊢ M ∷ A
                       → Tm
msubₜₘ σ (ᵐᵛ x # i)          = proj₁ (lookupₛ σ (proj∋₂ i))
msubₜₘ σ (ʳᵛ x # i)          = ʳᵛ x
msubₜₘ σ (ƛ x ∙ 𝒟)           = ƛ x ∙ msubₜₘ σ 𝒟
msubₜₘ σ (𝒟 $ ℰ)             = msubₜₘ σ 𝒟 $ msubₜₘ σ ℰ
msubₜₘ σ (𝒟 , ℰ)             = msubₜₘ σ 𝒟 , msubₜₘ σ ℰ
msubₜₘ σ (π₁ 𝒟)              = π₁ (msubₜₘ σ 𝒟)
msubₜₘ σ (π₂ 𝒟)              = π₂ (msubₜₘ σ 𝒟)
msubₜₘ σ tt                  = tt
msubₜₘ σ ⌜ 𝒟 ⌝               = ⌜ msubₜₘ σ 𝒟 ⌝
msubₜₘ {{p}} σ (⌞ 𝒟 ⌟ x ∙ ℰ) = ⌞ msubₜₘ σ 𝒟 ⌟ x ∙ msubₜₘ {{foo p}} (mliftₛ {x} σ) ℰ
msubₜₘ σ (𝒟 ⦂ A)             = msubₜₘ σ 𝒟 ⦂ A


msub : ∀ {Δ Γ Ξ M A} → {ξ : List MVar} {{p : length ξ ≡ length Ξ}}
                     → (σ : Δ ⁏ ∅ ⊢⋆ Ξ) (𝒟 : zip ξ Ξ ⁏ Γ ⊢ M ∷ A)
                     → Δ ⁏ Γ ⊢ msubₜₘ σ 𝒟 ∷ A
msub σ (ᵐᵛ x # i)          = rren infᵣ (proj₂ (lookupₛ σ (proj∋₂ i)))
msub σ (ʳᵛ x # i)          = ʳᵛ x # i
msub σ (ƛ x ∙ 𝒟)           = ƛ x ∙ msub σ 𝒟
msub σ (𝒟 $ ℰ)             = msub σ 𝒟 $ msub σ ℰ
msub σ (𝒟 , ℰ)             = msub σ 𝒟 , msub σ ℰ
msub σ (π₁ 𝒟)              = π₁ (msub σ 𝒟)
msub σ (π₂ 𝒟)              = π₂ (msub σ 𝒟)
msub σ tt                  = tt
msub σ ⌜ 𝒟 ⌝               = ⌜ msub σ 𝒟 ⌝
msub {{p}} σ (⌞ 𝒟 ⌟ x ∙ ℰ) = ⌞ msub σ 𝒟 ⌟ x ∙ msub {{foo p}} (mliftₛ σ) ℰ
msub σ (_⦂_ 𝒟 A {{refl}})  = msub σ 𝒟 ⦂ A


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


ᵐ⌊_⌋ : ∀ {{𝔐 : 𝔎}} → 𝒲 → List (MVar × Tp)
ᵐ⌊ w ⌋ = proj₁ ⌊ w ⌋

ʳ⌊_⌋ : ∀ {{𝔐 : 𝔎}} → 𝒲 → List (RVar × Tp)
ʳ⌊ w ⌋ = proj₂ ⌊ w ⌋

ᵐ⌊_⌋ₐ : ∀ {{𝔐 : 𝔎}} {w w′} → w′ ≥ w
                           → ᵐ⌊ w′ ⌋ ⊇ ᵐ⌊ w ⌋
ᵐ⌊ η ⌋ₐ = proj₁ ⌊ η ⌋ₐ

ʳ⌊_⌋ₐ : ∀ {{𝔐 : 𝔎}} {w w′} → w′ ≥ w
                           → ʳ⌊ w′ ⌋ ⊇ ʳ⌊ w ⌋
ʳ⌊ η ⌋ₐ = proj₂ ⌊ η ⌋ₐ


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
                                                 → Σ Tm (λ M″ → ⌊ w″ ⌋ ⊢ₙₘ M″ ∷ C))
                     → Σ Tm (λ M′ → ⌊ w′ ⌋ ⊢ₙₘ M′ ∷ C)

  infix 3 _ᵐᵏ⊩_
  _ᵐᵏ⊩_ : ∀ {{𝔐 : 𝔎}} → 𝒲 → Tp → Set
  w ᵐᵏ⊩ A = Σ Tm (λ M → ᵐ⌊ w ⌋ ⁏ ∅ ⊢ M ∷ A) × w ᵏ⊩ A


syn : ∀ {{𝔐 : 𝔎}} {w A} → w ᵐᵏ⊩ A
                        → Σ Tm (λ M → ᵐ⌊ w ⌋ ⁏ ∅ ⊢ M ∷ A)
syn M𝒟k = proj₁ M𝒟k

sem : ∀ {{𝔐 : 𝔎}} {w A} → w ᵐᵏ⊩ A
                        → w ᵏ⊩ A
sem M𝒟k = proj₂ M𝒟k


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
Δ ⁏ Γ ⊨ A = ∀ {{𝔐 : 𝔎}} {w} → w ᵐᵏ⊩⋆ map proj₂ Δ → w ᵏ⊩⋆ map proj₂ Γ
                             → w ᵏ⊩ A


-- Accessibility
mutual
  acc : ∀ {{𝔐 : 𝔎}} {A w w′} → w′ ≥ w → w ⊩ A
                             → w′ ⊩ A
  acc {ᵗᵛ x}  η M𝒟 = accᵥ η M𝒟
  acc {A ⊃ B} η f = λ η′ → f (η ∘ₐ η′)
  acc {A ∧ B} η p = kacc {A} η (proj₁ p) , kacc {B} η (proj₂ p)
  acc {𝕋}     η t = tt
  acc {□ A}   η f = λ η′ → f (η ∘ₐ η′)

  kacc : ∀ {{𝔐 : 𝔎}} {A w w′} → w′ ≥ w → w ᵏ⊩ A
                              → w′ ᵏ⊩ A
  kacc η k = λ η′ f → k (η ∘ₐ η′) f

mkacc : ∀ {{𝔐 : 𝔎}} {A w w′} → w′ ≥ w → w ᵐᵏ⊩ A
                             → w′ ᵐᵏ⊩ A
mkacc {A} η (M , 𝒟 , k) = M , mren ᵐ⌊ η ⌋ₐ 𝒟 , kacc {A} η k

kacc⋆ : ∀ {{𝔐 : 𝔎}} {Ξ w w′} → w′ ≥ w → w ᵏ⊩⋆ Ξ
                             → w′ ᵏ⊩⋆ Ξ
-- TODO: Why does Agda require seemingly unused annotations here?
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


-- -- Soundness
-- ↓ : ∀ {Δ Γ M A} → Δ ⁏ Γ ⊢ M ∷ A
--                 → Δ ⁏ Γ ⊨ A
-- ↓ (ᵐᵛ x # i)             mρ rρ = klookupₑ (sem⋆ mρ) (proj∋₂ i)
-- ↓ (ʳᵛ x # i)             mρ rρ = klookupₑ rρ (proj∋₂ i)
-- ↓ (ƛ_∙_ {A} {B} x 𝒟)     mρ rρ = kƛ {A} {B} (λ η k →
--                                    ↓ 𝒟 (mkacc⋆ η mρ) (kacc⋆ η rρ , k))
-- ↓ (_$_ {A} {B} 𝒟 ℰ)      mρ rρ = k$ {A} {B} (↓ 𝒟 mρ rρ) (↓ ℰ mρ rρ)
-- ↓ (_,_ {A} {B} 𝒟 ℰ)      mρ rρ = k, {A} {B} (↓ 𝒟 mρ rρ) (↓ ℰ mρ rρ)
-- ↓ (π₁_ {A} {B} 𝒟)        mρ rρ = kπ₁ {A} {B} (↓ 𝒟 mρ rρ)
-- ↓ (π₂_ {A} {B} 𝒟)        mρ rρ = kπ₂ {A} {B} (↓ 𝒟 mρ rρ)
-- ↓ tt                     mρ rρ = ktt
-- ↓ {Δ} (⌜_⌝ {A} {M} 𝒟)    mρ rρ rewrite lem₄ Δ ⁻¹
--                                = k⌜⌝ {A} (λ η →
--                                    msubₜₘ {ξ = map proj₁ Δ} (syn⋆ (mkacc⋆ η mρ)) 𝒟
--                                  , msub {ξ = map proj₁ Δ} (syn⋆ (mkacc⋆ η mρ)) 𝒟
--                                  , ↓ 𝒟 (mkacc⋆ η mρ) ∅)
-- ↓ (⌞_⌟_∙_ {A} {C} 𝒟 x ℰ) mρ rρ = k⌞⌟ {A} {C} (↓ 𝒟 mρ rρ) (λ η M𝒟k →
--                                    ↓ ℰ (mkacc⋆ η mρ , M𝒟k) (kacc⋆ η rρ))


-- Soundness, inlined
↓ : ∀ {Δ Γ M A} → Δ ⁏ Γ ⊢ M ∷ A
                → Δ ⁏ Γ ⊨ A
↓ (ᵐᵛ x # i)             mρ rρ = klookupₑ (sem⋆ mρ) (proj∋₂ i)
↓ (ʳᵛ x # i)             mρ rρ = klookupₑ rρ (proj∋₂ i)
↓ (ƛ_∙_ {A} {B} x 𝒟)     mρ rρ = return {A ⊃ B} (λ η k →
                                   ↓ 𝒟 (mkacc⋆ η mρ) (kacc⋆ η rρ , k))
↓ (_$_ {A} {B} 𝒟 ℰ)      mρ rρ = bind {A ⊃ B} {B} (↓ 𝒟 mρ rρ) (λ η f →
                                   f idₐ (↓ ℰ (mkacc⋆ η mρ) (kacc⋆ η rρ)))
↓ (_,_ {A} {B} 𝒟 ℰ)      mρ rρ = return {A ∧ B} (↓ 𝒟 mρ rρ , ↓ ℰ mρ rρ)
↓ (π₁ {A} {B} 𝒟)         mρ rρ = bind {A ∧ B} {A} (↓ 𝒟 mρ rρ) (λ η p → proj₁ p)
↓ (π₂ {A} {B} 𝒟)         mρ rρ = bind {A ∧ B} {B} (↓ 𝒟 mρ rρ) (λ η p → proj₂ p)
↓ tt                     mρ rρ = return {𝕋} tt
↓ {Δ} (⌜_⌝ {A} {M} 𝒟)    mρ rρ rewrite lem₄ Δ ⁻¹
                               = return {□ A} (λ η →
                                   msubₜₘ {ξ = map proj₁ Δ} (syn⋆ (mkacc⋆ η mρ)) 𝒟
                                 , msub {ξ = map proj₁ Δ} (syn⋆ (mkacc⋆ η mρ)) 𝒟
                                 , ↓ 𝒟 (mkacc⋆ η mρ) ∅)
↓ (⌞_⌟_∙_ {A} {C} 𝒟 x ℰ) mρ rρ = bind {□ A} {C} (↓ 𝒟 mρ rρ) (λ η f →
                                   ↓ ℰ (mkacc⋆ η mρ , f idₐ) (kacc⋆ η rρ))
↓ (_⦂_ 𝒟 A {{refl}})     mρ rρ = bind {A} {A} (↓ 𝒟 mρ rρ) (λ η a →
                                   return {A} a)


--------------------------------------------------------------------------------
--
-- Completeness


-- Universal model
instance
  𝔐ᵤ : 𝔎
  𝔐ᵤ = record
         { 𝒲    = Cx
         ; 𝒱    = λ { (Δ ⁏ Γ) x → Σ Tm (λ M → Δ ⁏ Γ ⊢ₙₘ M ∷ ᵗᵛ x ) }
         ; _≥_  = _⊇²_
         ; idₐ  = idᵣ²
         ; _∘ₐ_ = _∘ᵣ²_
         ; accᵥ = λ { η (M , 𝒟) → M , renₙₘ η 𝒟 }
         ; ⌊_⌋  = id
         ; ⌊_⌋ₐ = id
         }


-- Soundness and completeness with respect to the universal model

-- TODO: Generate fresh names!
mutual
  ↑ᵤ : ∀ {A Δ Γ} → Δ ⁏ Γ ᵏ⊩ A
                 → Σ Tm (λ M → Δ ⁏ Γ ⊢ₙₘ M ∷ A)
  ↑ᵤ {ᵗᵛ x}  k = k idᵣ² (λ η M𝒟 → M𝒟)
  ↑ᵤ {A ⊃ B} k = k idᵣ² (λ η f → let M , 𝒟 = ↑ᵤ (f (rwkᵣ idᵣ²) (↓ᵤ (ʳᵛ "RFRESH" # zero))) in
                                  ƛ "RFRESH" ∙ M , ƛ "RFRESH" ∙ 𝒟)
  ↑ᵤ {A ∧ B} k = k idᵣ² (λ η p → let M , 𝒟 = ↑ᵤ (proj₁ p) in
                                  let N , ℰ = ↑ᵤ (proj₂ p) in
                                  (M , N) , (𝒟 , ℰ))
  ↑ᵤ {𝕋}     k = k idᵣ² (λ η t → tt , tt)
  ↑ᵤ {□ A}   k = k idᵣ² (λ η f → let M , 𝒟 = syn (f idᵣ²) in
                                  ⌜ M ⌝ , ⌜ 𝒟 ⌝)

  ↓ᵤ : ∀ {A M Δ Γ} → Δ ⁏ Γ ⊢ₙₜ M ∷ A
                   → Δ ⁏ Γ ᵏ⊩ A
  ↓ᵤ {ᵗᵛ x}  {M} 𝒟 = return {ᵗᵛ x} (M , ⁿᵗ 𝒟)
  ↓ᵤ {A ⊃ B} {M} 𝒟 = return {A ⊃ B} (λ η k → ↓ᵤ (renₙₜ η 𝒟 $ proj₂ (↑ᵤ k)))
  ↓ᵤ {A ∧ B} {M} 𝒟 = return {A ∧ B} (↓ᵤ (π₁ 𝒟) , ↓ᵤ (π₂ 𝒟))
  ↓ᵤ {𝕋 }    {M} 𝒟 = return {𝕋} tt
  ↓ᵤ {□ A}   {M} 𝒟 = λ η f →
                       let N , ℰ = f (mwkᵣ idᵣ²) (λ η′ →
                                     ᵐᵛ "MFRESH"
                                   , (ᵐᵛ "MFRESH" # mlookupᵣ η′ zero)
                                   , ↓ᵤ (ᵐᵛ "MFRESH" # mlookupᵣ η′ zero)) in
                       ⌞ M ⌟ "MFRESH" ∙ N , ⌞ renₙₜ η 𝒟 ⌟ "MFRESH" ∙ ℰ


mkidₑ : ∀ {Δ Γ} → Δ ⁏ Γ ᵐᵏ⊩⋆ map proj₂ Δ
mkidₑ {∅}           = ∅
mkidₑ {Δ , (x , A)} = mkacc⋆ (mwkᵣ idᵣ²) mkidₑ , (ᵐᵛ x , (ᵐᵛ x # zero) , ↓ᵤ (ᵐᵛ x # zero))

kidₑ : ∀ {Γ Δ} → Δ ⁏ Γ ᵏ⊩⋆ map proj₂ Γ
kidₑ {∅}           = ∅
kidₑ {Γ , (x , A)} = kacc⋆ (rwkᵣ idᵣ²) kidₑ , ↓ᵤ (ʳᵛ x # zero)


-- Completeness
↑ : ∀ {Δ Γ A} → Δ ⁏ Γ ⊨ A
              → Σ Tm (λ M → Δ ⁏ Γ ⊢ₙₘ M ∷ A)
↑ f = ↑ᵤ (f mkidₑ kidₑ)


-- Normalisation
nm : ∀ {Δ Γ M A} → Δ ⁏ Γ ⊢ M ∷ A
                 → Σ Tm (λ M′ → Δ ⁏ Γ ⊢ₙₘ M′ ∷ A)
nm = ↑ ∘ ↓


--------------------------------------------------------------------------------
--
-- Examples


ᵐᵛ0 : ∀ {A Δ Γ} → (x : MVar) → Δ , (x , A) ⁏ Γ ⊢ ᵐᵛ x ∷ A
ᵐᵛ0 x = ᵐᵛ x # zero

ᵐᵛ1 : ∀ {A yB Δ Γ} → (x : MVar) → Δ , (x , A) , yB ⁏ Γ ⊢ ᵐᵛ x ∷ A
ᵐᵛ1 x = ᵐᵛ x # suc zero

ᵐᵛ2 : ∀ {A yB zC Δ Γ} → (x : MVar) → Δ , (x , A) , yB , zC ⁏ Γ ⊢ ᵐᵛ x ∷ A
ᵐᵛ2 x = ᵐᵛ x # suc (suc zero)


ʳᵛ0 : ∀ {A Δ Γ} → (x : RVar) → Δ ⁏ Γ , (x , A) ⊢ ʳᵛ x ∷ A
ʳᵛ0 x = ʳᵛ x # zero

ʳᵛ1 : ∀ {A yB Δ Γ} → (x : RVar) → Δ ⁏ Γ , (x , A) , yB ⊢ ʳᵛ x ∷ A
ʳᵛ1 x = ʳᵛ x # suc zero

ʳᵛ2 : ∀ {A yB zC Δ Γ} → (x : RVar) → Δ ⁏ Γ , (x , A) , yB , zC ⊢ ʳᵛ x ∷ A
ʳᵛ2 x = ʳᵛ x # suc (suc zero)


axIₜₘ : Tm
axIₜₘ = ƛ "x" ∙ ʳᵛ "x"

axKₜₘ : Tm
axKₜₘ = ƛ "x" ∙ (ƛ "y" ∙ ʳᵛ "x")

axSₜₘ : Tm
axSₜₘ = ƛ "f" ∙ (ƛ "g" ∙ (ƛ "x" ∙
          ((ʳᵛ "f" $ ʳᵛ "x") $ (ʳᵛ "g" $ ʳᵛ "x"))))


axDₜₘ : Tm
axDₜₘ = ƛ "'f" ∙ (ƛ "'x" ∙
          (⌞ ʳᵛ "'f" ⌟ "f" ∙ (⌞ ʳᵛ "'x" ⌟ "x" ∙
            (⌜ ᵐᵛ "f" $ ᵐᵛ "x" ⌝))))

axTₜₘ : Tm
axTₜₘ = ƛ "'x" ∙ (⌞ ʳᵛ "'x" ⌟ "x" ∙ (ᵐᵛ "x"))

ax4ₜₘ : Tm
ax4ₜₘ = ƛ "'x" ∙ (⌞ ʳᵛ "'x" ⌟ "x" ∙ (⌜ ⌜ ᵐᵛ "x" ⌝ ⌝))


axI : ∀ {A Δ Γ}
    → Δ ⁏ Γ ⊢ axIₜₘ ∷ A ⊃ A
axI = ƛ "x" ∙ ʳᵛ0 "x"

axK : ∀ {A B Δ Γ}
    → Δ ⁏ Γ ⊢ axKₜₘ ∷ A ⊃ B ⊃ A
axK = ƛ "x" ∙ (ƛ "y" ∙ ʳᵛ1 "x")

axS : ∀ {A B C Δ Γ}
    → Δ ⁏ Γ ⊢ axSₜₘ ∷ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
axS = ƛ "f" ∙ (ƛ "g" ∙ (ƛ "x" ∙
        ((ʳᵛ2 "f" $ ʳᵛ0 "x" ) $ (ʳᵛ1 "g" $ ʳᵛ0 "x"))))


axD : ∀ {A B Δ Γ}
    → Δ ⁏ Γ ⊢ axDₜₘ ∷ □ (A ⊃ B) ⊃ □ A ⊃ □ B
axD = ƛ "'f" ∙ (ƛ "'x" ∙
        (⌞ ʳᵛ1 "'f" ⌟ "f" ∙ (⌞ ʳᵛ0 "'x" ⌟ "x" ∙
          (⌜ ᵐᵛ1 "f" $ ᵐᵛ0 "x" ⌝))))

axT : ∀ {A Δ Γ}
    → Δ ⁏ Γ ⊢ axTₜₘ ∷ □ A ⊃ A
axT = ƛ "'x" ∙ (⌞ ʳᵛ0 "'x" ⌟ "x" ∙ (ᵐᵛ0 "x"))

ax4 : ∀ {A Δ Γ}
    → Δ ⁏ Γ ⊢ ax4ₜₘ ∷ □ A ⊃ □ □ A
ax4 = ƛ "'x" ∙ (⌞ ʳᵛ0 "'x" ⌟ "x" ∙ (⌜ ⌜ ᵐᵛ0 "x" ⌝ ⌝))


--------------------------------------------------------------------------------
--
-- Conversion tests


test∼ : ∀ {Δ Γ M₁ M₂ A} → Δ ⁏ Γ ⊢ M₁ ∷ A → Δ ⁏ Γ ⊢ M₂ ∷ A → Set
test∼ {M₂ = M₂} 𝒟₁ 𝒟₂ with nm 𝒟₁
test∼ {M₂ = M₂} 𝒟₁ 𝒟₂ | M₁′ , 𝒟₁′ with M₁′ ≟ₜₘ M₂
test∼ {M₂ = M₂} 𝒟₁ 𝒟₂ | .M₂ , 𝒟₁′ | yes refl  = embₙₘ 𝒟₁′ ≡ 𝒟₂
test∼ {M₂ = M₂} 𝒟₁ 𝒟₂ | M₁′ , 𝒟₁′ | no M₁′≢M₂ = ⊥


-- red⊃ : ∀ {Δ Γ x A B} → (M : Δ ⁏ Γ , A ⊢ B) (N : Δ ⁏ Γ ⊢ A)
--                      → ƛ x ∙ M $ N ∼ rsub (ridₛ , (x , N)) M

test∼red⊃ : test∼ {∅} {∅ , ("a" , "A")}
                  ((ƛ "x" ∙ ʳᵛ0 "x") $ ʳᵛ0 "a")
                  (ʳᵛ0 "a")
test∼red⊃ = refl


-- red∧₁ : ∀ {Δ Γ A B} → (M : Δ ⁏ Γ ⊢ A) (N : Δ ⁏ Γ ⊢ B)
--                     → π₁ (M , N) ∼ M

test∼red∧₁ : test∼ {∅} {∅ , ("a" , "A") , ("b" , "B")}
                   (π₁ (ʳᵛ1 "a" , ʳᵛ0 "b"))
                   (ʳᵛ1 "a")
test∼red∧₁ = refl


-- red∧₂ : ∀ {Δ Γ A B} → (M : Δ ⁏ Γ ⊢ A) (N : Δ ⁏ Γ ⊢ B)
--                     → π₂ (M , N) ∼ N

test∼red∧₂ : test∼ {∅} {∅ , ("a" , "A") , ("b" , "B")}
                   (π₂ (ʳᵛ1 "a" , ʳᵛ0 "b"))
                   (ʳᵛ0 "b")
test∼red∧₂ = refl


-- red□ : ∀ {Δ Γ x A C} → (M : Δ ⁏ ∅ ⊢ A) (N : Δ , A ⁏ Γ ⊢ C)
--                      → ⌞ ⌜ M ⌝ ⌟ x ∙ N ∼ msub (midₛ , (x , M)) N

test∼red□ : test∼ {∅ , ("a" , "A")} {∅}
                  (⌞ ⌜ ᵐᵛ0 "a" ⌝ ⌟ "x" ∙ ᵐᵛ0 "x")
                  (ᵐᵛ0 "a")
test∼red□ = refl


-- exp⊃ : ∀ {Δ Γ x A B} → (M : Δ ⁏ Γ ⊢ A ⊃ B) {{_ : fresh x Γ}}
--                      → M ∼ ƛ x ∙ (rren (wkᵣ idᵣ) M $ ʳᵛ0 x)

-- TODO: Generate sensible variable names
test∼exp⊃ : test∼ {∅} {∅ , ("f" , "A" ⊃ "B")}
                  (ʳᵛ0 "f")
                  (ƛ "RFRESH" ∙ (rren (wkᵣ idᵣ) (ʳᵛ0 "f") $ ʳᵛ0 "RFRESH"))
test∼exp⊃ = refl


-- exp∧ : ∀ {Δ Γ A B} → (M : Δ ⁏ Γ ⊢ A ∧ B)
--                    → M ∼ π₁ M , π₂ M

test∼exp∧ : test∼ {∅} {∅ , ("p" , "A" ∧ "B")}
                  (ʳᵛ0 "p")
                  (π₁ (ʳᵛ0 "p") , π₂ (ʳᵛ0 "p"))
test∼exp∧ = refl


-- exp𝕋 : ∀ {Δ Γ} → (M : Δ ⁏ Γ ⊢ 𝕋)
--                → M ∼ tt

test∼exp𝕋 : test∼ {∅} {∅ , ("t" , 𝕋)}
                  (ʳᵛ0 "t")
                  tt
test∼exp𝕋 = refl


-- exp□ : ∀ {Δ Γ x A} → (M : Δ ⁏ Γ ⊢ □ A) {{_ : fresh x Δ}}
--                    → M ∼ ⌞ M ⌟ x ∙ ⌜ ᵐᵛ0 x ⌝

-- TODO: Generate sensible variable names
test∼exp□ : test∼ {∅} {∅ , ("'a" , □ "A")}
                  (ʳᵛ0 "'a")
                  (⌞ ʳᵛ0 "'a" ⌟ "MFRESH" ∙ ⌜ ᵐᵛ0 "MFRESH" ⌝)
test∼exp□ = refl


-- comm□$ : ∀ {Δ Γ x A B} → (Q : Δ ⁏ Γ ⊢ □ (A ⊃ B)) {{_ : fresh x Δ}}
--                           (M : Δ , (x , A ⊃ B) ⁏ Γ ⊢ A ⊃ B) (N : Δ ⁏ Γ ⊢ A)
--                        → (⌞ Q ⌟ x ∙ M) $ N ∼ ⌞ Q ⌟ x ∙ (M $ (mren (wkᵣ idᵣ) N))

-- TODO: Stop forgetting variable names
test∼comm□$ : test∼ {∅} {∅ , ("'f" , □ ("A" ⊃ "B")) , ("a" , "A")}
                    ((⌞ ʳᵛ1 "'f" ⌟ "x" ∙ ᵐᵛ0 "x") $ ʳᵛ0 "a")
                    (⌞ ʳᵛ1 "'f" ⌟ "MFRESH" ∙ (ᵐᵛ0 "MFRESH" $ mren (wkᵣ idᵣ) (ʳᵛ0 "a")))
test∼comm□$ = refl


-- comm□⌞⌟ : ∀ {Δ Γ x₁ x₂ A C} → (Q : Δ ⁏ Γ ⊢ □ □ A) {{_ : fresh x₁ Δ}} {{_ : fresh x₂ Δ}}
--                                (M : Δ , (x₁ , □ A) ⁏ Γ ⊢ □ A) (N : Δ , (x₂ , A) ⁏ Γ ⊢ C)
--                             → ⌞ (⌞ Q ⌟ x₁ ∙ M) ⌟ x₂ ∙ N ∼ ⌞ Q ⌟ x₁ ∙ (⌞ M ⌟ x₂ ∙ (mren (wkᵣ idᵣ) N))

-- TODO: Generate sensible variable names
test∼comm□⌞⌟ : test∼ {∅} {∅ , ("''a" , □ □ "A")}
                     (⌞ ⌞ ʳᵛ0 "''a" ⌟ "x₁" ∙ ᵐᵛ0 "x₁" ⌟ "x₂" ∙ ᵐᵛ0 "x₂")
                     (⌞ ʳᵛ0 "''a" ⌟ "MFRESH" ∙ ⌞ ᵐᵛ0 "MFRESH" ⌟ "MFRESH" ∙ ᵐᵛ0 "MFRESH")
test∼comm□⌞⌟ = refl


-- comm□π₁ : ∀ {Δ Γ x A B} → (Q : Δ ⁏ Γ ⊢ □ (A ∧ B)) {{_ : fresh x Δ}}
--                            (M : Δ , (x , A ∧ B) ⁏ Γ ⊢ A ∧ B)
--                         → π₁ (⌞ Q ⌟ x ∙ M) ∼ ⌞ Q ⌟ x ∙ (π₁ M)

-- TODO: Stop forgetting variable names
test∼comm□π₁ : test∼ {∅} {∅ , ("'x" , □ ("A" ∧ "B"))}
                     (π₁ (⌞ ʳᵛ0 "'x" ⌟ "x" ∙ ᵐᵛ0 "x"))
                     (⌞ ʳᵛ0 "'x" ⌟ "MFRESH" ∙ π₁ (ᵐᵛ0 "MFRESH"))
test∼comm□π₁ = refl


-- comm□π₂ : ∀ {Δ Γ x A B} → (Q : Δ ⁏ Γ ⊢ □ (A ∧ B)) {{_ : fresh x Δ}}
--                            (M : Δ , (x , A ∧ B) ⁏ Γ ⊢ A ∧ B)
--                         → π₂ (⌞ Q ⌟ x ∙ M) ∼ ⌞ Q ⌟ x ∙ (π₂ M)

-- TODO: Stop forgetting variable names
test∼comm□π₂ : test∼ {∅} {∅ , ("'x" , □ ("A" ∧ "B"))}
                     (π₂ (⌞ ʳᵛ0 "'x" ⌟ "x" ∙ ᵐᵛ0 "x"))
                     (⌞ ʳᵛ0 "'x" ⌟ "MFRESH" ∙ π₂ (ᵐᵛ0 "MFRESH"))
test∼comm□π₂ = refl


--------------------------------------------------------------------------------
--
-- Self-interpretation


-- weakBP : ∀ {Δ Γ A B} → (M : Δ ⁏ Γ ⊢ A)
--                      → 𝕋 $ ⌜ M ⌝ ∼ ⌜ M ⌝

test∼weakBP : test∼ {∅ , ("x" , "A")} {∅}
                    (axT $ ⌜ ᵐᵛ0 "x" ⌝)
                    (ᵐᵛ0 "x")
test∼weakBP = refl


-- Andrej : ∀ {Δ Γ A B} → (M : Δ ⁏ Γ ⊢ A ⊃ B) (N : Δ ⁏ Γ ⊢ A)
--                      → (𝔻 $ ⌜ M ⌝) $ ⌜ N ⌝ ∼ ⌜ M $ N ⌝

test∼Andrej : test∼ {∅ , ("f" , "A" ⊃ "B") , ("x" , "A")} {∅}
                    ((axD $ ⌜ ᵐᵛ1 "f" ⌝) $ ⌜ ᵐᵛ0 "x" ⌝)
                    (⌜ ᵐᵛ1 "f" $ ᵐᵛ0 "x" ⌝)
test∼Andrej = refl


--------------------------------------------------------------------------------
