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
  𝔗   : Tp
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
ᵗᵛ x₁ ≟ₜₚ 𝔗         = no (λ ())
ᵗᵛ x₁ ≟ₜₚ (□ A₂)    = no (λ ())

(A₁ ⊃ B₁) ≟ₜₚ ᵗᵛ x₂     = no (λ ())
(A₁ ⊃ B₁) ≟ₜₚ (A₂ ⊃ B₂) with A₁ ≟ₜₚ A₂ | B₁ ≟ₜₚ B₂
...                     | yes refl | yes refl = yes refl
...                     | yes refl | no B₁≢B₂ = no (B₁≢B₂ ∘ inj⊃₂)
...                     | no A₁≢A₂ | _        = no (A₁≢A₂ ∘ inj⊃₁)
(A₁ ⊃ B₁) ≟ₜₚ (A₂ ∧ B₂) = no (λ ())
(A₁ ⊃ B₁) ≟ₜₚ 𝔗         = no (λ ())
(A₁ ⊃ B₁) ≟ₜₚ (□ A₂)    = no (λ ())

(A₁ ∧ B₁) ≟ₜₚ ᵗᵛ x₂     = no (λ ())
(A₁ ∧ B₁) ≟ₜₚ (A₂ ⊃ B₂) = no (λ ())
(A₁ ∧ B₁) ≟ₜₚ (A₂ ∧ B₂) with A₁ ≟ₜₚ A₂ | B₁ ≟ₜₚ B₂
...                     | yes refl | yes refl = yes refl
...                     | yes refl | no B₁≢B₂ = no (B₁≢B₂ ∘ inj∧₂)
...                     | no A₁≢A₂ | _        = no (A₁≢A₂ ∘ inj∧₁)
(A₁ ∧ B₁) ≟ₜₚ 𝔗         = no (λ ())
(A₁ ∧ B₁) ≟ₜₚ (□ A₂)    = no (λ ())

𝔗 ≟ₜₚ ᵗᵛ x₂     = no (λ ())
𝔗 ≟ₜₚ (A₂ ⊃ B₂) = no (λ ())
𝔗 ≟ₜₚ (A₂ ∧ B₂) = no (λ ())
𝔗 ≟ₜₚ 𝔗         = yes refl
𝔗 ≟ₜₚ (□ A₂)    = no (λ ())

(□ A₁) ≟ₜₚ ᵗᵛ x₂     = no (λ ())
(□ A₁) ≟ₜₚ (A₂ ⊃ B₂) = no (λ ())
(□ A₁) ≟ₜₚ (A₂ ∧ B₂) = no (λ ())
(□ A₁) ≟ₜₚ 𝔗         = no (λ ())
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


-- Variables
data Var : Set where
  var : String → Var

{-# COMPILE GHC Var = data Var (Var) #-}

injvar : ∀ {s₁ s₂} → var s₁ ≡ var s₂ → s₁ ≡ s₂
injvar refl = refl

_≟ᵥ_ : (x₁ x₂ : Var) → Dec (x₁ ≡ x₂)
var s₁ ≟ᵥ var s₂ = mapDec (var &_) injvar (s₁ ≟ₛ s₂)

instance
  varIsString : IsString Var
  varIsString =
    record
      { Constraint = λ s → ⊤
      ; fromString = λ s → var s
      }


-- Terms
infixl 10 _⦂_
data Tm : Set where
  ᵐᵛ     : (x : MVar) → Tm
  ᵛ      : (x : Var) → Tm
  ƛ_∙_   : (x : Var) (M : Tm) → Tm
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

injᵛ : ∀ {x₁ x₂} → ᵛ x₁ ≡ ᵛ x₂ → x₁ ≡ x₂
injᵛ refl = refl

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
(ᵐᵛ x₁) ≟ₜₘ (ᵛ x₂)           = no (λ ())
(ᵐᵛ x₁) ≟ₜₘ (ƛ x₂ ∙ M₂)      = no (λ ())
(ᵐᵛ x₁) ≟ₜₘ (M₂ $ N₂)        = no (λ ())
(ᵐᵛ x₁) ≟ₜₘ (M₂ , ℕ₂)        = no (λ ())
(ᵐᵛ x₁) ≟ₜₘ (π₁ M₂)          = no (λ ())
(ᵐᵛ x₁) ≟ₜₘ (π₂ M₂)          = no (λ ())
(ᵐᵛ x₁) ≟ₜₘ tt               = no (λ ())
(ᵐᵛ x₁) ≟ₜₘ ⌜ M₂ ⌝           = no (λ ())
(ᵐᵛ x₁) ≟ₜₘ (⌞ M₂ ⌟ x₂ ∙ N₂) = no (λ ())
(ᵐᵛ x₁) ≟ₜₘ (M₂ ⦂ A₂)        = no (λ ())

(ᵛ x₁) ≟ₜₘ (ᵐᵛ x₂)          = no (λ ())
(ᵛ x₁) ≟ₜₘ (ᵛ x₂)           with x₁ ≟ᵥ x₂
...                         | yes refl = yes refl
...                         | no x₁≢x₂ = no (x₁≢x₂ ∘ injᵛ)
(ᵛ x₁) ≟ₜₘ (ƛ x₂ ∙ M₂)      = no (λ ())
(ᵛ x₁) ≟ₜₘ (M₂ $ N₂)        = no (λ ())
(ᵛ x₁) ≟ₜₘ (M₂ , N₂)        = no (λ ())
(ᵛ x₁) ≟ₜₘ (π₁ M₂)          = no (λ ())
(ᵛ x₁) ≟ₜₘ (π₂ M₂)          = no (λ ())
(ᵛ x₁) ≟ₜₘ tt               = no (λ ())
(ᵛ x₁) ≟ₜₘ ⌜ M₂ ⌝           = no (λ ())
(ᵛ x₁) ≟ₜₘ (⌞ M₂ ⌟ x₂ ∙ N₂) = no (λ ())
(ᵛ x₁) ≟ₜₘ (M₂ ⦂ A₂)        = no (λ ())

(ƛ x₁ ∙ M₁) ≟ₜₘ (ᵐᵛ x₂)          = no (λ ())
(ƛ x₁ ∙ M₁) ≟ₜₘ (ᵛ x₂)           = no (λ ())
(ƛ x₁ ∙ M₁) ≟ₜₘ (ƛ x₂ ∙ M₂)      with x₁ ≟ᵥ x₂ | M₁ ≟ₜₘ M₂
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
(M₁ $ N₁) ≟ₜₘ (ᵛ x₂)           = no (λ ())
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
(M₁ , N₁) ≟ₜₘ (ᵛ x₂)           = no (λ ())
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
(π₁ M₁) ≟ₜₘ (ᵛ x₂)           = no (λ ())
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
(π₂ M₁) ≟ₜₘ (ᵛ x₂)           = no (λ ())
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
tt ≟ₜₘ (ᵛ x₂)           = no (λ ())
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
⌜ M₁ ⌝ ≟ₜₘ (ᵛ x₂)           = no (λ ())
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
(⌞ M₁ ⌟ x₁ ∙ N₁) ≟ₜₘ (ᵛ x₂)           = no (λ ())
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
(M₁ ⦂ A₁) ≟ₜₘ (ᵛ x₂)           = no (λ ())
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
Cx = List (MVar × Tp) × List (Var × Tp)


-- Syntactic entailment
infix 3 _⊢_∷_
data _⊢_∷_ : Cx → Tm → Tp → Set
  where
    ᵐᵛ_#_  : ∀ {A Δ Γ} → (x : MVar) (i : Δ ∋ (x , A))
                       → Δ ⁏ Γ ⊢ ᵐᵛ x ∷ A

    ᵛ_#_   : ∀ {A Δ Γ} → (x : Var) (i : Γ ∋ (x , A))
                       → Δ ⁏ Γ ⊢ ᵛ x ∷ A

    ƛ_∙_   : ∀ {A B M Δ Γ} → (x : Var) (𝒟 : Δ ⁏ Γ , (x , A) ⊢ M ∷ B)
                           → Δ ⁏ Γ ⊢ ƛ x ∙ M ∷ A ⊃ B

    _$_    : ∀ {A B M N Δ Γ} → (𝒟 : Δ ⁏ Γ ⊢ M ∷ A ⊃ B) (ℰ : Δ ⁏ Γ ⊢ N ∷ A)
                             → Δ ⁏ Γ ⊢ M $ N ∷ B

    _,_    : ∀ {A B M N Δ Γ} → (𝒟 : Δ ⁏ Γ ⊢ M ∷ A) (ℰ : Δ ⁏ Γ ⊢ N ∷ B)
                             → Δ ⁏ Γ ⊢ M , N ∷ A ∧ B

    π₁     : ∀ {A B M Δ Γ} → (𝒟 : Δ ⁏ Γ ⊢ M ∷ A ∧ B)
                           → Δ ⁏ Γ ⊢ π₁ M ∷ A

    π₂     : ∀ {A B M Δ Γ} → (𝒟 : Δ ⁏ Γ ⊢ M ∷ A ∧ B)
                           → Δ ⁏ Γ ⊢ π₂ M ∷ B

    tt     : ∀ {Δ Γ} → Δ ⁏ Γ ⊢ tt ∷ 𝔗

    ⌜_⌝    : ∀ {A M Δ Γ} → (𝒟 : Δ ⁏ ∅ ⊢ M ∷ A)
                         → Δ ⁏ Γ ⊢ ⌜ M ⌝ ∷ □ A

    ⌞_⌟_∙_ : ∀ {A C M N Δ Γ} → (𝒟 : Δ ⁏ Γ ⊢ M ∷ □ A) (x : MVar) (ℰ : Δ , (x , A) ⁏ Γ ⊢ N ∷ C)
                             → Δ ⁏ Γ ⊢ ⌞ M ⌟ x ∙ N ∷ C


-- Normal and neutral forms
-- NOTE: Almost the same as bidirectional syntactic entailment
mutual
  infix 3 _⊢ₙₘ_∷_
  data _⊢ₙₘ_∷_ : Cx → Tm → Tp → Set
    where
      ƛ_∙_   : ∀ {A B M Δ Γ} → (x : Var) (𝒟 : Δ ⁏ Γ , (x , A) ⊢ₙₘ M ∷ B)
                             → Δ ⁏ Γ ⊢ₙₘ ƛ x ∙ M ∷ A ⊃ B

      _,_    : ∀ {A B M N Δ Γ} → (𝒟 : Δ ⁏ Γ ⊢ₙₘ M ∷ A) (ℰ : Δ ⁏ Γ ⊢ₙₘ N ∷ B)
                               → Δ ⁏ Γ ⊢ₙₘ M , N ∷ A ∧ B

      tt     : ∀ {Δ Γ} → Δ ⁏ Γ ⊢ₙₘ tt ∷ 𝔗

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

      ᵛ_#_  : ∀ {A Δ Γ} → (x : Var) (i : Γ ∋ (x , A))
                        → Δ ⁏ Γ ⊢ₙₜ ᵛ x ∷ A

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
  embₙₜ (ᵛ x # i)  = ᵛ x # i
  embₙₜ (𝒟 $ ℰ)    = embₙₜ 𝒟 $ embₙₘ ℰ
  embₙₜ (π₁ 𝒟)     = π₁ (embₙₜ 𝒟)
  embₙₜ (π₂ 𝒟)     = π₂ (embₙₜ 𝒟)


--------------------------------------------------------------------------------
--
-- Renaming


ᵐren : ∀ {Δ Δ′ Γ M A} → Δ′ ⊇ Δ → Δ ⁏ Γ ⊢ M ∷ A
                      → Δ′ ⁏ Γ ⊢ M ∷ A
ᵐren η (ᵐᵛ x # i)    = ᵐᵛ x # lookupᵣ η i
ᵐren η (ᵛ x # i)     = ᵛ x #  i
ᵐren η (ƛ x ∙ 𝒟)     = ƛ x ∙ ᵐren η 𝒟
ᵐren η (𝒟 $ ℰ)       = ᵐren η 𝒟 $ ᵐren η ℰ
ᵐren η (𝒟 , ℰ)       = ᵐren η 𝒟 , ᵐren η ℰ
ᵐren η (π₁ 𝒟)        = π₁ (ᵐren η 𝒟)
ᵐren η (π₂ 𝒟)        = π₂ (ᵐren η 𝒟)
ᵐren η tt            = tt
ᵐren η ⌜ 𝒟 ⌝         = ⌜ ᵐren η 𝒟 ⌝
ᵐren η (⌞ 𝒟 ⌟ x ∙ ℰ) = ⌞ ᵐren η 𝒟 ⌟ x ∙ ᵐren (lift η) ℰ

ren : ∀ {Δ Γ Γ′ M A} → Γ′ ⊇ Γ → Δ ⁏ Γ ⊢ M ∷ A
                     → Δ ⁏ Γ′ ⊢ M ∷ A
ren η (ᵐᵛ x # i)    = ᵐᵛ x # i
ren η (ᵛ x # i)     = ᵛ x # lookupᵣ η i
ren η (ƛ x ∙ 𝒟)     = ƛ x ∙ ren (lift η) 𝒟
ren η (𝒟 $ ℰ)       = ren η 𝒟 $ ren η ℰ
ren η (𝒟 , ℰ)       = ren η 𝒟 , ren η ℰ
ren η (π₁ 𝒟)        = π₁ (ren η 𝒟)
ren η (π₂ 𝒟)        = π₂ (ren η 𝒟)
ren η tt            = tt
ren η ⌜ 𝒟 ⌝         = ⌜ 𝒟 ⌝
ren η (⌞ 𝒟 ⌟ x ∙ ℰ) = ⌞ ren η 𝒟 ⌟ x ∙ ren η ℰ


mutual
  ᵐrenₙₘ : ∀ {Δ Δ′ Γ M A} → Δ′ ⊇ Δ → Δ ⁏ Γ ⊢ₙₘ M ∷ A
                          → Δ′ ⁏ Γ ⊢ₙₘ M ∷ A
  ᵐrenₙₘ η (ƛ x ∙ 𝒟)     = ƛ x ∙ ᵐrenₙₘ η 𝒟
  ᵐrenₙₘ η (𝒟 , ℰ)       = ᵐrenₙₘ η 𝒟 , ᵐrenₙₘ η ℰ
  ᵐrenₙₘ η tt            = tt
  ᵐrenₙₘ η ⌜ 𝒟 ⌝         = ⌜ ᵐren η 𝒟 ⌝
  ᵐrenₙₘ η (⌞ 𝒟 ⌟ x ∙ ℰ) = ⌞ ᵐrenₙₜ η 𝒟 ⌟ x ∙ ᵐrenₙₘ (lift η) ℰ
  ᵐrenₙₘ η (ⁿᵗ 𝒟)        = ⁿᵗ (ᵐrenₙₜ η 𝒟)

  ᵐrenₙₜ : ∀ {Δ Δ′ Γ M A} → Δ′ ⊇ Δ → Δ ⁏ Γ ⊢ₙₜ M ∷ A
                          → Δ′ ⁏ Γ ⊢ₙₜ M ∷ A
  ᵐrenₙₜ η (ᵐᵛ x # i) = ᵐᵛ x # lookupᵣ η i
  ᵐrenₙₜ η (ᵛ x # i)  = ᵛ x # i
  ᵐrenₙₜ η (𝒟 $ ℰ)    = ᵐrenₙₜ η 𝒟 $ ᵐrenₙₘ η ℰ
  ᵐrenₙₜ η (π₁ 𝒟)     = π₁ (ᵐrenₙₜ η 𝒟)
  ᵐrenₙₜ η (π₂ 𝒟)     = π₂ (ᵐrenₙₜ η 𝒟)


mutual
  renₙₘ : ∀ {Δ Γ Γ′ M A} → Γ′ ⊇ Γ → Δ ⁏ Γ ⊢ₙₘ M ∷ A
                         → Δ ⁏ Γ′ ⊢ₙₘ M ∷ A
  renₙₘ η (ƛ x ∙ 𝒟)     = ƛ x ∙ renₙₘ (lift η) 𝒟
  renₙₘ η (𝒟 , ℰ)       = renₙₘ η 𝒟 , renₙₘ η ℰ
  renₙₘ η tt            = tt
  renₙₘ η ⌜ 𝒟 ⌝         = ⌜ 𝒟 ⌝
  renₙₘ η (⌞ 𝒟 ⌟ x ∙ ℰ) = ⌞ renₙₜ η 𝒟 ⌟ x ∙ renₙₘ η ℰ
  renₙₘ η (ⁿᵗ 𝒟)        = ⁿᵗ (renₙₜ η 𝒟)

  renₙₜ : ∀ {Δ Γ Γ′ M A} → Γ′ ⊇ Γ → Δ ⁏ Γ ⊢ₙₜ M ∷ A
                         → Δ ⁏ Γ′ ⊢ₙₜ M ∷ A
  renₙₜ η (ᵐᵛ x # i) = ᵐᵛ x # i
  renₙₜ η (ᵛ x # i)  = ᵛ x # lookupᵣ η i
  renₙₜ η (𝒟 $ ℰ)    = renₙₜ η 𝒟 $ renₙₘ η ℰ
  renₙₜ η (π₁ 𝒟)     = π₁ (renₙₜ η 𝒟)
  renₙₜ η (π₂ 𝒟)     = π₂ (renₙₜ η 𝒟)


renₙₘ² : ∀ {Δ Δ′ Γ Γ′ M A} → Δ′ ⁏ Γ′ ⊇² Δ ⁏ Γ → Δ ⁏ Γ ⊢ₙₘ M ∷ A
                           → Δ′ ⁏ Γ′ ⊢ₙₘ M ∷ A
renₙₘ² η 𝒟 = (ᵐrenₙₘ (proj₁ η) ∘ renₙₘ (proj₂ η)) 𝒟

renₙₜ² : ∀ {Δ Δ′ Γ Γ′ M A} → Δ′ ⁏ Γ′ ⊇² Δ ⁏ Γ → Δ ⁏ Γ ⊢ₙₜ M ∷ A
                           → Δ′ ⁏ Γ′ ⊢ₙₜ M ∷ A
renₙₜ² η 𝒟 = (ᵐrenₙₜ (proj₁ η) ∘ renₙₜ (proj₂ η)) 𝒟


--------------------------------------------------------------------------------
--
-- Substitution


-- Simultaneous substitutions
infix 3 _⊢⋆_
_⊢⋆_ : Cx → List Tp → Set
Δ ⁏ Γ ⊢⋆ Ξ = All (λ A → Σ Tm (λ M → Δ ⁏ Γ ⊢ M ∷ A)) Ξ


ᵐren⋆ : ∀ {Δ Δ′ Γ Ξ} → Δ′ ⊇ Δ → Δ ⁏ Γ ⊢⋆ Ξ
                     → Δ′ ⁏ Γ ⊢⋆ Ξ
ᵐren⋆ η σ = mapₐ (mapΣ id (ᵐren η)) σ

ren⋆ : ∀ {Δ Γ Γ′ Ξ} → Γ′ ⊇ Γ → Δ ⁏ Γ ⊢⋆ Ξ
                    → Δ ⁏ Γ′ ⊢⋆ Ξ
ren⋆ η σ = mapₐ (mapΣ id (ren η)) σ


ᵐwkₛ : ∀ {x A Δ Γ Ξ} → Δ ⁏ Γ ⊢⋆ Ξ
                     → Δ , (x , A) ⁏ Γ ⊢⋆ Ξ
ᵐwkₛ σ = ᵐren⋆ (wk idᵣ) σ

wkₛ : ∀ {x A Δ Γ Ξ} → Δ ⁏ Γ ⊢⋆ Ξ
                    → Δ ⁏ Γ , (x , A) ⊢⋆ Ξ
wkₛ σ = ren⋆ (wk idᵣ) σ


ᵐliftₛ : ∀ {x A Δ Γ Ξ} → Δ ⁏ Γ ⊢⋆ Ξ
                       → Δ , (x , A) ⁏ Γ ⊢⋆ Ξ , A
ᵐliftₛ {x} σ = ᵐwkₛ σ , (ᵐᵛ x , (ᵐᵛ x # zero))

liftₛ : ∀ {x A Δ Γ Ξ} → Δ ⁏ Γ ⊢⋆ Ξ
                      → Δ ⁏ Γ , (x , A) ⊢⋆ Ξ , A
liftₛ {x} σ = wkₛ σ , (ᵛ x , (ᵛ x # zero))


ᵐidₛ : ∀ {Δ Γ} → Δ ⁏ Γ ⊢⋆ mapₗ proj₂ Δ
ᵐidₛ {∅}     = ∅
ᵐidₛ {Δ , A} = ᵐliftₛ ᵐidₛ

idₛ : ∀ {Γ Δ} → Δ ⁏ Γ ⊢⋆ mapₗ proj₂ Γ
idₛ {∅}     = ∅
idₛ {Γ , A} = liftₛ idₛ


lookupₛ : ∀ {Δ Γ Ξ A} → Δ ⁏ Γ ⊢⋆ Ξ → Ξ ∋ A
                      → Σ Tm (λ M → Δ ⁏ Γ ⊢ M ∷ A)
lookupₛ σ i = lookupₐ σ i


-- Substitution
ᵐsubₜₘ : ∀ {Δ Γ Ξ M A} → {ξ : List MVar} {{p : lenₗ ξ ≡ lenₗ Ξ}}
                       → Δ ⁏ ∅ ⊢⋆ Ξ → zipₗ ξ Ξ ⁏ Γ ⊢ M ∷ A
                       → Tm
ᵐsubₜₘ σ (ᵐᵛ x # i)          = proj₁ (lookupₛ σ (proj∋₂ i))
ᵐsubₜₘ σ (ᵛ x # i)           = ᵛ x
ᵐsubₜₘ σ (ƛ x ∙ 𝒟)           = ƛ x ∙ ᵐsubₜₘ σ 𝒟
ᵐsubₜₘ σ (𝒟 $ ℰ)             = ᵐsubₜₘ σ 𝒟 $ ᵐsubₜₘ σ ℰ
ᵐsubₜₘ σ (𝒟 , ℰ)             = ᵐsubₜₘ σ 𝒟 , ᵐsubₜₘ σ ℰ
ᵐsubₜₘ σ (π₁ 𝒟)              = π₁ (ᵐsubₜₘ σ 𝒟)
ᵐsubₜₘ σ (π₂ 𝒟)              = π₂ (ᵐsubₜₘ σ 𝒟)
ᵐsubₜₘ σ tt                  = tt
ᵐsubₜₘ σ ⌜ 𝒟 ⌝               = ⌜ ᵐsubₜₘ σ 𝒟 ⌝
ᵐsubₜₘ {{p}} σ (⌞ 𝒟 ⌟ x ∙ ℰ) = ⌞ ᵐsubₜₘ σ 𝒟 ⌟ x ∙ ᵐsubₜₘ {{foo p}} (ᵐliftₛ {x} σ) ℰ

ᵐsub : ∀ {Δ Γ Ξ M A} → {ξ : List MVar} {{p : lenₗ ξ ≡ lenₗ Ξ}}
                     → (σ : Δ ⁏ ∅ ⊢⋆ Ξ) (𝒟 : zipₗ ξ Ξ ⁏ Γ ⊢ M ∷ A)
                     → Δ ⁏ Γ ⊢ ᵐsubₜₘ σ 𝒟 ∷ A
ᵐsub σ (ᵐᵛ x # i)          = ren infᵣ (proj₂ (lookupₛ σ (proj∋₂ i)))
ᵐsub σ (ᵛ x # i)           = ᵛ x # i
ᵐsub σ (ƛ x ∙ 𝒟)           = ƛ x ∙ ᵐsub σ 𝒟
ᵐsub σ (𝒟 $ ℰ)             = ᵐsub σ 𝒟 $ ᵐsub σ ℰ
ᵐsub σ (𝒟 , ℰ)             = ᵐsub σ 𝒟 , ᵐsub σ ℰ
ᵐsub σ (π₁ 𝒟)              = π₁ (ᵐsub σ 𝒟)
ᵐsub σ (π₂ 𝒟)              = π₂ (ᵐsub σ 𝒟)
ᵐsub σ tt                  = tt
ᵐsub σ ⌜ 𝒟 ⌝               = ⌜ ᵐsub σ 𝒟 ⌝
ᵐsub {{p}} σ (⌞ 𝒟 ⌟ x ∙ ℰ) = ⌞ ᵐsub σ 𝒟 ⌟ x ∙ ᵐsub {{foo p}} (ᵐliftₛ σ) ℰ


subₜₘ : ∀ {Δ Γ Ξ M A} → {ξ : List Var} {{p : lenₗ ξ ≡ lenₗ Ξ}}
                      → Δ ⁏ Γ ⊢⋆ Ξ → Δ ⁏ zipₗ ξ Ξ ⊢ M ∷ A
                      → Tm
subₜₘ σ (ᵐᵛ x # i)      = ᵐᵛ x
subₜₘ σ (ᵛ x # i)       = proj₁ (lookupₛ σ (proj∋₂ i))
subₜₘ {{p}} σ (ƛ x ∙ 𝒟) = ƛ x ∙ subₜₘ {{foo p}} (liftₛ {x} σ) 𝒟
subₜₘ σ (𝒟 $ ℰ)         = subₜₘ σ 𝒟 $ subₜₘ σ ℰ
subₜₘ σ (𝒟 , ℰ)         = subₜₘ σ 𝒟 , subₜₘ σ ℰ
subₜₘ σ (π₁ 𝒟)          = π₁ (subₜₘ σ 𝒟)
subₜₘ σ (π₂ 𝒟)          = π₂ (subₜₘ σ 𝒟)
subₜₘ σ tt              = tt
subₜₘ σ ⌜ 𝒟 ⌝           = ⌜ subₜₘ {Γ = ∅} ∅ 𝒟 ⌝
subₜₘ σ (⌞ 𝒟 ⌟ x ∙ ℰ)   = ⌞ subₜₘ σ 𝒟 ⌟ x ∙ subₜₘ (ᵐwkₛ {x} σ) ℰ

sub : ∀ {Δ Γ Ξ M A} → {ξ : List Var} {{p : lenₗ ξ ≡ lenₗ Ξ}}
                    → (σ : Δ ⁏ Γ ⊢⋆ Ξ) (𝒟 : Δ ⁏ zipₗ ξ Ξ ⊢ M ∷ A)
                    → Δ ⁏ Γ ⊢ subₜₘ σ 𝒟 ∷ A
sub σ (ᵐᵛ x # i)      = ᵐᵛ x # i
sub σ (ᵛ x # i)       = proj₂ (lookupₛ σ (proj∋₂ i))
sub {{p}} σ (ƛ x ∙ 𝒟) = ƛ x ∙ sub {{foo p}} (liftₛ {x} σ) 𝒟
sub σ (𝒟 $ ℰ)         = sub σ 𝒟 $ sub σ ℰ
sub σ (𝒟 , ℰ)         = sub σ 𝒟 , sub σ ℰ
sub σ (π₁ 𝒟)          = π₁ (sub σ 𝒟)
sub σ (π₂ 𝒟)          = π₂ (sub σ 𝒟)
sub σ tt              = tt
sub σ ⌜ 𝒟 ⌝           = ⌜ sub {Γ = ∅} ∅ 𝒟 ⌝
sub σ (⌞ 𝒟 ⌟ x ∙ ℰ)   = ⌞ sub σ 𝒟 ⌟ x ∙ sub (ᵐwkₛ {x} σ) ℰ


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

    movᵥ : ∀ {x w w′} → w′ ≥ w → w 𝒱 x
                      → w′ 𝒱 x

    ⌊_⌋  : 𝒲 → Cx

    ⌊_⌋ₐ : ∀ {w w′} → w′ ≥ w
                    → ⌊ w′ ⌋ ⊇² ⌊ w ⌋

open 𝔎 {{…}} public


ᵐ⌊_⌋ : ∀ {{𝔐 : 𝔎}} → 𝒲 → List (MVar × Tp)
ᵐ⌊ w ⌋ = proj₁ ⌊ w ⌋

ᵐ⌊_⌋ₐ : ∀ {{𝔐 : 𝔎}} {w w′} → w′ ≥ w
                           → ᵐ⌊ w′ ⌋ ⊇ ᵐ⌊ w ⌋
ᵐ⌊ η ⌋ₐ = proj₁ ⌊ η ⌋ₐ


-- Values
mutual
  infix 3 _⊩_
  _⊩_ : ∀ {{𝔐 : 𝔎}} → 𝒲 → Tp → Set

  w ⊩ ᵗᵛ x  = w 𝒱 x

  w ⊩ A ⊃ B = ∀ {w′} → (η : w′ ≥ w) (k : w′ ᵏ⊩ A)
                      → w′ ᵏ⊩ B

  w ⊩ A ∧ B = w ᵏ⊩ A × w ᵏ⊩ B

  w ⊩ 𝔗     = ⊤

  w ⊩ □ A   = w ᵐᵏ⊩ A

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
syn p = proj₁ p

sem : ∀ {{𝔐 : 𝔎}} {w A} → w ᵐᵏ⊩ A
                        → w ᵏ⊩ A
sem p = proj₂ p


-- Environments
infix 3 _ᵏ⊩⋆_
_ᵏ⊩⋆_ : ∀ {{𝔐 : 𝔎}} → 𝒲 → List Tp → Set
w ᵏ⊩⋆ Ξ = All (w ᵏ⊩_) Ξ

infix 3 _ᵐᵏ⊩⋆_
_ᵐᵏ⊩⋆_ : ∀ {{𝔐 : 𝔎}} → 𝒲 → List Tp → Set
w ᵐᵏ⊩⋆ Ξ = All (w ᵐᵏ⊩_) Ξ


syn⋆ : ∀ {{𝔐 : 𝔎}} {w Ξ} → w ᵐᵏ⊩⋆ Ξ
                         → ᵐ⌊ w ⌋ ⁏ ∅ ⊢⋆ Ξ
syn⋆ δ = mapₐ syn δ

sem⋆ : ∀ {{𝔐 : 𝔎}} {w Ξ} → w ᵐᵏ⊩⋆ Ξ
                         → w ᵏ⊩⋆ Ξ
sem⋆ δ = mapₐ sem δ


-- Semantic entailment
infix 3 _⊨_
_⊨_ : Cx → Tp → Set₁
Δ ⁏ Γ ⊨ A = ∀ {{𝔐 : 𝔎}} {w} → w ᵐᵏ⊩⋆ mapₗ proj₂ Δ → w ᵏ⊩⋆ mapₗ proj₂ Γ
                             → w ᵏ⊩ A


-- Accessibility
mutual
  mov : ∀ {{𝔐 : 𝔎}} {A w w′} → w′ ≥ w → w ⊩ A
                             → w′ ⊩ A
  mov {ᵗᵛ x}  η v = movᵥ η v
  mov {A ⊃ B} η f = λ η′ → f (η ∘ₐ η′)
  mov {A ∧ B} η p = ᵏmov {A} η (proj₁ p) , ᵏmov {B} η (proj₂ p)
  mov {𝔗}     η t = tt
  mov {□ A}   η p = ᵐᵏmov η p

  ᵏmov : ∀ {{𝔐 : 𝔎}} {A w w′} → w′ ≥ w → w ᵏ⊩ A
                              → w′ ᵏ⊩ A
  ᵏmov η k = λ η′ f → k (η ∘ₐ η′) f

  ᵐᵏmov : ∀ {{𝔐 : 𝔎}} {A w w′} → w′ ≥ w → w ᵐᵏ⊩ A
                               → w′ ᵐᵏ⊩ A
  ᵐᵏmov {A} η p = proj₁ (syn p) , ᵐren ᵐ⌊ η ⌋ₐ (proj₂ (syn p)) , ᵏmov {A} η (sem p)

ᵏmov⋆ : ∀ {{𝔐 : 𝔎}} {Ξ w w′} → w′ ≥ w → w ᵏ⊩⋆ Ξ → w′ ᵏ⊩⋆ Ξ
-- TODO: Why does Agda require seemingly unused annotations here?
-- ᵏmov⋆ η γ = mapₐ (ᵏmov η) γ
ᵏmov⋆ η γ = mapₐ (λ {A} k {w″} {C} → ᵏmov {A} η (λ {w‴} {C′} → k {w‴} {C′})) γ

ᵐᵏmov⋆ : ∀ {{𝔐 : 𝔎}} {Ξ w w′} → w′ ≥ w → w ᵐᵏ⊩⋆ Ξ
                              → w′ ᵐᵏ⊩⋆ Ξ
ᵐᵏmov⋆ η δ = mapₐ (ᵐᵏmov η) δ


-- Kripke continuation monad
unit : ∀ {{𝔐 : 𝔎}} {A w} → w ⊩ A
                         → w ᵏ⊩ A
unit {A} a = λ η f →
               f idₐ (mov {A} η a)

bind : ∀ {{𝔐 : 𝔎}} {A C w} → w ᵏ⊩ A → (∀ {w′} → w′ ≥ w → w′ ⊩ A
                                                 → w′ ᵏ⊩ C)
                           → w ᵏ⊩ C
bind k f = λ η f′ →
             k η (λ η′ a →
               f (η ∘ₐ η′) a idₐ (λ η″ b →
                 f′ (η′ ∘ₐ η″) b))


lookup : ∀ {{𝔐 : 𝔎}} {Ξ A w} → w ᵏ⊩⋆ Ξ → Ξ ∋ A
                             → w ᵏ⊩ A
lookup γ i = lookupₐ γ i


-- Soundness
↓ : ∀ {Δ Γ M A} → Δ ⁏ Γ ⊢ M ∷ A
                → Δ ⁏ Γ ⊨ A
↓ (ᵐᵛ x # i)             = λ δ γ → lookup (sem⋆ δ) (proj∋₂ i)
↓ (ᵛ x # i)              = λ δ γ → lookup γ (proj∋₂ i)
↓ (ƛ_∙_ {A} {B} x 𝒟)     = λ δ γ → unit {A ⊃ B} (λ η k →
                             ↓ 𝒟 (ᵐᵏmov⋆ η δ) (ᵏmov⋆ η γ , k))
↓ (_$_ {A} {B} 𝒟 ℰ)      = λ δ γ → bind {A ⊃ B} {B} (↓ 𝒟 δ γ) (λ η f →
                             f idₐ (↓ ℰ (ᵐᵏmov⋆ η δ) (ᵏmov⋆ η γ)))
↓ (_,_ {A} {B} 𝒟 ℰ)      = λ δ γ → unit {A ∧ B} (↓ 𝒟 δ γ , ↓ ℰ δ γ)
↓ (π₁ {A} {B} 𝒟)         = λ δ γ → bind {A ∧ B} {A} (↓ 𝒟 δ γ) (λ η p → proj₁ p)
↓ (π₂ {A} {B} 𝒟)         = λ δ γ → bind {A ∧ B} {B} (↓ 𝒟 δ γ) (λ η p → proj₂ p)
↓ tt                     = λ δ γ → unit {𝔗} tt
↓ {Δ} (⌜_⌝ {A} {M} 𝒟)    rewrite lem₄ Δ ⁻¹
                         = λ δ γ → unit {□ A} ( ᵐsubₜₘ {ξ = mapₗ proj₁ Δ} (syn⋆ δ) 𝒟
                                               , ᵐsub {ξ = mapₗ proj₁ Δ} (syn⋆ δ) 𝒟
                                               , ↓ 𝒟 δ ∅
                                               )
↓ (⌞_⌟_∙_ {A} {C} 𝒟 x ℰ) = λ δ γ → bind {□ A} {C} (↓ 𝒟 δ γ) (λ η p →
                             ↓ ℰ (ᵐᵏmov⋆ η δ , p) (ᵏmov⋆ η γ))


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
         ; movᵥ = λ { η (M , 𝒟) → M , renₙₘ² η 𝒟 }
         ; ⌊_⌋  = id
         ; ⌊_⌋ₐ = id
         }
    where
      infix 3 _𝒱ᵤ_
      _𝒱ᵤ_ : Cx → TVar → Set
      Δ ⁏ Γ 𝒱ᵤ x = Σ Tm (λ M → Δ ⁏ Γ ⊢ₙₘ M ∷ ᵗᵛ x )


-- Soundness and completeness with respect to the universal model

-- TODO: Generate fresh names!
mutual
  ↓ᵤ : ∀ {A M Δ Γ} → Δ ⁏ Γ ⊢ₙₜ M ∷ A
                   → Δ ⁏ Γ ᵏ⊩ A
  ↓ᵤ {ᵗᵛ x}  {M} 𝒟 = unit {ᵗᵛ x} (M , ⁿᵗ 𝒟)
  ↓ᵤ {A ⊃ B} {M} 𝒟 = unit {A ⊃ B} (λ η k → ↓ᵤ (renₙₜ² η 𝒟 $ proj₂ (↑ᵤ k)))
  ↓ᵤ {A ∧ B} {M} 𝒟 = unit {A ∧ B} (↓ᵤ (π₁ 𝒟) , ↓ᵤ (π₂ 𝒟))
  ↓ᵤ {𝔗 }    {M} 𝒟 = unit {𝔗} tt
  ↓ᵤ {□ A}   {M} 𝒟 = λ η f →
                       let N , ℰ = f (ᵐwk² idᵣ²) ( ᵐᵛ "MFRESH"
                                                 , (ᵐᵛ "MFRESH" # zero)
                                                 , ↓ᵤ (ᵐᵛ "MFRESH" # zero)
                                                 ) in
                       ⌞ M ⌟ "MFRESH" ∙ N , ⌞ renₙₜ² η 𝒟 ⌟ "MFRESH" ∙ ℰ

  ↑ᵤ : ∀ {A Δ Γ} → Δ ⁏ Γ ᵏ⊩ A
                 → Σ Tm (λ M → Δ ⁏ Γ ⊢ₙₘ M ∷ A)
  ↑ᵤ {ᵗᵛ x}  k = k idᵣ² (λ η v → v)
  ↑ᵤ {A ⊃ B} k = k idᵣ² (λ η f → let M , 𝒟 = ↑ᵤ (f (wk² idᵣ²) (↓ᵤ (ᵛ "RFRESH" # zero))) in
                                  ƛ "RFRESH" ∙ M , ƛ "RFRESH" ∙ 𝒟)
  ↑ᵤ {A ∧ B} k = k idᵣ² (λ η p → let M , 𝒟 = ↑ᵤ (proj₁ p) in
                                  let N , ℰ = ↑ᵤ (proj₂ p) in
                                  (M , N) , (𝒟 , ℰ))
  ↑ᵤ {𝔗}     k = k idᵣ² (λ η t → tt , tt)
  ↑ᵤ {□ A}   k = k idᵣ² (λ η p → let M , 𝒟 = syn p in
                                  ⌜ M ⌝ , ⌜ 𝒟 ⌝)


ᵐidₑ : ∀ {Δ Γ} → Δ ⁏ Γ ᵐᵏ⊩⋆ mapₗ proj₂ Δ
ᵐidₑ {∅}           = ∅
ᵐidₑ {Δ , (x , A)} = ᵐᵏmov⋆ (ᵐwk² idᵣ²) ᵐidₑ , (ᵐᵛ x , (ᵐᵛ x # zero) , ↓ᵤ (ᵐᵛ x # zero))

idₑ : ∀ {Γ Δ} → Δ ⁏ Γ ᵏ⊩⋆ mapₗ proj₂ Γ
idₑ {∅}           = ∅
idₑ {Γ , (x , A)} = ᵏmov⋆ (wk² idᵣ²) idₑ , ↓ᵤ (ᵛ x # zero)


-- Completeness
↑ : ∀ {Δ Γ A} → Δ ⁏ Γ ⊨ A
              → Σ Tm (λ M → Δ ⁏ Γ ⊢ₙₘ M ∷ A)
↑ f = ↑ᵤ (f ᵐidₑ idₑ)


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


ᵛ0 : ∀ {A Δ Γ} → (x : Var) → Δ ⁏ Γ , (x , A) ⊢ ᵛ x ∷ A
ᵛ0 x = ᵛ x # zero

ᵛ1 : ∀ {A yB Δ Γ} → (x : Var) → Δ ⁏ Γ , (x , A) , yB ⊢ ᵛ x ∷ A
ᵛ1 x = ᵛ x # suc zero

ᵛ2 : ∀ {A yB zC Δ Γ} → (x : Var) → Δ ⁏ Γ , (x , A) , yB , zC ⊢ ᵛ x ∷ A
ᵛ2 x = ᵛ x # suc (suc zero)


ᵃˣIₜₘ : Tm
ᵃˣIₜₘ = ƛ "x" ∙ ᵛ "x"

ᵃˣKₜₘ : Tm
ᵃˣKₜₘ = ƛ "x" ∙ (ƛ "y" ∙ ᵛ "x")

ᵃˣSₜₘ : Tm
ᵃˣSₜₘ = ƛ "f" ∙ (ƛ "g" ∙ (ƛ "x" ∙
          ((ᵛ "f" $ ᵛ "x") $ (ᵛ "g" $ ᵛ "x"))))


ᵃˣDₜₘ : Tm
ᵃˣDₜₘ = ƛ "'f" ∙ (ƛ "'x" ∙
          (⌞ ᵛ "'f" ⌟ "f" ∙ (⌞ ᵛ "'x" ⌟ "x" ∙
            (⌜ ᵐᵛ "f" $ ᵐᵛ "x" ⌝))))

ᵃˣTₜₘ : Tm
ᵃˣTₜₘ = ƛ "'x" ∙ (⌞ ᵛ "'x" ⌟ "x" ∙ (ᵐᵛ "x"))

ᵃˣ4ₜₘ : Tm
ᵃˣ4ₜₘ = ƛ "'x" ∙ (⌞ ᵛ "'x" ⌟ "x" ∙ (⌜ ⌜ ᵐᵛ "x" ⌝ ⌝))


ᵃˣI : ∀ {A Δ Γ}
    → Δ ⁏ Γ ⊢ ᵃˣIₜₘ ∷ A ⊃ A
ᵃˣI = ƛ "x" ∙ ᵛ0 "x"

ᵃˣK : ∀ {A B Δ Γ}
    → Δ ⁏ Γ ⊢ ᵃˣKₜₘ ∷ A ⊃ B ⊃ A
ᵃˣK = ƛ "x" ∙ (ƛ "y" ∙ ᵛ1 "x")

ᵃˣS : ∀ {A B C Δ Γ}
    → Δ ⁏ Γ ⊢ ᵃˣSₜₘ ∷ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
ᵃˣS = ƛ "f" ∙ (ƛ "g" ∙ (ƛ "x" ∙
        ((ᵛ2 "f" $ ᵛ0 "x" ) $ (ᵛ1 "g" $ ᵛ0 "x"))))


ᵃˣD : ∀ {A B Δ Γ}
    → Δ ⁏ Γ ⊢ ᵃˣDₜₘ ∷ □ (A ⊃ B) ⊃ □ A ⊃ □ B
ᵃˣD = ƛ "'f" ∙ (ƛ "'x" ∙
        (⌞ ᵛ1 "'f" ⌟ "f" ∙ (⌞ ᵛ0 "'x" ⌟ "x" ∙
          (⌜ ᵐᵛ1 "f" $ ᵐᵛ0 "x" ⌝))))

ᵃˣT : ∀ {A Δ Γ}
    → Δ ⁏ Γ ⊢ ᵃˣTₜₘ ∷ □ A ⊃ A
ᵃˣT = ƛ "'x" ∙ (⌞ ᵛ0 "'x" ⌟ "x" ∙ (ᵐᵛ0 "x"))

ᵃˣ4 : ∀ {A Δ Γ}
    → Δ ⁏ Γ ⊢ ᵃˣ4ₜₘ ∷ □ A ⊃ □ □ A
ᵃˣ4 = ƛ "'x" ∙ (⌞ ᵛ0 "'x" ⌟ "x" ∙ (⌜ ⌜ ᵐᵛ0 "x" ⌝ ⌝))


--------------------------------------------------------------------------------
--
-- Conversion tests


test∼ : ∀ {Δ Γ M₁ M₂ A} → Δ ⁏ Γ ⊢ M₁ ∷ A → Δ ⁏ Γ ⊢ M₂ ∷ A → Set
test∼ {M₂ = M₂} 𝒟₁ 𝒟₂ with nm 𝒟₁
test∼ {M₂ = M₂} 𝒟₁ 𝒟₂ | M₁′ , 𝒟₁′ with M₁′ ≟ₜₘ M₂
test∼ {M₂ = M₂} 𝒟₁ 𝒟₂ | .M₂ , 𝒟₁′ | yes refl  = embₙₘ 𝒟₁′ ≡ 𝒟₂
test∼ {M₂ = M₂} 𝒟₁ 𝒟₂ | M₁′ , 𝒟₁′ | no M₁′≢M₂ = ⊥


-- red⊃ : ∀ {Δ Γ x A B} → (𝒟 : Δ ⁏ Γ , A ⊢ B) (ℰ : Δ ⁏ Γ ⊢ A)
--                      → ƛ x ∙ 𝒟 $ ℰ ∼ sub (idₛ , (x , ℰ)) 𝒟

test∼red⊃ : test∼ {∅} {∅ , ("a" , "A")}
                  ((ƛ "x" ∙ ᵛ0 "x") $ ᵛ0 "a")
                  (ᵛ0 "a")
test∼red⊃ = refl


-- red∧₁ : ∀ {Δ Γ A B} → (𝒟 : Δ ⁏ Γ ⊢ A) (ℰ : Δ ⁏ Γ ⊢ B)
--                     → π₁ (𝒟 , ℰ) ∼ 𝒟

test∼red∧₁ : test∼ {∅} {∅ , ("a" , "A") , ("b" , "B")}
                   (π₁ (ᵛ1 "a" , ᵛ0 "b"))
                   (ᵛ1 "a")
test∼red∧₁ = refl


-- red∧₂ : ∀ {Δ Γ A B} → (𝒟 : Δ ⁏ Γ ⊢ A) (ℰ : Δ ⁏ Γ ⊢ B)
--                     → π₂ (𝒟 , ℰ) ∼ ℰ

test∼red∧₂ : test∼ {∅} {∅ , ("a" , "A") , ("b" , "B")}
                   (π₂ (ᵛ1 "a" , ᵛ0 "b"))
                   (ᵛ0 "b")
test∼red∧₂ = refl


-- red□ : ∀ {Δ Γ x A C} → (𝒟 : Δ ⁏ ∅ ⊢ A) (ℰ : Δ , A ⁏ Γ ⊢ C)
--                      → ⌞ ⌜ 𝒟 ⌝ ⌟ x ∙ ℰ ∼ ᵐsub (ᵐidₛ , (x , 𝒟)) ℰ

test∼red□ : test∼ {∅ , ("a" , "A")} {∅}
                  (⌞ ⌜ ᵐᵛ0 "a" ⌝ ⌟ "x" ∙ ᵐᵛ0 "x")
                  (ᵐᵛ0 "a")
test∼red□ = refl


-- exp⊃ : ∀ {Δ Γ x A B} → (𝒟 : Δ ⁏ Γ ⊢ A ⊃ B) {{_ : fresh x Γ}}
--                      → 𝒟 ∼ ƛ x ∙ (ren (wk idᵣ) 𝒟 $ ᵛ0 x)

-- TODO: Generate sensible variable names
test∼exp⊃ : test∼ {∅} {∅ , ("f" , "A" ⊃ "B")}
                  (ᵛ0 "f")
                  (ƛ "RFRESH" ∙ (ren (wk idᵣ) (ᵛ0 "f") $ ᵛ0 "RFRESH"))
test∼exp⊃ = refl


-- exp∧ : ∀ {Δ Γ A B} → (𝒟 : Δ ⁏ Γ ⊢ A ∧ B)
--                    → 𝒟 ∼ π₁ 𝒟 , π₂ 𝒟

test∼exp∧ : test∼ {∅} {∅ , ("p" , "A" ∧ "B")}
                  (ᵛ0 "p")
                  (π₁ (ᵛ0 "p") , π₂ (ᵛ0 "p"))
test∼exp∧ = refl


-- exp𝔗 : ∀ {Δ Γ} → (𝒟 : Δ ⁏ Γ ⊢ 𝔗)
--                → 𝒟 ∼ tt

test∼exp𝔗 : test∼ {∅} {∅ , ("t" , 𝔗)}
                  (ᵛ0 "t")
                  tt
test∼exp𝔗 = refl


-- exp□ : ∀ {Δ Γ x A} → (𝒟 : Δ ⁏ Γ ⊢ □ A) {{_ : fresh x Δ}}
--                    → 𝒟 ∼ ⌞ 𝒟 ⌟ x ∙ ⌜ ᵐᵛ0 x ⌝

-- TODO: Generate sensible variable names
test∼exp□ : test∼ {∅} {∅ , ("'a" , □ "A")}
                  (ᵛ0 "'a")
                  (⌞ ᵛ0 "'a" ⌟ "MFRESH" ∙ ⌜ ᵐᵛ0 "MFRESH" ⌝)
test∼exp□ = refl


-- comm□$ : ∀ {Δ Γ x A B} → (𝒬 : Δ ⁏ Γ ⊢ □ (A ⊃ B)) {{_ : fresh x Δ}}
--                           (𝒟 : Δ , (x , A ⊃ B) ⁏ Γ ⊢ A ⊃ B) (ℰ : Δ ⁏ Γ ⊢ A)
--                        → (⌞ 𝒬 ⌟ x ∙ 𝒟) $ ℰ ∼ ⌞ 𝒬 ⌟ x ∙ (𝒟 $ (ᵐren (wk idᵣ) ℰ))

-- TODO: Stop forgetting variable names
test∼comm□$ : test∼ {∅} {∅ , ("'f" , □ ("A" ⊃ "B")) , ("a" , "A")}
                    ((⌞ ᵛ1 "'f" ⌟ "x" ∙ ᵐᵛ0 "x") $ ᵛ0 "a")
                    (⌞ ᵛ1 "'f" ⌟ "MFRESH" ∙ (ᵐᵛ0 "MFRESH" $ ᵐren (wk idᵣ) (ᵛ0 "a")))
test∼comm□$ = refl


-- comm□⌞⌟ : ∀ {Δ Γ x₁ x₂ A C} → (𝒬 : Δ ⁏ Γ ⊢ □ □ A) {{_ : fresh x₁ Δ}} {{_ : fresh x₂ Δ}}
--                                (𝒟 : Δ , (x₁ , □ A) ⁏ Γ ⊢ □ A) (ℰ : Δ , (x₂ , A) ⁏ Γ ⊢ C)
--                             → ⌞ (⌞ 𝒬 ⌟ x₁ ∙ 𝒟) ⌟ x₂ ∙ ℰ ∼ ⌞ 𝒬 ⌟ x₁ ∙ (⌞ 𝒟 ⌟ x₂ ∙ (ᵐren (wk idᵣ) ℰ))

-- TODO: Generate sensible variable names
test∼comm□⌞⌟ : test∼ {∅} {∅ , ("''a" , □ □ "A")}
                     (⌞ ⌞ ᵛ0 "''a" ⌟ "x₁" ∙ ᵐᵛ0 "x₁" ⌟ "x₂" ∙ ᵐᵛ0 "x₂")
                     (⌞ ᵛ0 "''a" ⌟ "MFRESH" ∙ ⌞ ᵐᵛ0 "MFRESH" ⌟ "MFRESH" ∙ ᵐᵛ0 "MFRESH")
test∼comm□⌞⌟ = refl


-- comm□π₁ : ∀ {Δ Γ x A B} → (𝒬 : Δ ⁏ Γ ⊢ □ (A ∧ B)) {{_ : fresh x Δ}}
--                            (𝒟 : Δ , (x , A ∧ B) ⁏ Γ ⊢ A ∧ B)
--                         → π₁ (⌞ 𝒬 ⌟ x ∙ 𝒟) ∼ ⌞ 𝒬 ⌟ x ∙ (π₁ 𝒟)

-- TODO: Stop forgetting variable names
test∼comm□π₁ : test∼ {∅} {∅ , ("'x" , □ ("A" ∧ "B"))}
                     (π₁ (⌞ ᵛ0 "'x" ⌟ "x" ∙ ᵐᵛ0 "x"))
                     (⌞ ᵛ0 "'x" ⌟ "MFRESH" ∙ π₁ (ᵐᵛ0 "MFRESH"))
test∼comm□π₁ = refl


-- comm□π₂ : ∀ {Δ Γ x A B} → (𝒬 : Δ ⁏ Γ ⊢ □ (A ∧ B)) {{_ : fresh x Δ}}
--                            (𝒟 : Δ , (x , A ∧ B) ⁏ Γ ⊢ A ∧ B)
--                         → π₂ (⌞ 𝒬 ⌟ x ∙ 𝒟) ∼ ⌞ 𝒬 ⌟ x ∙ (π₂ 𝒟)

-- TODO: Stop forgetting variable names
test∼comm□π₂ : test∼ {∅} {∅ , ("'x" , □ ("A" ∧ "B"))}
                     (π₂ (⌞ ᵛ0 "'x" ⌟ "x" ∙ ᵐᵛ0 "x"))
                     (⌞ ᵛ0 "'x" ⌟ "MFRESH" ∙ π₂ (ᵐᵛ0 "MFRESH"))
test∼comm□π₂ = refl


--------------------------------------------------------------------------------
--
-- Self-interpretation


-- weakBP : ∀ {Δ Γ A B} → (𝒟 : Δ ⁏ Γ ⊢ A)
--                      → 𝔗 $ ⌜ 𝒟 ⌝ ∼ ⌜ 𝒟 ⌝

test∼weakBP : test∼ {∅ , ("x" , "A")} {∅}
                    (ᵃˣT $ ⌜ ᵐᵛ0 "x" ⌝)
                    (ᵐᵛ0 "x")
test∼weakBP = refl


-- Andrej : ∀ {Δ Γ A B} → (𝒟 : Δ ⁏ Γ ⊢ A ⊃ B) (ℰ : Δ ⁏ Γ ⊢ A)
--                      → (𝔻 $ ⌜ 𝒟 ⌝) $ ⌜ ℰ ⌝ ∼ ⌜ 𝒟 $ ℰ ⌝

test∼Andrej : test∼ {∅ , ("f" , "A" ⊃ "B") , ("x" , "A")} {∅}
                    ((ᵃˣD $ ⌜ ᵐᵛ1 "f" ⌝) $ ⌜ ᵐᵛ0 "x" ⌝)
                    (⌜ ᵐᵛ1 "f" $ ᵐᵛ0 "x" ⌝)
test∼Andrej = refl


--------------------------------------------------------------------------------
