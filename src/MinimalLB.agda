{-# OPTIONS --without-K #-}

module MinimalLB where


--------------------------------------------------------------------------------
--
-- Prelude


open import Agda.Primitive public
  using (_⊔_)

open import Agda.Builtin.Equality
  using (_≡_ ; refl)

open import Agda.Builtin.Unit
  using (⊤ ; tt)


id : ∀ {ℓ} → {X : Set ℓ}
           → X
           → X
id x = x

_∘_ : ∀ {ℓ ℓ′ ℓ″} → {X : Set ℓ} {P : X → Set ℓ′} {Q : ∀ {x} → P x → Set ℓ″}
                  → (g : ∀ {x} → (y : P x) → Q y) (f : (x : X) → P x) (x : X)
                  → Q (f x)
(g ∘ f) x = g (f x)


data ⊥ : Set where

elim⊥ : ∀ {ℓ} → {X : Set ℓ}
               → ⊥
               → X
elim⊥ ()

¬_ : ∀ {ℓ} → Set ℓ → Set ℓ
¬ X = X → ⊥


infixl 6 _,_
record Σ {ℓ ℓ′}
         (X : Set ℓ) (P : X → Set ℓ′)
       : Set (ℓ ⊔ ℓ′) where
  constructor _,_
  field
    proj₁ : X
    proj₂ : P proj₁
open Σ public

infixl 5 _⁏_
pattern _⁏_ x y = x , y

infixl 2 _×_
_×_ : ∀ {ℓ ℓ′} → Set ℓ → Set ℓ′
               → Set (ℓ ⊔ ℓ′)
X × Y = Σ X (λ x → Y)


--------------------------------------------------------------------------------
--
-- Syntax


-- Types
infixl 9 _⩕_
infixr 7 _⇒_
data 𝒯 : Set where
  ∗    : 𝒯
  _⇒_ : (A B : 𝒯) → 𝒯
  _⩕_  : (A B : 𝒯) → 𝒯
  ⫪   : 𝒯
  □_   : (A : 𝒯) → 𝒯


-- Contexts
data 𝒞 : Set where
  ∅   : 𝒞
  _,_ : (Γ : 𝒞) (A : 𝒯) → 𝒞

𝒞² : Set
𝒞² = 𝒞 × 𝒞


-- Variables
infix 4 _∋_
data _∋_ : 𝒞 → 𝒯 → Set
  where
    zero : ∀ {Γ A} → Γ , A ∋ A

    suc  : ∀ {Γ A B} → (i : Γ ∋ A)
                     → Γ , B ∋ A

-- Syntactic entailment
infixl 5 _∙_
infix 3 _⊢_
data _⊢_ : 𝒞² → 𝒯 → Set
  where
    -- Reference to modal hypothesis
    ᵐᵛ  : ∀ {A Δ Γ} → (i : Δ ∋ A)
                    → Δ ⁏ Γ ⊢ A

    -- Reference to hypothesis
    ᵛ   : ∀ {A Δ Γ} → (i : Γ ∋ A)
                    → Δ ⁏ Γ ⊢ A

    -- Abstraction
    ƛ   : ∀ {A B Δ Γ} → (M : Δ ⁏ Γ , A ⊢ B)
                      → Δ ⁏ Γ ⊢ A ⇒ B

    -- Application
    _∙_ : ∀ {A B Δ Γ} → (M : Δ ⁏ Γ ⊢ A ⇒ B) (N : Δ ⁏ Γ ⊢ A)
                      → Δ ⁏ Γ ⊢ B

    -- Pairing
    _,_ : ∀ {A B Δ Γ} → (M : Δ ⁏ Γ ⊢ A) (N : Δ ⁏ Γ ⊢ B)
                      → Δ ⁏ Γ ⊢ A ⩕ B

    -- First projection
    π₁  : ∀ {A B Δ Γ} → (M : Δ ⁏ Γ ⊢ A ⩕ B)
                      → Δ ⁏ Γ ⊢ A

    -- Second projection
    π₂  : ∀ {A B Δ Γ} → (M : Δ ⁏ Γ ⊢ A ⩕ B)
                      → Δ ⁏ Γ ⊢ B

    -- Unit
    τ   : ∀ {Δ Γ} → Δ ⁏ Γ ⊢ ⫪

    -- Quotation
    ⌜_⌝ : ∀ {A Δ Γ} → (M : Δ ⁏ ∅ ⊢ A)
                    → Δ ⁏ Γ ⊢ □ A

    -- Unquotation
    ⌞_⌟ : ∀ {A C Δ Γ} → (M : Δ ⁏ Γ ⊢ □ A) (N : Δ , A ⁏ Γ ⊢ C)
                      → Δ ⁏ Γ ⊢ C


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


-- Normal and neutral forms
mutual
  infix 3 _⊢ⁿᶠ_
  data _⊢ⁿᶠ_ : 𝒞² → 𝒯 → Set
    where
      ƛ   : ∀ {A B Δ Γ} → (M : Δ ⁏ Γ , A ⊢ⁿᶠ B)
                        → Δ ⁏ Γ ⊢ⁿᶠ A ⇒ B

      _,_ : ∀ {A B Δ Γ} → (M : Δ ⁏ Γ ⊢ⁿᶠ A) (N : Δ ⁏ Γ ⊢ⁿᶠ B)
                        → Δ ⁏ Γ ⊢ⁿᶠ A ⩕ B

      τ   : ∀ {Δ Γ} → Δ ⁏ Γ ⊢ⁿᶠ ⫪

      ⌜_⌝ : ∀ {A Δ Γ} → (M : Δ ⁏ ∅ ⊢ A)
                      → Δ ⁏ Γ ⊢ⁿᶠ □ A

      ne  : ∀ {A Δ Γ} → (M : Δ ⁏ Γ ⊢ⁿᵉ A)
                      → Δ ⁏ Γ ⊢ⁿᶠ A

  infix 3 _⊢ⁿᵉ_
  data _⊢ⁿᵉ_ : 𝒞² → 𝒯 → Set
    where
      ᵐᵛ  : ∀ {A Δ Γ} → (i : Δ ∋ A)
                      → Δ ⁏ Γ ⊢ⁿᵉ A

      ᵛ   : ∀ {A Δ Γ} → (i : Γ ∋ A)
                      → Δ ⁏ Γ ⊢ⁿᵉ A

      _∙_ : ∀ {A B Δ Γ} → (M : Δ ⁏ Γ ⊢ⁿᵉ A ⇒ B) (N : Δ ⁏ Γ ⊢ⁿᶠ A)
                        → Δ ⁏ Γ ⊢ⁿᵉ B

      π₁  : ∀ {A B Δ Γ} → (M : Δ ⁏ Γ ⊢ⁿᵉ A ⩕ B)
                        → Δ ⁏ Γ ⊢ⁿᵉ A

      π₂  : ∀ {A B Δ Γ} → (M : Δ ⁏ Γ ⊢ⁿᵉ A ⩕ B)
                        → Δ ⁏ Γ ⊢ⁿᵉ B

      ⌞_⌟ : ∀ {A C Δ Γ} → (M : Δ ⁏ Γ ⊢ⁿᵉ □ A) (N : Δ , A ⁏ Γ ⊢ⁿᶠ C)
                        → Δ ⁏ Γ ⊢ⁿᵉ C


mutual
  embⁿᶠ : ∀ {Δ Γ A} → Δ ⁏ Γ ⊢ⁿᶠ A → Δ ⁏ Γ ⊢ A
  embⁿᶠ (ƛ M)   = ƛ (embⁿᶠ M)
  embⁿᶠ (M , N) = embⁿᶠ M , embⁿᶠ N
  embⁿᶠ τ       = τ
  embⁿᶠ (⌜ M ⌝) = ⌜ M ⌝
  embⁿᶠ (ne M)  = embⁿᵉ M

  embⁿᵉ : ∀ {Δ Γ A} → Δ ⁏ Γ ⊢ⁿᵉ A → Δ ⁏ Γ ⊢ A
  embⁿᵉ (ᵐᵛ i)    = ᵐᵛ i
  embⁿᵉ (ᵛ i)     = ᵛ i
  embⁿᵉ (M ∙ N)   = embⁿᵉ M ∙ embⁿᶠ N
  embⁿᵉ (π₁ M)    = π₁ (embⁿᵉ M)
  embⁿᵉ (π₂ M)    = π₂ (embⁿᵉ M)
  embⁿᵉ (⌞ M ⌟ N) = ⌞ embⁿᵉ M ⌟ (embⁿᶠ N)


--------------------------------------------------------------------------------
--
-- Renaming


-- Order-preserving embeddings
infix 4 _⊇_
data _⊇_ : 𝒞 → 𝒞 → Set
  where
    doneᵣ : ∅ ⊇ ∅

    wkᵣ   : ∀ {Γ Γ′ A} → (η : Γ′ ⊇ Γ)
                       → Γ′ , A ⊇ Γ

    liftᵣ : ∀ {Γ Γ′ A} → (η : Γ′ ⊇ Γ)
                       → Γ′ , A ⊇ Γ , A

infix 3 _⊇²_
_⊇²_ : 𝒞² → 𝒞² → Set
Δ′ ⁏ Γ′ ⊇² Δ ⁏ Γ = Δ′ ⊇ Δ × Γ′ ⊇ Γ


ᵐwkᵣ² : ∀ {Δ Δ′ Γ Γ′ A} → Δ′ ⁏ Γ′ ⊇² Δ ⁏ Γ
                        → Δ′ , A ⁏ Γ′ ⊇² Δ ⁏ Γ
ᵐwkᵣ² η = wkᵣ (proj₁ η) , proj₂ η

wkᵣ² : ∀ {Δ Δ′ Γ Γ′ A} → Δ′ ⁏ Γ′ ⊇² Δ ⁏ Γ
                       → Δ′ ⁏ Γ′ , A ⊇² Δ ⁏ Γ
wkᵣ² η = proj₁ η , wkᵣ (proj₂ η)


infᵣ : ∀ {Γ} → Γ ⊇ ∅
infᵣ {∅}     = doneᵣ
infᵣ {Γ , A} = wkᵣ infᵣ


idᵣ : ∀ {Γ} → Γ ⊇ Γ
idᵣ {∅}     = doneᵣ
idᵣ {Γ , A} = liftᵣ idᵣ

idᵣ² : ∀ {Δ Γ} → Δ ⁏ Γ ⊇² Δ ⁏ Γ
idᵣ² = idᵣ , idᵣ


_∘ᵣ_ : ∀ {Γ Γ′ Γ″} → Γ′ ⊇ Γ → Γ″ ⊇ Γ′
                  → Γ″ ⊇ Γ
η       ∘ᵣ doneᵣ    = η
η       ∘ᵣ wkᵣ η′   = wkᵣ (η ∘ᵣ η′)
wkᵣ η   ∘ᵣ liftᵣ η′ = wkᵣ (η ∘ᵣ η′)
liftᵣ η ∘ᵣ liftᵣ η′ = liftᵣ (η ∘ᵣ η′)

_∘ᵣ²_ : ∀ {Δ Δ′ Δ″ Γ Γ′ Γ″} → Δ′ ⁏ Γ′ ⊇² Δ ⁏ Γ → Δ″ ⁏ Γ″ ⊇² Δ′ ⁏ Γ′
                           → Δ″ ⁏ Γ″ ⊇² Δ ⁏ Γ
η ∘ᵣ² η′ = (proj₁ η ∘ᵣ proj₁ η′) , (proj₂ η ∘ᵣ proj₂ η′)


lookupᵣ : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ∋ A
                     → Γ′ ∋ A
lookupᵣ doneᵣ     i       = i
lookupᵣ (wkᵣ η)   i       = suc (lookupᵣ η i)
lookupᵣ (liftᵣ η) zero    = zero
lookupᵣ (liftᵣ η) (suc i) = suc (lookupᵣ η i)

ᵐlookupᵣ² : ∀ {Δ Δ′ Γ Γ′ A} → Δ′ ⁏ Γ′ ⊇² Δ ⁏ Γ → Δ ∋ A
                            → Δ′ ∋ A
ᵐlookupᵣ² η i = lookupᵣ (proj₁ η) i

lookupᵣ² : ∀ {Δ Δ′ Γ Γ′ A} → Δ′ ⁏ Γ′ ⊇² Δ ⁏ Γ → Γ ∋ A
                           → Γ′ ∋ A
lookupᵣ² η i = lookupᵣ (proj₂ η) i


-- Renaming
ᵐren : ∀ {Δ Δ′ Γ A} → Δ′ ⊇ Δ → Δ ⁏ Γ ⊢ A
                    → Δ′ ⁏ Γ ⊢ A
ᵐren η (ᵐᵛ i)    = ᵐᵛ (lookupᵣ η i)
ᵐren η (ᵛ i)     = ᵛ i
ᵐren η (ƛ M)     = ƛ (ᵐren η M)
ᵐren η (M ∙ N)   = ᵐren η M ∙ ᵐren η N
ᵐren η (M , N)   = ᵐren η M , ᵐren η N
ᵐren η (π₁ M)    = π₁ (ᵐren η M)
ᵐren η (π₂ M)    = π₂ (ᵐren η M)
ᵐren η τ         = τ
ᵐren η (⌜ M ⌝)   = ⌜ ᵐren η M ⌝
ᵐren η (⌞ M ⌟ N) = ⌞ ᵐren η M ⌟ (ᵐren (liftᵣ η) N)

ren : ∀ {Δ Γ Γ′ A} → Γ′ ⊇ Γ → Δ ⁏ Γ ⊢ A
                   → Δ ⁏ Γ′ ⊢ A
ren η (ᵐᵛ i)    = ᵐᵛ i
ren η (ᵛ i)     = ᵛ (lookupᵣ η i)
ren η (ƛ M)     = ƛ (ren (liftᵣ η) M)
ren η (M ∙ N)   = ren η M ∙ ren η N
ren η (M , N)   = ren η M , ren η N
ren η (π₁ M)    = π₁ (ren η M)
ren η (π₂ M)    = π₂ (ren η M)
ren η τ         = τ
ren η (⌜ M ⌝)   = ⌜ M ⌝
ren η (⌞ M ⌟ N) = ⌞ ren η M ⌟ (ren η N)

ren² : ∀ {Δ Δ′ Γ Γ′ A} → Δ′ ⁏ Γ′ ⊇² Δ ⁏ Γ → Δ ⁏ Γ ⊢ A
                       → Δ′ ⁏ Γ′ ⊢ A
ren² η M = (ᵐren (proj₁ η) ∘ ren (proj₂ η)) M


mutual
  ᵐrenⁿᶠ : ∀ {Δ Δ′ Γ A} → Δ′ ⊇ Δ → Δ ⁏ Γ ⊢ⁿᶠ A
                        → Δ′ ⁏ Γ ⊢ⁿᶠ A
  ᵐrenⁿᶠ η (ƛ M)   = ƛ (ᵐrenⁿᶠ η M)
  ᵐrenⁿᶠ η (M , N) = ᵐrenⁿᶠ η M , ᵐrenⁿᶠ η N
  ᵐrenⁿᶠ η τ       = τ
  ᵐrenⁿᶠ η (⌜ M ⌝) = ⌜ ᵐren η M ⌝
  ᵐrenⁿᶠ η (ne M)  = ne (ᵐrenⁿᵉ η M)

  ᵐrenⁿᵉ : ∀ {Δ Δ′ Γ A} → Δ′ ⊇ Δ → Δ ⁏ Γ ⊢ⁿᵉ A
                        → Δ′ ⁏ Γ ⊢ⁿᵉ A
  ᵐrenⁿᵉ η (ᵐᵛ i)    = ᵐᵛ (lookupᵣ η i)
  ᵐrenⁿᵉ η (ᵛ i )    = ᵛ i
  ᵐrenⁿᵉ η (M ∙ N)   = ᵐrenⁿᵉ η M ∙ ᵐrenⁿᶠ η N
  ᵐrenⁿᵉ η (π₁ M)    = π₁ (ᵐrenⁿᵉ η M)
  ᵐrenⁿᵉ η (π₂ M)    = π₂ (ᵐrenⁿᵉ η M)
  ᵐrenⁿᵉ η (⌞ M ⌟ N) = ⌞ ᵐrenⁿᵉ η M ⌟ (ᵐrenⁿᶠ (liftᵣ η) N)

mutual
  renⁿᶠ : ∀ {Δ Γ Γ′ A} → Γ′ ⊇ Γ → Δ ⁏ Γ ⊢ⁿᶠ A
                       → Δ ⁏ Γ′ ⊢ⁿᶠ A
  renⁿᶠ η (ƛ M)   = ƛ (renⁿᶠ (liftᵣ η) M)
  renⁿᶠ η (M , N) = renⁿᶠ η M , renⁿᶠ η N
  renⁿᶠ η τ       = τ
  renⁿᶠ η (⌜ M ⌝) = ⌜ M ⌝
  renⁿᶠ η (ne M)  = ne (renⁿᵉ η M)

  renⁿᵉ : ∀ {Δ Γ Γ′ A} → Γ′ ⊇ Γ → Δ ⁏ Γ ⊢ⁿᵉ A
                       → Δ ⁏ Γ′ ⊢ⁿᵉ A
  renⁿᵉ η (ᵐᵛ i)    = ᵐᵛ i
  renⁿᵉ η (ᵛ i)     = ᵛ (lookupᵣ η i)
  renⁿᵉ η (M ∙ N)   = renⁿᵉ η M ∙ renⁿᶠ η N
  renⁿᵉ η (π₁ M)    = π₁ (renⁿᵉ η M)
  renⁿᵉ η (π₂ M)    = π₂ (renⁿᵉ η M)
  renⁿᵉ η (⌞ M ⌟ N) = ⌞ renⁿᵉ η M ⌟ (renⁿᶠ η N)

renⁿᶠ² : ∀ {Δ Δ′ Γ Γ′ A} → Δ′ ⁏ Γ′ ⊇² Δ ⁏ Γ → Δ ⁏ Γ ⊢ⁿᶠ A
                         → Δ′ ⁏ Γ′ ⊢ⁿᶠ A
renⁿᶠ² η M = (ᵐrenⁿᶠ (proj₁ η) ∘ renⁿᶠ (proj₂ η)) M

renⁿᵉ² : ∀ {Δ Δ′ Γ Γ′ A} → Δ′ ⁏ Γ′ ⊇² Δ ⁏ Γ → Δ ⁏ Γ ⊢ⁿᵉ A
                         → Δ′ ⁏ Γ′ ⊢ⁿᵉ A
renⁿᵉ² η M = (ᵐrenⁿᵉ (proj₁ η) ∘ renⁿᵉ (proj₂ η)) M


--------------------------------------------------------------------------------
--
-- Substitution


-- Simultaneous ubstitutions
infix 3 _⊢⋆_
data _⊢⋆_ : 𝒞² → 𝒞 → Set
  where
    ∅   : ∀ {Δ Γ} → Δ ⁏ Γ ⊢⋆ ∅

    _,_ : ∀ {Δ Γ Ξ A} → (σ : Δ ⁏ Γ ⊢⋆ Ξ) (M : Δ ⁏ Γ ⊢ A)
                      → Δ ⁏ Γ ⊢⋆ Ξ , A


ᵐren⋆ : ∀ {Δ Δ′ Γ Ξ} → Δ′ ⊇ Δ → Δ ⁏ Γ ⊢⋆ Ξ
                     → Δ′ ⁏ Γ ⊢⋆ Ξ
ᵐren⋆ η ∅       = ∅
ᵐren⋆ η (σ , M) = ᵐren⋆ η σ , ᵐren η M

ren⋆ : ∀ {Δ Γ Γ′ Ξ} → Γ′ ⊇ Γ → Δ ⁏ Γ ⊢⋆ Ξ
                    → Δ ⁏ Γ′ ⊢⋆ Ξ
ren⋆ η ∅       = ∅
ren⋆ η (σ , M) = ren⋆ η σ , ren η M


ᵐwkₛ : ∀ {Δ Γ Ξ A} → Δ ⁏ Γ ⊢⋆ Ξ
                   → Δ , A ⁏ Γ ⊢⋆ Ξ
ᵐwkₛ σ = ᵐren⋆ (wkᵣ idᵣ) σ

wkₛ : ∀ {Δ Γ Ξ A} → Δ ⁏ Γ ⊢⋆ Ξ
                  → Δ ⁏ Γ , A ⊢⋆ Ξ
wkₛ σ = ren⋆ (wkᵣ idᵣ) σ

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
lookupₛ (σ , M) zero    = M
lookupₛ (σ , M) (suc i) = lookupₛ σ i


-- Substitution
ᵐsub : ∀ {Δ Γ Ξ A} → Δ ⁏ ∅ ⊢⋆ Ξ → Ξ ⁏ Γ ⊢ A
                   → Δ ⁏ Γ ⊢ A
ᵐsub σ (ᵐᵛ i)    = ren infᵣ (lookupₛ σ i)
ᵐsub σ (ᵛ i)     = ᵛ i
ᵐsub σ (ƛ M)     = ƛ (ᵐsub σ M)
ᵐsub σ (M ∙ N)   = ᵐsub σ M ∙ ᵐsub σ N
ᵐsub η (M , N)   = ᵐsub η M , ᵐsub η N
ᵐsub η (π₁ M)    = π₁ (ᵐsub η M)
ᵐsub η (π₂ M)    = π₂ (ᵐsub η M)
ᵐsub η τ         = τ
ᵐsub σ ⌜ M ⌝     = ⌜ ᵐsub σ M ⌝
ᵐsub σ (⌞ M ⌟ N) = ⌞ ᵐsub σ M ⌟ (ᵐsub (ᵐliftₛ σ) N)

sub : ∀ {Δ Γ Ξ A} → Δ ⁏ Γ ⊢⋆ Ξ → Δ ⁏ Ξ ⊢ A
                  → Δ ⁏ Γ ⊢ A
sub σ (ᵐᵛ i)    = ᵐᵛ i
sub σ (ᵛ i)     = lookupₛ σ i
sub σ (ƛ M)     = ƛ (sub (liftₛ σ) M)
sub σ (M ∙ N)   = sub σ M ∙ sub σ N
sub η (M , N)   = sub η M , sub η N
sub η (π₁ M)    = π₁ (sub η M)
sub η (π₂ M)    = π₂ (sub η M)
sub η τ         = τ
sub σ ⌜ M ⌝     = ⌜ M ⌝
sub σ (⌞ M ⌟ N) = ⌞ sub σ M ⌟ (sub (ᵐwkₛ σ) N)


--------------------------------------------------------------------------------
--
-- Semantics


-- Introspective Kripke models
record 𝔐 : Set₁ where
  field
    𝒲      : Set

    𝒢      : 𝒲 → Set

    _≥_    : 𝒲 → 𝒲 → Set

    idₐ    : ∀ {w} → w ≥ w

    _∘ₐ_   : ∀ {w w′ w″} → w′ ≥ w → w″ ≥ w′
                         → w″ ≥ w

    acc𝒢   : ∀ {w w′} → w′ ≥ w → 𝒢 w
                      → 𝒢 w′

    peek²  : 𝒲 → 𝒞²

    peekₐ² : ∀ {w w′} → w′ ≥ w
                      → peek² w′ ⊇² peek² w

open 𝔐 {{…}} public


ᵐpeek : ∀ {{_ : 𝔐}} → 𝒲 → 𝒞
ᵐpeek w = proj₁ (peek² w)

peek : ∀ {{_ : 𝔐}} → 𝒲 → 𝒞
peek w = proj₂ (peek² w)

ᵐpeekₐ : ∀ {{_ : 𝔐}} {w w′} → w′ ≥ w
                            → ᵐpeek w′ ⊇ ᵐpeek w
ᵐpeekₐ w = proj₁ (peekₐ² w)

peekₐ : ∀ {{_ : 𝔐}} {w w′} → w′ ≥ w
                           → peek w′ ⊇ peek w
peekₐ w = proj₂ (peekₐ² w)


-- Values
mutual
  infix 3 _⊩_
  _⊩_ : ∀ {{_ : 𝔐}} → 𝒲 → 𝒯 → Set

  w ⊩ ∗      = 𝒢 w

  w ⊩ A ⇒ B = ∀ {w′} → (η : w′ ≥ w) (aₖ : w′ ∂⊩ A)
                       → w′ ∂⊩ B

  w ⊩ A ⩕ B  = w ∂⊩ A × w ∂⊩ B

  w ⊩ ⫪     = ⊤

  w ⊩ □ A    = ∀ {w′} → (η : w′ ≥ w)
                       → w′ ᵐ∂⊩ A

  infix 3 _∂⊩_
  _∂⊩_ : ∀ {{_ : 𝔐}} → 𝒲 → 𝒯 → Set
  w ∂⊩ A = ∀ {w′ C} → (η : w′ ≥ w) (f : ∀ {w″} → w″ ≥ w′ → w″ ⊩ A
                                                 → peek² w″ ⊢ⁿᶠ C)
                     → peek² w′ ⊢ⁿᶠ C

  infix 3 _ᵐ∂⊩_
  _ᵐ∂⊩_ : ∀ {{_ : 𝔐}} → 𝒲 → 𝒯 → Set
  w ᵐ∂⊩ A = ᵐpeek w ⁏ ∅ ⊢ A × w ∂⊩ A


-- Environments
infix 3 _∂⊩⋆_
data _∂⊩⋆_ {{_ : 𝔐}} : 𝒲 → 𝒞 → Set
  where
    ∅   : ∀ {w} → w ∂⊩⋆ ∅

    _,_ : ∀ {A Ξ w} → (ρ : w ∂⊩⋆ Ξ) (aₖ : w ∂⊩ A)
                    → w ∂⊩⋆ Ξ , A


infix 3 _ᵐ∂⊩⋆_
data _ᵐ∂⊩⋆_ {{_ : 𝔐}} : 𝒲 → 𝒞 → Set
  where
    ∅   : ∀ {w} → w ᵐ∂⊩⋆ ∅

    _,_ : ∀ {A Ξ w} → (ρ : w ᵐ∂⊩⋆ Ξ) (Maₖ : w ᵐ∂⊩ A)
                    → w ᵐ∂⊩⋆ Ξ , A


syn⋆ : ∀ {{_ : 𝔐}} {w Ξ} → w ᵐ∂⊩⋆ Ξ
                         → ᵐpeek w ⁏ ∅ ⊢⋆ Ξ
syn⋆ ∅              = ∅
syn⋆ (ρ , (M , aₖ)) = syn⋆ ρ , M

sem⋆ : ∀ {{_ : 𝔐}} {w Ξ} → w ᵐ∂⊩⋆ Ξ
                         → w ∂⊩⋆ Ξ
sem⋆ ∅              = ∅
sem⋆ (ρ , (M , aₖ)) = sem⋆ ρ , aₖ


-- Semantic entailment
infix 3 _⊨_
_⊨_ : 𝒞² → 𝒯 → Set₁
Δ ⁏ Γ ⊨ A = ∀ {{_ : 𝔐}} {w} → w ᵐ∂⊩⋆ Δ → w ∂⊩⋆ Γ
                             → w ∂⊩ A


-- Accessibility
mutual
  acc : ∀ {{_ : 𝔐}} {A w w′} → w′ ≥ w → w ⊩ A
                             → w′ ⊩ A
  acc {∗}      η M = acc𝒢 η M
  acc {A ⇒ B} η f = λ η′ → f (η ∘ₐ η′)
  acc {A ⩕ B}  η p = ∂acc {A} η (proj₁ p) , ∂acc {B} η (proj₂ p)
  acc {⫪}     η t = tt
  acc {□ A}    η f = λ η′ → f (η ∘ₐ η′)

  ∂acc : ∀ {{_ : 𝔐}} {A w w′} → w′ ≥ w → w ∂⊩ A
                              → w′ ∂⊩ A
  ∂acc η aₖ = λ η′ f → aₖ (η ∘ₐ η′) f

ᵐ∂acc : ∀ {{_ : 𝔐}} {A w w′} → w′ ≥ w → w ᵐ∂⊩ A
                             → w′ ᵐ∂⊩ A
ᵐ∂acc {A} η (M , aₖ) = ren² (ᵐpeekₐ η , doneᵣ) M , ∂acc {A} η aₖ


∂acc⋆ : ∀ {{_ : 𝔐}} {Ξ w w′} → w′ ≥ w → w ∂⊩⋆ Ξ
                             → w′ ∂⊩⋆ Ξ
∂acc⋆ η ∅              = ∅
∂acc⋆ η (_,_ {A} ρ aₖ) = ∂acc⋆ η ρ , ∂acc {A} η aₖ

ᵐ∂acc⋆ : ∀ {{_ : 𝔐}} {Ξ w w′} → w′ ≥ w → w ᵐ∂⊩⋆ Ξ
                              → w′ ᵐ∂⊩⋆ Ξ
ᵐ∂acc⋆ η ∅               = ∅
ᵐ∂acc⋆ η (_,_ {A} ρ Maₖ) = ᵐ∂acc⋆ η ρ , ᵐ∂acc {A} η Maₖ


-- Kripke continuation monad
return : ∀ {{_ : 𝔐}} {A w} → w ⊩ A
                           → w ∂⊩ A
return {A} a = λ η f →
                 f idₐ (acc {A} η a)

bind : ∀ {{_ : 𝔐}} {A C w} → w ∂⊩ A → (∀ {w′} → w′ ≥ w → w′ ⊩ A
                                                 → w′ ∂⊩ C)
                           → w ∂⊩ C
bind aₖ f = λ η f′ →
              aₖ η (λ η′ a →
                f (η ∘ₐ η′) a idₐ (λ η″ b →
                  f′ (η′ ∘ₐ η″) b))


∂lookup : ∀ {{_ : 𝔐}} {Ξ A w} → w ∂⊩⋆ Ξ → Ξ ∋ A
                              → w ∂⊩ A
∂lookup (ρ , aₖ) zero    = aₖ
∂lookup (ρ , aₖ) (suc i) = ∂lookup ρ i


∂ƛ : ∀ {{_ : 𝔐}} {A B w} → (∀ {w′} → w′ ≥ w → w′ ∂⊩ A
                                    → w′ ∂⊩ B)
                         → w ∂⊩ A ⇒ B
∂ƛ {A} {B} f = return {A ⇒ B} (λ η aₖ → f η aₖ)

∂∙ : ∀ {{_ : 𝔐}} {A B w} → w ∂⊩ A ⇒ B → w ∂⊩ A
                         → w ∂⊩ B
∂∙ {A} {B} fₖ aₖ = bind {A ⇒ B} {B} fₖ (λ η f → f idₐ (∂acc {A} η aₖ))

∂, : ∀ {{_ : 𝔐}} {A B w} → w ∂⊩ A → w ∂⊩ B
                         → w ∂⊩ A ⩕ B
∂, {A} {B} aₖ bₖ = return {A ⩕ B} (aₖ , bₖ)

∂π₁ : ∀ {{_ : 𝔐}} {A B w} → w ∂⊩ A ⩕ B
                          → w ∂⊩ A
∂π₁ {A} {B} pₖ = bind {A ⩕ B} {A} pₖ (λ η p → proj₁ p)

∂π₂ : ∀ {{_ : 𝔐}} {A B w} → w ∂⊩ A ⩕ B
                          → w ∂⊩ B
∂π₂ {A} {B} pₖ = bind {A ⩕ B} {B} pₖ (λ η p → proj₂ p)

∂τ : ∀ {{_ : 𝔐}} {w} → w ∂⊩ ⫪
∂τ = return {⫪} tt

∂⌜⌝ : ∀ {{_ : 𝔐}} {A w} → (∀ {w′} → w′ ≥ w
                                   → w′ ᵐ∂⊩ A)
                        → w ∂⊩ □ A
∂⌜⌝ {A} f = return {□ A} (λ η → f η)

∂⌞⌟ : ∀ {{_ : 𝔐}} {A C w} → w ∂⊩ □ A
                          → (∀ {w′} → w′ ≥ w → w′ ᵐ∂⊩ A
                                     → w′ ∂⊩ C)
                          → w ∂⊩ C
∂⌞⌟ {A} {C} aₖ f = bind {□ A} {C} aₖ (λ η f′ → f η (f′ idₐ))


-- Soundness
⟦_⟧ : ∀ {Δ Γ A} → Δ ⁏ Γ ⊢ A
                → Δ ⁏ Γ ⊨ A
⟦ ᵐᵛ i ⟧            ᵐρ ρ = ∂lookup (sem⋆ ᵐρ) i
⟦ ᵛ i ⟧             ᵐρ ρ = ∂lookup ρ i
⟦ ƛ   {A} {B} M ⟧   ᵐρ ρ = ∂ƛ {A} {B} (λ η aₖ →
                             ⟦ M ⟧ (ᵐ∂acc⋆ η ᵐρ) (∂acc⋆ η ρ , aₖ))
⟦ _∙_ {A} {B} M N ⟧ ᵐρ ρ = ∂∙ {A} {B} (⟦ M ⟧ ᵐρ ρ) (⟦ N ⟧ ᵐρ ρ)
⟦ _,_ {A} {B} M N ⟧ ᵐρ ρ = ∂, {A} {B} (⟦ M ⟧ ᵐρ ρ) (⟦ N ⟧ ᵐρ ρ)
⟦ π₁  {A} {B} M ⟧   ᵐρ ρ = ∂π₁ {A} {B} (⟦ M ⟧ ᵐρ ρ)
⟦ π₂  {A} {B} M ⟧   ᵐρ ρ = ∂π₂ {A} {B} (⟦ M ⟧ ᵐρ ρ)
⟦ τ ⟧               ᵐρ ρ = ∂τ
⟦ ⌜_⌝ {A} M ⟧       ᵐρ ρ = ∂⌜⌝ {A} (λ η →
                             ᵐsub (syn⋆ (ᵐ∂acc⋆ η ᵐρ)) M , ⟦ M ⟧ (ᵐ∂acc⋆ η ᵐρ) ∅)
⟦ ⌞_⌟ {A} {C} M N ⟧ ᵐρ ρ = ∂⌞⌟ {A} {C} (⟦ M ⟧ ᵐρ ρ) (λ η Maₖ →
                             ⟦ N ⟧ (ᵐ∂acc⋆ η ᵐρ , Maₖ) (∂acc⋆ η ρ))


-- Canonical model
instance
  𝔠 : 𝔐
  𝔠 = record
        { 𝒲      = 𝒞²
        ; 𝒢      = _⊢ⁿᶠ ∗
        ; _≥_    = _⊇²_
        ; idₐ    = idᵣ²
        ; _∘ₐ_   = _∘ᵣ²_
        ; acc𝒢   = renⁿᶠ²
        ; peek²  = id
        ; peekₐ² = id
        }

-- Canonical soundness and completeness
mutual
  ⟦_⟧ᶜ : ∀ {A Δ Γ} → Δ ⁏ Γ ⊢ⁿᵉ A
                   → Δ ⁏ Γ ∂⊩ A
  ⟦_⟧ᶜ {∗}      M = return {∗}      (ne M)
  ⟦_⟧ᶜ {A ⇒ B} M = return {A ⇒ B} (λ η aₖ → ⟦ renⁿᵉ² η M ∙ reifyᶜ aₖ ⟧ᶜ)
  ⟦_⟧ᶜ {A ⩕ B}  M = return {A ⩕ B}  (⟦ π₁ M ⟧ᶜ , ⟦ π₂ M ⟧ᶜ)
  ⟦_⟧ᶜ {⫪}     M = return {⫪}     tt
  ⟦_⟧ᶜ {□ A}    M = λ η f →
                      ne (⌞ renⁿᵉ² η M ⌟ (f (ᵐwkᵣ² idᵣ²) (λ η′ →
                        ᵐᵛ (ᵐlookupᵣ² η′ zero) , ⟦ ᵐᵛ (ᵐlookupᵣ² η′ zero) ⟧ᶜ)))

  reifyᶜ : ∀ {A Δ Γ} → Δ ⁏ Γ ∂⊩ A
                     → Δ ⁏ Γ ⊢ⁿᶠ A
  reifyᶜ {∗}      aₖ = aₖ idᵣ² (λ η M → M)
  reifyᶜ {A ⇒ B} aₖ = aₖ idᵣ² (λ η f → ƛ (reifyᶜ (f (wkᵣ² idᵣ²) ⟦ ᵛ zero ⟧ᶜ)))
  reifyᶜ {A ⩕ B}  aₖ = aₖ idᵣ² (λ η p → reifyᶜ (proj₁ p) , reifyᶜ (proj₂ p))
  reifyᶜ {⫪}     aₖ = aₖ idᵣ² (λ η t → τ)
  reifyᶜ {□ A}    aₖ = aₖ idᵣ² (λ η f → ⌜ proj₁ (f idᵣ²) ⌝)


ᵐidₑ : ∀ {Δ Γ} → Δ ⁏ Γ ᵐ∂⊩⋆ Δ
ᵐidₑ {∅}     = ∅
ᵐidₑ {Δ , A} = ᵐ∂acc⋆ (ᵐwkᵣ² idᵣ²) ᵐidₑ , (ᵐᵛ zero , ⟦ ᵐᵛ zero ⟧ᶜ)

idₑ : ∀ {Γ Δ} → Δ ⁏ Γ ∂⊩⋆ Γ
idₑ {∅}     = ∅
idₑ {Γ , A} = ∂acc⋆ (wkᵣ² idᵣ²) idₑ , ⟦ ᵛ zero ⟧ᶜ


-- Completeness
reify : ∀ {Δ Γ A} → Δ ⁏ Γ ⊨ A
                  → Δ ⁏ Γ ⊢ⁿᶠ A
reify 𝔞 = reifyᶜ (𝔞 ᵐidₑ idₑ)


-- Normalisation
nf : ∀ {Δ Γ A} → Δ ⁏ Γ ⊢ A
               → Δ ⁏ Γ ⊢ⁿᶠ A
nf = reify ∘ ⟦_⟧


--------------------------------------------------------------------------------
--
-- Examples


𝕀 : ∀ {A Δ Γ} → Δ ⁏ Γ ⊢ A ⇒ A
𝕀 = ƛ ᵛ0

𝕂 : ∀ {A B Δ Γ} → Δ ⁏ Γ ⊢ A ⇒ B ⇒ A
𝕂 = ƛ (ƛ ᵛ1)

𝕊 : ∀ {A B C Δ Γ} → Δ ⁏ Γ ⊢ (A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C
𝕊 = ƛ (ƛ (ƛ ((ᵛ2 ∙ ᵛ0) ∙ (ᵛ1 ∙ ᵛ0))))


𝔻 : ∀ {A B Δ Γ} → Δ ⁏ Γ ⊢ □ (A ⇒ B) ⇒ □ A ⇒ □ B
𝔻 = ƛ (ƛ (⌞ ᵛ1 ⌟ (⌞ ᵛ0 ⌟ ⌜ ᵐᵛ1 ∙ ᵐᵛ0 ⌝)))

𝕋 : ∀ {A Δ Γ} → Δ ⁏ Γ ⊢ □ A ⇒ A
𝕋 = ƛ (⌞ ᵛ0 ⌟ ᵐᵛ0)

𝟜 : ∀ {A Δ Γ} → Δ ⁏ Γ ⊢ □ A ⇒ □ □ A
𝟜 = ƛ (⌞ ᵛ0 ⌟ ⌜ ⌜ ᵐᵛ0 ⌝ ⌝)


--------------------------------------------------------------------------------
--
-- Conversion tests


test : ∀ {Δ Γ A} → Δ ⁏ Γ ⊢ A → Δ ⁏ Γ ⊢ A
test = embⁿᶠ ∘ nf


-- red⇒ : ∀ {Δ Γ A B} → (M : Δ ⁏ Γ , A ⊢ B) (N : Δ ⁏ Γ ⊢ A)
--                     → ƛ M ∙ N ∼ sub (idₛ , N) M

test_red⇒ : test {∅} {∅ , ∗} (ƛ ᵛ0 ∙ ᵛ0) ≡ ᵛ0
test_red⇒ = refl


-- red⩕₁ : ∀ {Δ Γ A B} → (M : Δ ⁏ Γ ⊢ A) (N : Δ ⁏ Γ ⊢ B)
--                     → π₁ (M , N) ∼ M

test_red⩕₁ : test {∅} {∅ , ∗ , ∗} (π₁ (ᵛ1 , ᵛ0)) ≡ ᵛ1
test_red⩕₁ = refl


-- red⩕₂ : ∀ {Δ Γ A B} → (M : Δ ⁏ Γ ⊢ A) (N : Δ ⁏ Γ ⊢ B)
--                     → π₂ (M , N) ∼ N
test_red⩕₂ : test {∅} {∅ , ∗ , ∗} (π₂ (ᵛ1 , ᵛ0)) ≡ ᵛ0
test_red⩕₂ = refl


-- red□ : ∀ {Δ Γ A C} → (M : Δ ⁏ ∅ ⊢ A) (N : Δ , A ⁏ Γ ⊢ C)
--                    → ⌞ ⌜ M ⌝ ⌟ N ∼ ᵐsub (ᵐidₛ , M) N

test_red□ : test {∅ , ∗} {∅} (⌞ ⌜ ᵐᵛ0 ⌝ ⌟ ᵐᵛ0) ≡ ᵐᵛ0
test_red□ = refl


-- exp⇒ : ∀ {Δ Γ A B} → (M : Δ ⁏ Γ ⊢ A ⇒ B)
--                     → M ∼ ƛ (ren (wkᵣ idᵣ) M ∙ ᵛ0)

test_exp⇒ : test {∅} {∅ , ∗ ⇒ ∗} ᵛ0 ≡ ƛ (ren (wkᵣ idᵣ) ᵛ0 ∙ ᵛ0)
test_exp⇒ = refl


-- exp⩕ : ∀ {Δ Γ A B} → (M : Δ ⁏ Γ ⊢ A ⩕ B)
--                    → M ∼ π₁ M , π₂ M

test_exp⩕ : test {∅} {∅ , ∗ ⩕ ∗} ᵛ0 ≡ π₁ ᵛ0 , π₂ ᵛ0
test_exp⩕ = refl


-- exp⫪ : ∀ {Δ Γ} → (M : Δ ⁏ Γ ⊢ ⫪)
--                 → M ∼ τ

test_exp⫪ : test {∅} {∅ , ⫪} ᵛ0 ≡ τ
test_exp⫪ = refl


-- exp□ : ∀ {Δ Γ} → (M : Δ ⁏ Γ ⊢ □ A)
--                → M ∼ ⌞ M ⌟ ⌜ ᵐᵛ0 ⌝

test_exp□ : test {∅} {∅ , □ ∗} ᵛ0 ≡ ⌞ ᵛ0 ⌟ ⌜ ᵐᵛ0 ⌝
test_exp□ = refl


-- comm□∙ : ∀ {Δ Γ A B X} → (K : Δ ⁏ Γ ⊢ □ X)
--                           (M : Δ , X ⁏ Γ ⊢ A ⇒ B) (N : Δ ⁏ Γ ⊢ A)
--                        → (⌞ K ⌟ M) ∙ N ∼ ⌞ K ⌟ (M ∙ (ᵐren (wkᵣ idᵣ) N))

test_comm□∙ : test {∅} {∅ , □ (∗ ⇒ ∗) , ∗} ((⌞ ᵛ1 ⌟ ᵐᵛ0) ∙ ᵛ0) ≡ ⌞ ᵛ1 ⌟ (ᵐᵛ0 ∙ ᵐren (wkᵣ idᵣ) ᵛ0)
test_comm□∙ = refl


-- comm□⌞⌟ : ∀ {Δ Γ A C X} → (K : Δ ⁏ Γ ⊢ □ X)
--                            (M : Δ , X ⁏ Γ ⊢ □ A) (N : Δ , A ⁏ Γ ⊢ C)
--                         → ⌞ (⌞ K ⌟ M) ⌟ N ∼ ⌞ K ⌟ (⌞ M ⌟ (ᵐren (wkᵣ idᵣ) N))

test_comm□⌞⌟ : test {∅} {∅ , □ □ ∗} (⌞ (⌞ ᵛ0 ⌟ ᵐᵛ0) ⌟ ᵐᵛ0) ≡ ⌞ ᵛ0 ⌟ (⌞ ᵐᵛ0 ⌟ ᵐᵛ0)
test_comm□⌞⌟ = refl


-- comm□π₁ : ∀ {Δ Γ A B X} → (K : Δ ⁏ Γ ⊢ □ X)
--                            (M : Δ , X ⁏ Γ ⊢ A ⩕ B)
--                         → π₁ (⌞ K ⌟ M) ∼ ⌞ K ⌟ (π₁ M)

test_comm□π₁ : test {∅} {∅ , □ (∗ ⩕ ∗)} (π₁ (⌞ ᵛ0 ⌟ ᵐᵛ0)) ≡ ⌞ ᵛ0 ⌟ (π₁ ᵐᵛ0)
test_comm□π₁ = refl


-- comm□π₂ : ∀ {Δ Γ A B X} → (K : Δ ⁏ Γ ⊢ □ X)
--                            (M : Δ , X ⁏ Γ ⊢ A ⩕ B)
--                         → π₂ (⌞ K ⌟ M) ∼ ⌞ K ⌟ (π₂ M)

test_comm□π₂ : test {∅} {∅ , □ (∗ ⩕ ∗)} (π₂ (⌞ ᵛ0 ⌟ ᵐᵛ0)) ≡ ⌞ ᵛ0 ⌟ (π₂ ᵐᵛ0)
test_comm□π₂ = refl


--------------------------------------------------------------------------------


-- weakBP : ∀ {Δ Γ A B} → (M : Δ ⁏ Γ ⊢ A)
--                      → 𝕋 ∙ ⌜ M ⌝ ∼ ⌜ M ⌝

test_weakBP : test {∅ , ∗} {∅} (𝕋 ∙ ⌜ ᵐᵛ0 ⌝) ≡ ᵐᵛ0
test_weakBP = refl


-- Andrej : ∀ {Δ Γ A B} → (M : Δ ⁏ Γ ⊢ A ⇒ B) (N : Δ ⁏ Γ ⊢ A)
--                      → (𝔻 ∙ ⌜ M ⌝) ∙ ⌜ N ⌝ ∼ ⌜ M ∙ N ⌝

test_Andrej : test {∅ , ∗ ⇒ ∗ , ∗} {∅} ((𝔻 ∙ ⌜ ᵐᵛ1 ⌝) ∙ ⌜ ᵐᵛ0 ⌝) ≡ ⌜ ᵐᵛ1 ∙ ᵐᵛ0 ⌝
test_Andrej = refl
