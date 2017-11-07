module STLC-Base where

open import Prelude public


--------------------------------------------------------------------------------
--
-- Syntax


-- Types
infixr 7 _⊃_
data Tp : Set where
  •   : Tp
  _⊃_ : (A B : Tp) → Tp


-- Contexts
Cx : Set
Cx = List Tp


-- Syntactic entailment
infix 3 _⊢_
data _⊢_ : Cx → Tp → Set
  where
    ᵛ   : ∀ {A Γ} → (i : Γ ∋ A)
                  → Γ ⊢ A

    ƛ   : ∀ {A B Γ} → (𝒟 : Γ , A ⊢ B)
                    → Γ ⊢ A ⊃ B

    _$_ : ∀ {A B Γ} → (𝒟 : Γ ⊢ A ⊃ B) (ℰ : Γ ⊢ A)
                    → Γ ⊢ B


-- Normal and neutral forms
mutual
  infix 3 _⊢ₙₘ_
  data _⊢ₙₘ_ : Cx → Tp → Set
    where
      ƛ   : ∀ {A B Γ} → (𝒟 : Γ , A ⊢ₙₘ B)
                      → Γ ⊢ₙₘ A ⊃ B

      ⁿᵗ  : ∀ {Γ} → (𝒟 : Γ ⊢ₙₜ •)
                  → Γ ⊢ₙₘ •

  infix 3 _⊢ₙₜ_
  data _⊢ₙₜ_ : Cx → Tp → Set
    where
      ᵛ   : ∀ {A Γ} → (i : Γ ∋ A)
                    → Γ ⊢ₙₜ A

      _$_ : ∀ {A B Γ} → (𝒟 : Γ ⊢ₙₜ A ⊃ B) (ℰ : Γ ⊢ₙₘ A)
                      → Γ ⊢ₙₜ B


mutual
  embₙₘ : ∀ {Γ A} → Γ ⊢ₙₘ A → Γ ⊢ A
  embₙₘ (ƛ 𝒟)   = ƛ (embₙₘ 𝒟)
  embₙₘ (ⁿᵗ 𝒟)  = embₙₜ 𝒟

  embₙₜ : ∀ {Γ A} → Γ ⊢ₙₜ A → Γ ⊢ A
  embₙₜ (ᵛ i)   = ᵛ i
  embₙₜ (𝒟 $ ℰ) = embₙₜ 𝒟 $ embₙₘ ℰ


--------------------------------------------------------------------------------
--
-- Renaming


ren : ∀ {Γ Γ′ A} →    Γ′ ⊇ Γ    →    Γ ⊢ A
                 ----------------------------
                 →    Γ′ ⊢ A

ren η (ᵛ i)   = ᵛ (lookupᵣ η i)
ren η (ƛ 𝒟)   = ƛ (ren (lift η) 𝒟)
ren η (𝒟 $ ℰ) = ren η 𝒟 $ ren η ℰ


mutual
  renₙₘ : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢ₙₘ A
                     → Γ′ ⊢ₙₘ A
  renₙₘ η (ƛ 𝒟)   = ƛ (renₙₘ (lift η) 𝒟)
  renₙₘ η (ⁿᵗ 𝒟)  = ⁿᵗ (renₙₜ η 𝒟)

  renₙₜ : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢ₙₜ A
                     → Γ′ ⊢ₙₜ A
  renₙₜ η (ᵛ i)   = ᵛ (lookupᵣ η i)
  renₙₜ η (𝒟 $ ℰ) = renₙₜ η 𝒟 $ renₙₘ η ℰ


--------------------------------------------------------------------------------
--
-- Substitution


{-
-- Simultaneous substitutions
infix 3 _⊢⋆_
_⊢⋆_ : Cx → List Tp → Set
Γ ⊢⋆ Ξ = All (Γ ⊢_) Ξ


ren⋆ : ∀ {Γ Γ′ Ξ} → Γ′ ⊇ Γ → Γ ⊢⋆ Ξ
                  → Γ′ ⊢⋆ Ξ
ren⋆ η σ = mapₐ (ren η) σ


wkₛ : ∀ {Γ Ξ A} → Γ ⊢⋆ Ξ
                → Γ , A ⊢⋆ Ξ
wkₛ σ = ren⋆ (wk idᵣ) σ

liftₛ : ∀ {Γ Ξ A} → Γ ⊢⋆ Ξ
                  → Γ , A ⊢⋆ Ξ , A
liftₛ σ = wkₛ σ , ᵛ zero


idₛ : ∀ {Γ} → Γ ⊢⋆ Γ
idₛ {∅}     = ∅
idₛ {Γ , A} = liftₛ idₛ


lookupₛ : ∀ {Γ Ξ A} → Γ ⊢⋆ Ξ → Ξ ∋ A
                    → Γ ⊢ A
lookupₛ σ i = lookupₐ σ i


-- Substitution
sub : ∀ {Γ Ξ A} → Γ ⊢⋆ Ξ → Ξ ⊢ A
                → Γ ⊢ A
sub σ (ᵛ i)   = lookupₛ σ i
sub σ (ƛ 𝒟)   = ƛ (sub (liftₛ σ) 𝒟)
sub σ (𝒟 $ ℰ) = sub σ 𝒟 $ sub σ ℰ
-}


--------------------------------------------------------------------------------
--
-- Semantics


-- Kripke models
record 𝔎 : Set₁ where
  field
    𝒲    : Set

    𝒱    : 𝒲 → Set

    _≥_  : 𝒲 → 𝒲 → Set

    idₐ  : ∀ {w} → w ≥ w

    _∘ₐ_ : ∀ {w w′ w″} → w′ ≥ w → w″ ≥ w′
                       → w″ ≥ w

    movᵥ : ∀ {w w′} → w′ ≥ w → 𝒱 w
                    → 𝒱 w′

open 𝔎 {{…}} public


-- Values
infix 3 _⊩_
_⊩_ : ∀ {{𝔐 : 𝔎}} → 𝒲 → Tp → Set

w ⊩ •     = 𝒱 w

w ⊩ A ⊃ B = ∀ {w′} → (η : w′ ≥ w) (k : w′ ⊩ A)
                    → w′ ⊩ B


-- Environments
infix 3 _⊩⋆_
_⊩⋆_ : ∀ {{𝔐 : 𝔎}} → 𝒲 → List Tp → Set
w ⊩⋆ Ξ = All (w ⊩_) Ξ


-- Semantic entailment
infix 3 _⊨_
_⊨_ : Cx → Tp → Set₁
Γ ⊨ A = ∀ {{𝔐 : 𝔎}} {w} → w ⊩⋆ Γ
                         → w ⊩ A


-- Accessibility
mov : ∀ {{𝔐 : 𝔎}} {A w w′} → w′ ≥ w → w ⊩ A
                           → w′ ⊩ A
mov {•}     η v = movᵥ η v
mov {A ⊃ B} η f = λ η′ → f (η ∘ₐ η′)

mov⋆ : ∀ {{𝔐 : 𝔎}} {Ξ w w′} → w′ ≥ w → w ⊩⋆ Ξ
                            → w′ ⊩⋆ Ξ
mov⋆ η γ = mapₐ (λ {A} → mov {A} η) γ


lookup : ∀ {{𝔐 : 𝔎}} {Ξ A w} → w ⊩⋆ Ξ → Ξ ∋ A
                             → w ⊩ A
lookup γ i = lookupₐ γ i


-- Soundness
↓ : ∀ {Γ A} → Γ ⊢ A
            → Γ ⊨ A
↓ (ᵛ i)   = λ γ → lookup γ i
↓ (ƛ 𝒟)   = λ γ η a → ↓ 𝒟 (mov⋆ η γ , a)
↓ (𝒟 $ ℰ) = λ γ → (↓ 𝒟 γ) idₐ (↓ ℰ γ)


--------------------------------------------------------------------------------
--
-- Completeness


-- Universal model
instance
  𝔐ᵤ : 𝔎
  𝔐ᵤ = record
         { 𝒲    = Cx
         ; 𝒱    = _⊢ₙₘ •
         ; _≥_  = _⊇_
         ; idₐ  = idᵣ
         ; _∘ₐ_ = _∘ᵣ_
         ; movᵥ = renₙₘ
         }


-- Soundness and completeness with respect to the universal model
mutual
  ↓ᵤ : ∀ {A Γ} → Γ ⊢ₙₜ A
               → Γ ⊩ A
  ↓ᵤ {•}     𝒟 = ⁿᵗ 𝒟
  ↓ᵤ {A ⊃ B} 𝒟 = λ η a → ↓ᵤ (renₙₜ η 𝒟 $ ↑ᵤ a)

  ↑ᵤ : ∀ {A Γ} → Γ ⊩ A
               → Γ ⊢ₙₘ A
  ↑ᵤ {•}     v = v
  ↑ᵤ {A ⊃ B} f = ƛ (↑ᵤ (f (wk idᵣ) (↓ᵤ {A} (ᵛ zero))))


idₑ : ∀ {Γ} → Γ ⊩⋆ Γ
idₑ {∅}     = ∅
idₑ {Γ , A} = mov⋆ (wk idᵣ) idₑ , ↓ᵤ {A} (ᵛ zero)


-- Completeness
↑ : ∀ {Γ A} → Γ ⊨ A
            → Γ ⊢ₙₘ A
↑ f = ↑ᵤ (f idₑ)


-- Normalisation
nm : ∀ {Γ A} → Γ ⊢ A
             → Γ ⊢ₙₘ A
nm = ↑ ∘ ↓



--------------------------------------------------------------------------------
--
-- Examples


ᵛ0 : ∀ {Γ A} → Γ , A ⊢ A
ᵛ0 = ᵛ zero

ᵛ1 : ∀ {Γ A B} → Γ , A , B ⊢ A
ᵛ1 = ᵛ (suc zero)

ᵛ2 : ∀ {Γ A B C} → Γ , A , B , C ⊢ A
ᵛ2 = ᵛ (suc (suc zero))


ᵃˣI : ∀ {A Γ} → Γ ⊢ A ⊃ A
ᵃˣI = ƛ ᵛ0

ᵃˣK : ∀ {A B Γ} → Γ ⊢ A ⊃ B ⊃ A
ᵃˣK = ƛ (ƛ ᵛ1)

ᵃˣS : ∀ {A B C Γ} → Γ ⊢ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
ᵃˣS = ƛ (ƛ (ƛ ((ᵛ2 $ ᵛ0) $ (ᵛ1 $ ᵛ0))))


--------------------------------------------------------------------------------
--
-- Conversion tests


test∼ : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A → Set
test∼ 𝒟₁ 𝒟₂ = embₙₘ (nm 𝒟₁) ≡ 𝒟₂


-- red⊃ : ∀ {Γ A B} → (𝒟 : Γ , A ⊢ B) (ℰ : Γ ⊢ A)
--                  → ƛ 𝒟 $ ℰ ∼ sub (idₛ , ℰ) 𝒟

test∼red⊃ : test∼ {∅ , •}
                  ((ƛ ᵛ0) $ ᵛ0)
                  ᵛ0
test∼red⊃ = refl


-- exp⊃ : ∀ {Γ A B} → (𝒟 : Γ ⊢ A ⊃ B)
--                  → 𝒟 ∼ ƛ (ren (wk idᵣ) 𝒟 $ ᵛ0)

test∼exp⊃ : test∼ {∅ , • ⊃ •}
                  ᵛ0
                  (ƛ (ren (wk idᵣ) ᵛ0 $ ᵛ0))
test∼exp⊃ = refl


--------------------------------------------------------------------------------
