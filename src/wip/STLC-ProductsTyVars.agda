module STLC-ProductsTyVars where

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
  𝔗   : Tp

instance
  typeIsString : IsString Tp
  typeIsString =
    record
      { Constraint = λ s → ⊤
      ; fromString = λ s → ᵗᵛ (tvar s)
      }


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

    _,_ : ∀ {A B Γ} → (𝒟 : Γ ⊢ A) (ℰ : Γ ⊢ B)
                    → Γ ⊢ A ∧ B

    π₁  : ∀ {A B Γ} → (𝒟 : Γ ⊢ A ∧ B)
                    → Γ ⊢ A

    π₂  : ∀ {A B Γ} → (𝒟 : Γ ⊢ A ∧ B)
                    → Γ ⊢ B

    tt  : ∀ {Γ} → Γ ⊢ 𝔗


-- Normal and neutral forms
mutual
  infix 3 _⊢ₙₘ_
  data _⊢ₙₘ_ : Cx → Tp → Set
    where
      ƛ   : ∀ {A B Γ} → (𝒟 : Γ , A ⊢ₙₘ B)
                      → Γ ⊢ₙₘ A ⊃ B

      _,_ : ∀ {A B Γ} → (𝒟 : Γ ⊢ₙₘ A) (ℰ : Γ ⊢ₙₘ B)
                      → Γ ⊢ₙₘ A ∧ B

      tt  : ∀ {Γ} → Γ ⊢ₙₘ 𝔗

      ⁿᵗ  : ∀ {x Γ} → (𝒟 : Γ ⊢ₙₜ ᵗᵛ x)
                    → Γ ⊢ₙₘ ᵗᵛ x

  infix 3 _⊢ₙₜ_
  data _⊢ₙₜ_ : Cx → Tp → Set
    where
      ᵛ   : ∀ {A Γ} → (i : Γ ∋ A)
                    → Γ ⊢ₙₜ A

      _$_ : ∀ {A B Γ} → (𝒟 : Γ ⊢ₙₜ A ⊃ B) (ℰ : Γ ⊢ₙₘ A)
                      → Γ ⊢ₙₜ B

      π₁  : ∀ {A B Γ} → (𝒟 : Γ ⊢ₙₜ A ∧ B)
                      → Γ ⊢ₙₜ A

      π₂  : ∀ {A B Γ} → (𝒟 : Γ ⊢ₙₜ A ∧ B)
                      → Γ ⊢ₙₜ B


mutual
  embₙₘ : ∀ {Γ A} → Γ ⊢ₙₘ A → Γ ⊢ A
  embₙₘ (ƛ 𝒟)   = ƛ (embₙₘ 𝒟)
  embₙₘ (𝒟 , ℰ) = embₙₘ 𝒟 , embₙₘ ℰ
  embₙₘ tt      = tt
  embₙₘ (ⁿᵗ 𝒟)  = embₙₜ 𝒟

  embₙₜ : ∀ {Γ A} → Γ ⊢ₙₜ A → Γ ⊢ A
  embₙₜ (ᵛ i)   = ᵛ i
  embₙₜ (𝒟 $ ℰ) = embₙₜ 𝒟 $ embₙₘ ℰ
  embₙₜ (π₁ 𝒟)  = π₁ (embₙₜ 𝒟)
  embₙₜ (π₂ 𝒟)  = π₂ (embₙₜ 𝒟)


--------------------------------------------------------------------------------
--
-- Renaming


ren : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢ A
                 → Γ′ ⊢ A
ren η (ᵛ i)   = ᵛ (lookupᵣ η i)
ren η (ƛ 𝒟)   = ƛ (ren (lift η) 𝒟)
ren η (𝒟 $ ℰ) = ren η 𝒟 $ ren η ℰ
ren η (𝒟 , ℰ) = ren η 𝒟 , ren η ℰ
ren η (π₁ 𝒟)  = π₁ (ren η 𝒟)
ren η (π₂ 𝒟)  = π₂ (ren η 𝒟)
ren η tt      = tt


mutual
  renₙₘ : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢ₙₘ A
                     → Γ′ ⊢ₙₘ A
  renₙₘ η (ƛ 𝒟)   = ƛ (renₙₘ (lift η) 𝒟)
  renₙₘ η (𝒟 , ℰ) = renₙₘ η 𝒟 , renₙₘ η ℰ
  renₙₘ η tt      = tt
  renₙₘ η (ⁿᵗ 𝒟)  = ⁿᵗ (renₙₜ η 𝒟)

  renₙₜ : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢ₙₜ A
                     → Γ′ ⊢ₙₜ A
  renₙₜ η (ᵛ i)   = ᵛ (lookupᵣ η i)
  renₙₜ η (𝒟 $ ℰ) = renₙₜ η 𝒟 $ renₙₘ η ℰ
  renₙₜ η (π₁ 𝒟)  = π₁ (renₙₜ η 𝒟)
  renₙₜ η (π₂ 𝒟)  = π₂ (renₙₜ η 𝒟)


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
sub η (𝒟 , ℰ) = sub η 𝒟 , sub η ℰ
sub η (π₁ 𝒟)  = π₁ (sub η 𝒟)
sub η (π₂ 𝒟)  = π₂ (sub η 𝒟)
sub η tt      = tt
-}


--------------------------------------------------------------------------------
--
-- Semantics


-- Kripke models
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

open 𝔎 {{…}} public


-- Values
infix 3 _⊩_
_⊩_ : ∀ {{𝔐 : 𝔎}} → 𝒲 → Tp → Set

w ⊩ ᵗᵛ x  = w 𝒱 x

w ⊩ A ⊃ B = ∀ {w′} → (η : w′ ≥ w) (k : w′ ⊩ A)
                    → w′ ⊩ B

w ⊩ A ∧ B = w ⊩ A × w ⊩ B

w ⊩ 𝔗     = ⊤


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
mov {ᵗᵛ x}  η v = movᵥ η v
mov {A ⊃ B} η f = λ η′ → f (η ∘ₐ η′)
mov {A ∧ B} η p = mov {A} η (proj₁ p) , mov {B} η (proj₂ p)
mov {𝔗}     η t = tt

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
↓ (𝒟 $ ℰ) = λ γ → ↓ 𝒟 γ idₐ (↓ ℰ γ)
↓ (𝒟 , ℰ) = λ γ → ↓ 𝒟 γ , ↓ ℰ γ
↓ (π₁ 𝒟)  = λ γ → proj₁ (↓ 𝒟 γ)
↓ (π₂ 𝒟)  = λ γ → proj₂ (↓ 𝒟 γ)
↓ tt      = λ γ → tt


--------------------------------------------------------------------------------
--
-- Completeness


-- Universal model
instance
  𝔐ᵤ : 𝔎
  𝔐ᵤ = record
         { 𝒲    = Cx
         ; _𝒱_  = _𝒱ᵤ_
         ; _≥_  = _⊇_
         ; idₐ  = idᵣ
         ; _∘ₐ_ = _∘ᵣ_
         ; movᵥ = renₙₘ
         }
    where
      infix 3 _𝒱ᵤ_
      _𝒱ᵤ_ : Cx → TVar → Set
      Γ 𝒱ᵤ x = Γ ⊢ₙₘ ᵗᵛ x


-- Soundness and completeness with respect to the universal model
mutual
  ↓ᵤ : ∀ {A Γ} → Γ ⊢ₙₜ A
               → Γ ⊩ A
  ↓ᵤ {ᵗᵛ x}  𝒟 = ⁿᵗ 𝒟
  ↓ᵤ {A ⊃ B} 𝒟 = λ η k → ↓ᵤ (renₙₜ η 𝒟 $ ↑ᵤ k)
  ↓ᵤ {A ∧ B} 𝒟 = ↓ᵤ (π₁ 𝒟) , ↓ᵤ (π₂ 𝒟)
  ↓ᵤ {𝔗}     𝒟 = tt

  ↑ᵤ : ∀ {A Γ} → Γ ⊩ A
               → Γ ⊢ₙₘ A
  ↑ᵤ {ᵗᵛ x}  v = v
  ↑ᵤ {A ⊃ B} f = ƛ (↑ᵤ (f (wk idᵣ) (↓ᵤ {A} (ᵛ zero))))
  ↑ᵤ {A ∧ B} p = ↑ᵤ (proj₁ p) , ↑ᵤ (proj₂ p)
  ↑ᵤ {𝔗}     t = tt


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

test∼red⊃ : test∼ {∅ , "A"}
                  ((ƛ ᵛ0) $ ᵛ0)
                  ᵛ0
test∼red⊃ = refl


-- red∧₁ : ∀ {Γ A B} → (𝒟 : Γ ⊢ A) (ℰ : Γ ⊢ B)
--                   → π₁ (𝒟 , ℰ) ∼ 𝒟

test∼red∧₁ : test∼ {∅ , "A" , "B"}
                   (π₁ (ᵛ1 , ᵛ0))
                   ᵛ1
test∼red∧₁ = refl


-- red∧₂ : ∀ {Γ A B} → (𝒟 : Γ ⊢ A) (ℰ : Γ ⊢ B)
--                   → π₂ (𝒟 , ℰ) ∼ ℰ

test∼red∧₂ : test∼ {∅ , "A" , "B"}
                   (π₂ (ᵛ1 , ᵛ0))
                   ᵛ0
test∼red∧₂ = refl


-- exp⊃ : ∀ {Γ A B} → (𝒟 : Γ ⊢ A ⊃ B)
--                  → 𝒟 ∼ ƛ (ren (wk idᵣ) 𝒟 $ ᵛ0)

test∼exp⊃ : test∼ {∅ , "A" ⊃ "B"}
                  ᵛ0
                  (ƛ (ren (wk idᵣ) ᵛ0 $ ᵛ0))
test∼exp⊃ = refl


-- exp∧ : ∀ {Γ A B} → (𝒟 : Γ ⊢ A ∧ B)
--                  → 𝒟 ∼ π₁ 𝒟 , π₂ 𝒟

test∼exp∧ : test∼ {∅ , "A" ∧ "B"}
                  ᵛ0
                  (π₁ ᵛ0 , π₂ ᵛ0)
test∼exp∧ = refl


-- exp𝔗 : ∀ {Γ} → (𝒟 : Γ ⊢ 𝔗)
--              → 𝒟 ∼ tt

test∼exp𝔗 : test∼ {∅ , 𝔗}
                  ᵛ0
                  tt
test∼exp𝔗 = refl


--------------------------------------------------------------------------------
