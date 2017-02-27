module Common where


-- Identity and composition.

id : ∀ {ℓ} {X : Set ℓ} → X → X
id x = x

_∘_ : ∀ {ℓ ℓ′ ℓ″} {X : Set ℓ} {Y : Set ℓ′} {Z : Set ℓ″} →
      (Y → Z) → (X → Y) → X → Z
f ∘ g = λ x → f (g x)


-- Verum.

open import Agda.Builtin.Unit public
  using (⊤)
  renaming (tt to ∙)


-- Falsum.

data ⊥ : Set where

elim⊥ : ∀ {X : Set} → ⊥ → X
elim⊥ ()


-- Negation.

infix 3 ¬_
¬_ : Set → Set
¬ X = X → ⊥


-- Constructive existence.

infixl 5 _,_
record Σ (X : Set) (Y : X → Set) : Set where
  constructor _,_
  field
    π₁ : X
    π₂ : Y π₁

open Σ public


-- Conjunction.

infixr 2 _∧_
_∧_ : Set → Set → Set
X ∧ Y = Σ X (λ _ → Y)


-- Disjunction.

infixr 1 _∨_
data _∨_ (X Y : Set) : Set where
  ι₁ : X → X ∨ Y
  ι₂ : Y → X ∨ Y

elim∨ : ∀ {X Y Z : Set} → X ∨ Y → (X → Z) → (Y → Z) → Z
elim∨ (ι₁ x) f g = f x
elim∨ (ι₂ y) f g = g y


-- Naturals.

open import Agda.Builtin.Nat public
  using (Nat ; zero ; suc)

elimNat : ∀ {X : Set} → Nat → X → (Nat → X → X) → X
elimNat zero    z f = z
elimNat (suc n) z f = f n (elimNat n z f)


-- Composition of relations.

_⨾_ : ∀ {X : Set} → (X → X → Set) → (X → X → Set) → (X → X → Set)
_R_ ⨾ _Q_ = λ x x′ → Σ _ (λ y → x R y ∧ y Q x′)


-- Stacks, or snoc-lists.

data Stack (X : Set) : Set where
  ∅   : Stack X
  _,_ : Stack X → X → Stack X


-- Stack membership, or de Bruijn indices.

module _ {X : Set} where
  infix 3 _∈_
  data _∈_ (A : X) : Stack X → Set where
    top : ∀ {Γ}   → A ∈ Γ , A
    pop : ∀ {Γ B} → A ∈ Γ → A ∈ Γ , B


-- Stack inclusion, or order-preserving embeddings.

module _ {X : Set} where
  infix 3 _⊆_
  data _⊆_ : Stack X → Stack X → Set where
    done : ∀ {Γ}      → ∅ ⊆ Γ
    skip : ∀ {Γ Γ′ A} → Γ ⊆ Γ′ → Γ ⊆ Γ′ , A
    keep : ∀ {Γ Γ′ A} → Γ ⊆ Γ′ → Γ , A ⊆ Γ′ , A

  refl⊆ : ∀ {Γ} → Γ ⊆ Γ
  refl⊆ {∅}     = done
  refl⊆ {Γ , A} = keep refl⊆

  trans⊆ : ∀ {Γ Γ′ Γ″} → Γ ⊆ Γ′ → Γ′ ⊆ Γ″ → Γ ⊆ Γ″
  trans⊆ done     η′        = done
  trans⊆ η        (skip η′) = skip (trans⊆ η η′)
  trans⊆ (skip η) (keep η′) = skip (trans⊆ η η′)
  trans⊆ (keep η) (keep η′) = keep (trans⊆ η η′)

  weak⊆ : ∀ {Γ A} → Γ ⊆ Γ , A
  weak⊆ = skip refl⊆


-- Monotonicity of stack membership with respect to stack inclusion.

module _ {X : Set} where
  mono∈ : ∀ {Γ Γ′ : Stack X} {A} → Γ ⊆ Γ′ → A ∈ Γ → A ∈ Γ′
  mono∈ done     ()
  mono∈ (skip η) i       = pop (mono∈ η i)
  mono∈ (keep η) top     = top
  mono∈ (keep η) (pop i) = pop (mono∈ η i)


-- Pairs of stacks.

infixl 4 _⁏_
record Stack² (X Y : Set) : Set where
  constructor _⁏_
  field
    π₁ : Stack X
    π₂ : Stack Y

open Stack² public


-- Stack pair inclusion.

module _ {X Y : Set} where
  infix 3 _⊆²_
  _⊆²_ : Stack² X Y → Stack² X Y → Set
  Γ ⁏ Δ ⊆² Γ′ ⁏ Δ′ = Γ ⊆ Γ′ ∧ Δ ⊆ Δ′

  refl⊆² : ∀ {Γ Δ} → Γ ⁏ Δ ⊆² Γ ⁏ Δ
  refl⊆² = refl⊆ , refl⊆

  trans⊆² : ∀ {Γ Γ′ Γ″ Δ Δ′ Δ″} → Γ ⁏ Δ ⊆² Γ′ ⁏ Δ′ → Γ′ ⁏ Δ′ ⊆² Γ″ ⁏ Δ″ → Γ ⁏ Δ ⊆² Γ″ ⁏ Δ″
  trans⊆² (η , ρ) (η′ , ρ′) = trans⊆ η η′ , trans⊆ ρ ρ′
