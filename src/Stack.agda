module Stack where

open import Prelude public


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

  ⌊_⌋∈ : ∀ {Γ A} → A ∈ Γ → Nat
  ⌊ top ⌋∈   = zero
  ⌊ pop i ⌋∈ = suc ⌊ i ⌋∈

  i₀ : ∀ {Γ A} → A ∈ Γ , A
  i₀ = top

  i₁ : ∀ {Γ A B} → A ∈ Γ , A , B
  i₁ = pop i₀

  i₂ : ∀ {Γ A B C} → A ∈ Γ , A , B , C
  i₂ = pop i₁


-- Stack inclusion, or order-preserving embeddings.

module _ {X : Set} where
  infix 3 _⊆_
  data _⊆_ : Stack X → Stack X → Set where
    bot  : ∀ {Γ}      → ∅ ⊆ Γ
    skip : ∀ {Γ Γ′ A} → Γ ⊆ Γ′ → Γ ⊆ Γ′ , A
    keep : ∀ {Γ Γ′ A} → Γ ⊆ Γ′ → Γ , A ⊆ Γ′ , A

  refl⊆ : ∀ {Γ} → Γ ⊆ Γ
  refl⊆ {∅}     = bot
  refl⊆ {Γ , A} = keep refl⊆

  trans⊆ : ∀ {Γ Γ′ Γ″} → Γ ⊆ Γ′ → Γ′ ⊆ Γ″ → Γ ⊆ Γ″
  trans⊆ bot      η′        = bot
  trans⊆ η        (skip η′) = skip (trans⊆ η η′)
  trans⊆ (skip η) (keep η′) = skip (trans⊆ η η′)
  trans⊆ (keep η) (keep η′) = keep (trans⊆ η η′)

  weak⊆ : ∀ {Γ A} → Γ ⊆ Γ , A
  weak⊆ = skip refl⊆


-- Monotonicity of stack membership with respect to stack inclusion.

module _ {X : Set} where
  mono∈ : ∀ {Γ Γ′ : Stack X} {A} → Γ ⊆ Γ′ → A ∈ Γ → A ∈ Γ′
  mono∈ bot      ()
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
