module Prelude where

open import Agda.Primitive public
  using (_⊔_)
  renaming (lsuc to ↑_)


-- Built-in implication.

id : ∀ {ℓ} {X : Set ℓ} → X → X
id x = x

const : ∀ {ℓ ℓ′} {X : Set ℓ} {Y : Set ℓ′} → X → Y → X
const x y = x

flip : ∀ {ℓ ℓ′ ℓ″} {X : Set ℓ} {Y : Set ℓ′} {Z : Set ℓ″} →
       (X → Y → Z) → Y → X → Z
flip P y x = P x y

ap : ∀ {ℓ ℓ′ ℓ″} {X : Set ℓ} {Y : Set ℓ′} {Z : Set ℓ″} →
     (X → Y → Z) → (X → Y) → X → Z
ap f g x = f x (g x)

infixr 9 _∘_
_∘_ : ∀ {ℓ ℓ′ ℓ″} {X : Set ℓ} {Y : Set ℓ′} {Z : Set ℓ″} →
      (Y → Z) → (X → Y) → X → Z
f ∘ g = λ x → f (g x)

refl→ : ∀ {ℓ} {X : Set ℓ} → X → X
refl→ = id

trans→ : ∀ {ℓ ℓ′ ℓ″} {X : Set ℓ} {Y : Set ℓ′} {Z : Set ℓ″} →
          (X → Y) → (Y → Z) → X → Z
trans→ = flip _∘_


-- Built-in verum.

open import Agda.Builtin.Unit public
  using (⊤)
  renaming (tt to ∙)


-- Falsum.

data ⊥ : Set where

elim⊥ : ∀ {ℓ} {X : Set ℓ} → ⊥ → X
elim⊥ ()


-- Negation.

infix 3 ¬_
¬_ : ∀ {ℓ} → Set ℓ → Set ℓ
¬ X = X → ⊥

_↯_ : ∀ {ℓ ℓ′} {X : Set ℓ} {Y : Set ℓ′} → X → ¬ X → Y
p ↯ ¬p = elim⊥ (¬p p)


-- Built-in equality.

open import Agda.Builtin.Equality public
  using (_≡_ ; refl)

infix 4 _≢_
_≢_ : ∀ {ℓ} {X : Set ℓ} → X → X → Set ℓ
x ≢ x′ = ¬ (x ≡ x′)

trans : ∀ {ℓ} {X : Set ℓ} {x x′ x″ : X} → x ≡ x′ → x′ ≡ x″ → x ≡ x″
trans refl refl = refl

sym : ∀ {ℓ} {X : Set ℓ} {x x′ : X} → x ≡ x′ → x′ ≡ x
sym refl = refl

subst : ∀ {ℓ ℓ′} {X : Set ℓ} → (P : X → Set ℓ′) →
        ∀ {x x′} → x ≡ x′ → P x → P x′
subst P refl p = p

cong : ∀ {ℓ ℓ′} {X : Set ℓ} {Y : Set ℓ′} → (f : X → Y) →
       ∀ {x x′} → x ≡ x′ → f x ≡ f x′
cong f refl = refl

cong₂ : ∀ {ℓ ℓ′ ℓ″} {X : Set ℓ} {Y : Set ℓ′} {Z : Set ℓ″} → (f : X → Y → Z) →
        ∀ {x x′ y y′} → x ≡ x′ → y ≡ y′ → f x y ≡ f x′ y′
cong₂ f refl refl = refl

cong₃ : ∀ {ℓ ℓ′ ℓ″ ℓ‴} {X : Set ℓ} {Y : Set ℓ′} {Z : Set ℓ″} {A : Set ℓ‴} →
        (f : X → Y → Z → A) →
        ∀ {x x′ y y′ z z′} → x ≡ x′ → y ≡ y′ → z ≡ z′ → f x y z ≡ f x′ y′ z′
cong₃ f refl refl refl = refl


-- Equational reasoning with built-in equality.

module ≡-Reasoning {ℓ} {X : Set ℓ} where
  infix 1 begin_
  begin_ : ∀ {x x′ : X} → x ≡ x′ → x ≡ x′
  begin p = p

  infixr 2 _≡⟨⟩_
  _≡⟨⟩_ : ∀ (x {x′} : X) → x ≡ x′ → x ≡ x′
  x ≡⟨⟩ p = p

  infixr 2 _≡⟨_⟩_
  _≡⟨_⟩_ : ∀ (x {x′ x″} : X) → x ≡ x′ → x′ ≡ x″ → x ≡ x″
  x ≡⟨ p ⟩ q = trans p q

  infix 3 _∎
  _∎ : ∀ (x : X) → x ≡ x
  x ∎ = refl

open ≡-Reasoning public


-- Constructive existence.

infixl 5 _,_
record Σ {ℓ ℓ′} (X : Set ℓ) (Y : X → Set ℓ′) : Set (ℓ ⊔ ℓ′) where
  constructor _,_
  field
    π₁ : X
    π₂ : Y π₁

open Σ public


-- Conjunction.

infixr 2 _∧_
_∧_ : ∀ {ℓ ℓ′} → Set ℓ → Set ℓ′ → Set (ℓ ⊔ ℓ′)
X ∧ Y = Σ X (λ x → Y)


-- Disjunction.

infixr 1 _∨_
data _∨_ {ℓ ℓ′} (X : Set ℓ) (Y : Set ℓ′) : Set (ℓ ⊔ ℓ′) where
  ι₁ : X → X ∨ Y
  ι₂ : Y → X ∨ Y

elim∨ : ∀ {ℓ ℓ′ ℓ″} {X : Set ℓ} {Y : Set ℓ′} {Z : Set ℓ″} →
        X ∨ Y → (X → Z) → (Y → Z) → Z
elim∨ (ι₁ x) f g = f x
elim∨ (ι₂ y) f g = g y


-- Equivalence.

infix 3 _↔_
_↔_ : ∀ {ℓ ℓ′} → (X : Set ℓ) (Y : Set ℓ′) → Set (ℓ ⊔ ℓ′)
X ↔ Y = (X → Y) ∧ (Y → X)

infix 3 _↮_
_↮_ : ∀ {ℓ ℓ′} → (X : Set ℓ) (Y : Set ℓ′) → Set (ℓ ⊔ ℓ′)
X ↮ Y = ¬ (X ↔ Y)

refl↔ : ∀ {ℓ} {X : Set ℓ} → X ↔ X
refl↔ = refl→ , refl→

trans↔ : ∀ {ℓ ℓ′ ℓ″} {X : Set ℓ} {Y : Set ℓ′} {Z : Set ℓ″} →
          X ↔ Y → Y ↔ Z → X ↔ Z
trans↔ (P , Q) (P′ , Q′) = trans→ P P′ , trans→ Q′ Q

sym↔ : ∀ {ℓ ℓ′} {X : Set ℓ} {Y : Set ℓ′} → X ↔ Y → Y ↔ X
sym↔ (P , Q) = Q , P

antisym→ : ∀ {ℓ ℓ′} {X : Set ℓ} {Y : Set ℓ′} →
            ((X → Y) ∧ (Y → X)) ≡ (X ↔ Y)
antisym→ = refl


-- Equational reasoning with equivalence.

module ↔-Reasoning where
  infix 1 begin↔_
  begin↔_ : ∀ {ℓ ℓ′} {X : Set ℓ} {Y : Set ℓ′} → X ↔ Y → X ↔ Y
  begin↔ P = P

  infixr 2 _↔⟨⟩_
  _↔⟨⟩_ : ∀ {ℓ ℓ′} → (X : Set ℓ) → {Y : Set ℓ′} → X ↔ Y → X ↔ Y
  X ↔⟨⟩ P = P

  infixr 2 _↔⟨_⟩_
  _↔⟨_⟩_ : ∀ {ℓ ℓ′ ℓ″} → (X : Set ℓ) → {Y : Set ℓ′} {Z : Set ℓ″} →
            X ↔ Y → Y ↔ Z → X ↔ Z
  X ↔⟨ P ⟩ Q = trans↔ P Q

  infix 3 _∎↔
  _∎↔ : ∀ {ℓ} → (X : Set ℓ) → X ↔ X
  X ∎↔ = refl↔

open ↔-Reasoning public


-- Booleans.

open import Agda.Builtin.Bool public
  using (Bool ; false ; true)

elimBool : ∀ {ℓ} {X : Set ℓ} → Bool → X → X → X
elimBool false z s = z
elimBool true  z s = s


-- Conditionals.

data Maybe {ℓ} (X : Set ℓ) : Set ℓ where
  nothing : Maybe X
  just    : X → Maybe X

elimMaybe : ∀ {ℓ ℓ′} {X : Set ℓ} {Y : Set ℓ′} → Maybe X → Y → (X → Y) → Y
elimMaybe nothing  z f = z
elimMaybe (just x) z f = f x


-- Naturals.

open import Agda.Builtin.Nat public
  using (Nat ; zero ; suc)

elimNat : ∀ {ℓ} {X : Set ℓ} → Nat → X → (Nat → X → X) → X
elimNat zero    z f = z
elimNat (suc n) z f = f n (elimNat n z f)


-- Decidability.

data Dec {ℓ} (X : Set ℓ) : Set ℓ where
  yes : X → Dec X
  no  : ¬ X → Dec X

mapDec : ∀ {ℓ ℓ′} {X : Set ℓ} {Y : Set ℓ′} →
         (X → Y) → (Y → X) → Dec X → Dec Y
mapDec f g (yes x) = yes (f x)
mapDec f g (no ¬x) = no (λ y → g y ↯ ¬x)

⌊_⌋Dec : ∀ {ℓ} {X : Set ℓ} → Dec X → Bool
⌊ yes x ⌋Dec = true
⌊ no ¬x ⌋Dec = false


-- Relational composition.

_⨾_ : ∀ {ℓ ℓ′ ℓ″} {X : Set ℓ} → (X → X → Set ℓ′) → (X → X → Set ℓ″) →
      (X → X → Set (ℓ ⊔ ℓ′ ⊔ ℓ″))
_R_ ⨾ _Q_ = λ x x′ → Σ _ (λ y → x R y ∧ y Q x′)
