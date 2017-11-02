{-# OPTIONS --rewriting #-}

module Prelude where


--------------------------------------------------------------------------------
--
-- Prelude


open import Agda.Primitive public
  using (_⊔_ ; lsuc)

open import Agda.Builtin.Unit public
  using (⊤ ; tt)


id : ∀ {ℓ} → {X : Set ℓ} → X → X
id x = x

_∘_ : ∀ {ℓ ℓ′ ℓ″} → {X : Set ℓ} {P : X → Set ℓ′} {Q : ∀ {x} → P x → Set ℓ″}
                  → (g : ∀ {x} → (y : P x) → Q y) (f : (x : X) → P x) (x : X)
                  → Q (f x)
(g ∘ f) x = g (f x)


data ⊥ : Set
  where

elim⊥ : ∀ {ℓ} → {X : Set ℓ} → ⊥ → X
elim⊥ ()

¬_ : ∀ {ℓ} → Set ℓ → Set ℓ
¬ X = X → ⊥

_↯_ : ∀ {ℓ ℓ′} → {X : Set ℓ} {Y : Set ℓ′} → X → ¬ X → Y
p ↯ ¬p = elim⊥ (¬p p)


infixl 6 _,_
record Σ {ℓ ℓ′} (X : Set ℓ) (P : X → Set ℓ′) : Set (ℓ ⊔ ℓ′)
  where
    constructor _,_
    field
      proj₁ : X
      proj₂ : P proj₁
open Σ public

infixl 5 _⁏_
pattern _⁏_ x y = x , y

infixl 2 _×_
_×_ : ∀ {ℓ ℓ′} → Set ℓ → Set ℓ′ → Set (ℓ ⊔ ℓ′)
X × Y = Σ X (λ x → Y)

forΣ : ∀ {ℓ ℓ′ ℓ″ ℓ‴} → {X : Set ℓ} {Y : Set ℓ′} {P : X → Set ℓ″} {Q : Y → Set ℓ‴}
                      → Σ X P → (f : X → Y) (g : ∀ {x} → P x → Q (f x))
                      → Σ Y Q
forΣ (x , y) f g = f x , g y

mapΣ : ∀ {ℓ ℓ′ ℓ″ ℓ‴} → {X : Set ℓ} {Y : Set ℓ′} {P : X → Set ℓ″} {Q : Y → Set ℓ‴}
                      → (f : X → Y) (g : ∀ {x} → P x → Q (f x)) → Σ X P
                      → Σ Y Q
mapΣ f g p = forΣ p f g


infixl 1 _⊎_
data _⊎_ {ℓ ℓ′} (X : Set ℓ) (Y : Set ℓ′) : Set (ℓ ⊔ ℓ′)
  where
    inj₁ : (x : X) → X ⊎ Y
    inj₂ : (y : Y) → X ⊎ Y

elim⊎ : ∀ {ℓ ℓ′ ℓ″} → {X : Set ℓ} {Y : Set ℓ′} {Z : Set ℓ″}
                    → X ⊎ Y → (X → Z) → (Y → Z)
                    → Z
elim⊎ (inj₁ x) f g = f x
elim⊎ (inj₂ y) f g = g y

for⊎ : ∀ {ℓ ℓ′ ℓ″ ℓ‴} → {X : Set ℓ} {Y : Set ℓ′} {U : Set ℓ″} {V : Set ℓ‴}
                      → X ⊎ Y → (X → U) → (Y → V)
                      → U ⊎ V
for⊎ s f g = elim⊎ s (inj₁ ∘ f) (inj₂ ∘ g)

map⊎ : ∀ {ℓ ℓ′ ℓ″ ℓ‴} → {X : Set ℓ} {Y : Set ℓ′} {U : Set ℓ″} {V : Set ℓ‴}
                      → (X → U) → (Y → V) → X ⊎ Y
                      → U ⊎ V
map⊎ f g s = for⊎ s f g


data Dec {ℓ} (X : Set ℓ) : Set ℓ
  where
    yes : X → Dec X
    no  : ¬ X → Dec X

forDec : ∀ {ℓ ℓ′} → {X : Set ℓ} {Y : Set ℓ′}
                  → Dec X → (X → Y) → (Y → X)
                  → Dec Y
forDec (yes x) f f⁻¹ = yes (f x)
forDec (no ¬x) f f⁻¹ = no (λ y → f⁻¹ y ↯ ¬x)

mapDec : ∀ {ℓ ℓ′} → {X : Set ℓ} {Y : Set ℓ′}
                  → (X → Y) → (Y → X) → Dec X
                  → Dec Y
mapDec f f⁻¹ d = forDec d f f⁻¹


--------------------------------------------------------------------------------
--
-- Propositional equality


open import Agda.Builtin.Equality public
  using (_≡_ ; refl)

{-# BUILTIN REWRITE _≡_ #-}


infix 4 _≢_
_≢_ : ∀ {ℓ} → {X : Set ℓ} → X → X → Set ℓ
x ≢ x′ = ¬ (x ≡ x′)


_⁻¹≡ : ∀ {ℓ} → {X : Set ℓ} {x₁ x₂ : X}
             → x₁ ≡ x₂ → x₂ ≡ x₁
refl ⁻¹≡ = refl

_⦙≡_ : ∀ {ℓ} → {X : Set ℓ} {x₁ x₂ x₃ : X}
             → x₁ ≡ x₂ → x₂ ≡ x₃ → x₁ ≡ x₃
refl ⦙≡ refl = refl


record PER {ℓ}
           (X : Set ℓ)
           (_≈_ : X → X → Set ℓ)
         : Set ℓ where
  infix  9 _⁻¹
  infixr 4 _⦙_
  field
    _⁻¹ : ∀ {x₁ x₂} → x₁ ≈ x₂
                    → x₂ ≈ x₁

    _⦙_ : ∀ {x₁ x₂ x₃} → x₁ ≈ x₂ → x₂ ≈ x₃
                       → x₁ ≈ x₃

open PER {{...}} public

instance
  per≡ : ∀ {ℓ} {X : Set ℓ} → PER X _≡_
  per≡ =
    record
      { _⁻¹ = _⁻¹≡
      ; _⦙_ = _⦙≡_
      }


infixl 9 _&_
_&_ : ∀ {ℓ ℓ′} → {X : Set ℓ} {Y : Set ℓ′} {x₁ x₂ : X}
               → (f : X → Y) → x₁ ≡ x₂
               → f x₁ ≡ f x₂
f & refl = refl

infixl 8 _⊗_
_⊗_ : ∀ {ℓ ℓ′} → {X : Set ℓ} {Y : Set ℓ′} {f₁ f₂ : X → Y} {x₁ x₂ : X}
               → f₁ ≡ f₂ → x₁ ≡ x₂
               → f₁ x₁ ≡ f₂ x₂
refl ⊗ refl = refl

coe : ∀ {ℓ} → {X Y : Set ℓ}
            → X ≡ Y → X → Y
coe refl x = x


case_of_ : ∀ {ℓ ℓ′} → {X : Set ℓ} {Y : Set ℓ′}
                    → X → (X → Y) → Y
case x of f = f x


--------------------------------------------------------------------------------
--
-- Booleans


open import Agda.Builtin.Bool public
  using (Bool ; false ; true)


data True : Bool → Set
  where
    instance
      yes : True true


--------------------------------------------------------------------------------
--
-- Naturals


open import Agda.Builtin.Nat public
  using (Nat ; zero ; suc)

open import Agda.Builtin.FromNat public
  using (Number ; fromNat)


injsuc : ∀ {n₁ n₂} → Nat.suc n₁ ≡ suc n₂ → n₁ ≡ n₂
injsuc refl = refl


-- TODO: Rename this
wat : ∀ {n₁ n₂} → (p : n₁ ≡ n₂)
                → injsuc (suc & p) ≡ p
wat refl = refl
{-# REWRITE wat #-}


-- TODO: Rename this
foo : ∀ {n₁ n₂} → (p : n₁ ≡ n₂)
                → Nat.suc n₁ ≡ suc n₂
foo p = suc & p


instance
  natIsNumber : Number Nat
  natIsNumber =
    record
      { Constraint = λ n → ⊤
      ; fromNat    = λ n → n
      }

_⩼_ : Nat → Nat → Bool
zero  ⩼ k     = false
suc n ⩼ zero  = true
suc n ⩼ suc k = n ⩼ k


--------------------------------------------------------------------------------
--
-- Finite naturals


data Fin : Nat → Set
  where
    zero : ∀ {n} → Fin (suc n)

    suc  : ∀ {n} → Fin n
                 → Fin (suc n)


Nat→Fin : ∀ {n} → (k : Nat) {{_ : True (n ⩼ k)}}
                 → Fin n
Nat→Fin {n = zero}  k       {{()}}
Nat→Fin {n = suc n} zero    {{yes}} = zero
Nat→Fin {n = suc n} (suc k) {{p}}   = suc (Nat→Fin k {{p}})

instance
  finIsNumber : ∀ {n} → Number (Fin n)
  finIsNumber {n} =
    record
      { Constraint = λ k → True (n ⩼ k)
      ; fromNat    = Nat→Fin
      }


--------------------------------------------------------------------------------
--
-- Strings


open import Agda.Builtin.String public
  using (String ; primStringAppend ; primStringEquality)

open import Agda.Builtin.FromString public
  using (IsString ; fromString)

open import Agda.Builtin.TrustMe


infixl 5 _⧺_
_⧺_ : String → String → String
_⧺_ = primStringAppend

_≟ₛ_ : (s s′ : String) → Dec (s ≡ s′)
s ≟ₛ s′ with primStringEquality s s′
...    | true  = yes primTrustMe
...    | false = no s≢s′
  where
    postulate
      s≢s′ : s ≢ s′

instance
  stringIsString : IsString String
  stringIsString =
    record
      { Constraint = λ s → ⊤
      ; fromString = λ s → s
      }


--------------------------------------------------------------------------------
--
-- Lists


data List {ℓ} (X : Set ℓ) : Set ℓ
  where
    ∅   : List X
    _,_ : (Γ : List X) (A : X) → List X

{-# COMPILE GHC List = data List ([] | (:)) #-}


length : ∀ {ℓ} → {X : Set ℓ}
               → List X
               → Nat
length ∅       = zero
length (Γ , A) = suc (length Γ)

map : ∀ {ℓ ℓ′} → {X : Set ℓ} {Y : Set ℓ′}
               → (X → Y) → List X
               → List Y
map f ∅       = ∅
map f (Γ , A) = map f Γ , f A

reduce : ∀ {ℓ ℓ′} → {X : Set ℓ} {Z : Set ℓ′}
                  → (Z → X → Z) → Z → List X
                  → Z
reduce f z ∅       = z
reduce f z (Γ , A) = f (reduce f z Γ) A

lookup : ∀ {ℓ} → {X : Set ℓ}
               → (Γ : List X) (i : Nat) {{_ : True (length Γ ⩼ i)}}
               → X
lookup ∅       i       {{()}}
lookup (Γ , A) zero    {{yes}} = A
lookup (Γ , B) (suc i) {{p}}   = lookup Γ i

zip : ∀ {ℓ ℓ′} → {X : Set ℓ} {Y : Set ℓ′}
               → (Γ₁ : List X) (Γ₂ : List Y) {{_ : length Γ₁ ≡ length Γ₂}}
               → List (X × Y)
zip ∅         ∅         {{refl}} = ∅
zip ∅         (Γ₂ , A₂) {{()}}
zip (Γ₁ , A₁) ∅         {{()}}
zip (Γ₁ , A₁) (Γ₂ , A₂) {{x}}    = zip Γ₁ Γ₂ {{injsuc x}} , (A₁ , A₂)


-- TODO: Rename this
lem₁ : ∀ {ℓ ℓ′} → {X : Set ℓ} {Y : Set ℓ′}
                → (Γ₁ : List X) (Γ₂ : List Y) {{p : length Γ₁ ≡ length Γ₂}}
                → map proj₁ (zip Γ₁ Γ₂) ≡ Γ₁
lem₁ ∅        ∅        {{refl}} = refl
lem₁ ∅        (Γ₂ , B) {{()}}
lem₁ (Γ₁ , A) ∅        {{()}}
lem₁ (Γ₁ , A) (Γ₂ , B) {{p}}    = (_, A) & lem₁ Γ₁ Γ₂ {{injsuc p}}

-- TODO: Rename this
lem₂ : ∀ {ℓ ℓ′} → {X : Set ℓ} {Y : Set ℓ′}
                → (Γ₁ : List X) (Γ₂ : List Y) {{p : length Γ₁ ≡ length Γ₂}}
                → map proj₂ (zip Γ₁ Γ₂) ≡ Γ₂
lem₂ ∅        ∅        {{refl}} = refl
lem₂ ∅        (Γ₂ , B) {{()}}
lem₂ (Γ₁ , A) ∅        {{()}}
lem₂ (Γ₁ , A) (Γ₂ , B) {{p}}    = (_, B) & lem₂ Γ₁ Γ₂ {{injsuc p}}
{-# REWRITE lem₂ #-}

-- TODO: Rename this
lem₃ : ∀ {ℓ ℓ′} → {X : Set ℓ} {Y : Set ℓ′}
                → (Γ : List (X × Y))
                → length (map proj₁ Γ) ≡ length (map proj₂ Γ)
lem₃ ∅        = refl
lem₃ (Γ , AB) = suc & lem₃ Γ
{-# REWRITE lem₃ #-}

-- TODO: Rename this
lem₄ : ∀ {ℓ ℓ′} → {X : Set ℓ} {Y : Set ℓ′}
                → (Γ : List (X × Y))
                → zip (map proj₁ Γ) (map proj₂ Γ) ≡ Γ
lem₄ ∅        = refl
lem₄ (Γ , AB) = (_, AB) & lem₄ Γ


--------------------------------------------------------------------------------
--
-- Variables


infix 4 _∋_
data _∋_ {ℓ} {X : Set ℓ} : List X → X → Set ℓ
  where
    zero : ∀ {Γ A} → Γ , A ∋ A

    suc  : ∀ {Γ A B} → (i : Γ ∋ A)
                     → Γ , B ∋ A


Nat→∋ : ∀ {ℓ} → {X : Set ℓ} {Γ : List X}
               → (i : Nat) {{_ : True (length Γ ⩼ i)}}
               → Γ ∋ lookup Γ i
Nat→∋ {Γ = ∅}     i       {{()}}
Nat→∋ {Γ = Γ , A} zero    {{yes}} = zero
Nat→∋ {Γ = Γ , B} (suc i) {{p}}   = suc (Nat→∋ i)

instance
  ∋IsNumber : ∀ {ℓ} → {X : Set ℓ} {Γ : List X} {A : X}
                    → Number (Γ ∋ A)
  ∋IsNumber {Γ = Γ} {A} =
    record
      { Constraint = λ i → Σ (True (length Γ ⩼ i))
                              (λ p → lookup Γ i {{p}} ≡ A)
      ; fromNat    = λ { i {{p , refl}} → Nat→∋ i }
      }


data All {ℓ ℓ′} {X : Set ℓ} (P : X → Set ℓ′) : List X → Set (ℓ ⊔ ℓ′)
  where
    ∅   : All P ∅
    _,_ : ∀ {Γ A} → (ψ : All P Γ) (p : P A)
                  → All P (Γ , A)


mapAll : ∀ {ℓ ℓ′ ℓ″} → {X : Set ℓ} {P : X → Set ℓ′} {Q : X → Set ℓ″} {Γ : List X}
                     → (∀ {x} → P x → Q x) → All P Γ
                     → All Q Γ
mapAll f ∅       = ∅
mapAll f (ψ , p) = mapAll f ψ , f p

mmapAll : ∀ {ℓ ℓ′ ℓ″ ℓ‴} → {X : Set ℓ} {Y : Set ℓ′} {P : X → Set ℓ″} {Q : Y → Set ℓ‴} {Γ : List X}
                         → (f : X → Y) → (∀ {x} → P x → Q (f x)) → All P Γ
                         → All Q (map f Γ)
mmapAll f g ∅       = ∅
mmapAll f g (ψ , p) = mmapAll f g ψ , g p


reduceAll : ∀ {ℓ ℓ′ ℓ″} → {X : Set ℓ} {P : X → Set ℓ′} {Z : Set ℓ″} {Γ : List X}
                        → (∀ {x} → Z → P x → Z) → Z → All P Γ
                        → Z
reduceAll f z ∅       = z
reduceAll f z (ψ , p) = f (reduceAll f z ψ) p

lookupAll : ∀ {ℓ ℓ′} → {X : Set ℓ} {P : X → Set ℓ′} {Γ : List X} {A : X}
                     → All P Γ → Γ ∋ A
                     → P A
lookupAll (ψ , p) zero    = p
lookupAll (ψ , q) (suc i) = lookupAll ψ i


proj∋₁ : ∀ {ℓ ℓ′} → {X : Set ℓ} {Y : Set ℓ′} {Γ : List (X × Y)} {A : X} {B : Y}
                  → Γ ∋ (A , B)
                  → map proj₁ Γ ∋ A
proj∋₁ zero    = zero
proj∋₁ (suc i) = suc (proj∋₁ i)

proj∋₂ : ∀ {ℓ ℓ′} → {X : Set ℓ} {Y : Set ℓ′} {Γ : List (X × Y)} {A : X} {B : Y}
                  → Γ ∋ (A , B)
                  → map proj₂ Γ ∋ B
proj∋₂ zero    = zero
proj∋₂ (suc i) = suc (proj∋₂ i)


unproj∋₁ : ∀ {ℓ ℓ′} → {X : Set ℓ} {Y : Set ℓ′} {Γ : List (X × Y)} {A : X}
                    → map proj₁ Γ ∋ A
                    → Σ Y (λ B → Γ ∋ (A , B))
unproj∋₁ {Γ = ∅}           ()
unproj∋₁ {Γ = Γ , (A , B)} zero    = B , zero
unproj∋₁ {Γ = Γ , (A , B)} (suc i) = mapΣ id suc (unproj∋₁ i)

unproj∋₂ : ∀ {ℓ ℓ′} → {X : Set ℓ} {Y : Set ℓ′} {Γ : List (X × Y)} {B : Y}
                    → map proj₂ Γ ∋ B
                    → Σ X (λ A → Γ ∋ (A , B))
unproj∋₂ {Γ = ∅}           ()
unproj∋₂ {Γ = Γ , (A , B)} zero    = A , zero
unproj∋₂ {Γ = Γ , (A , B)} (suc i) = mapΣ id suc (unproj∋₂ i)


--------------------------------------------------------------------------------
--
-- Order-preserving embeddings


infix 4 _⊇_
data _⊇_ {ℓ} {X : Set ℓ} : List X → List X → Set ℓ
  where
    doneᵣ : ∅ ⊇ ∅

    wkᵣ   : ∀ {Γ Γ′ A} → (η : Γ′ ⊇ Γ)
                       → Γ′ , A ⊇ Γ

    liftᵣ : ∀ {Γ Γ′ A} → (η : Γ′ ⊇ Γ)
                       → Γ′ , A ⊇ Γ , A


infᵣ : ∀ {ℓ} → {X : Set ℓ} {Γ : List X}
             → Γ ⊇ ∅
infᵣ {Γ = ∅}     = doneᵣ
infᵣ {Γ = Γ , A} = wkᵣ infᵣ

idᵣ : ∀ {ℓ} → {X : Set ℓ} {Γ : List X}
            → Γ ⊇ Γ
idᵣ {Γ = ∅}     = doneᵣ
idᵣ {Γ = Γ , A} = liftᵣ idᵣ

_∘ᵣ_ : ∀ {ℓ} → {X : Set ℓ} {Γ Γ′ Γ″ : List X}
             → Γ′ ⊇ Γ → Γ″ ⊇ Γ′
             → Γ″ ⊇ Γ
η       ∘ᵣ doneᵣ    = η
η       ∘ᵣ wkᵣ η′   = wkᵣ (η ∘ᵣ η′)
wkᵣ η   ∘ᵣ liftᵣ η′ = wkᵣ (η ∘ᵣ η′)
liftᵣ η ∘ᵣ liftᵣ η′ = liftᵣ (η ∘ᵣ η′)

lookupᵣ : ∀ {ℓ} → {X : Set ℓ} {Γ Γ′ : List X} {A : X}
                → Γ′ ⊇ Γ → Γ ∋ A
                → Γ′ ∋ A
lookupᵣ doneᵣ     i       = i
lookupᵣ (wkᵣ η)   i       = suc (lookupᵣ η i)
lookupᵣ (liftᵣ η) zero    = zero
lookupᵣ (liftᵣ η) (suc i) = suc (lookupᵣ η i)


--------------------------------------------------------------------------------
--
-- Dual lists


List² : ∀ {ℓ ℓ′} → Set ℓ → Set ℓ′ → Set (ℓ ⊔ ℓ′)
List² X Y = List X × List Y


infix 3 _⊇²_
_⊇²_ : ∀ {ℓ ℓ′} → {X : Set ℓ} {Y : Set ℓ′} → List² X Y → List² X Y → Set (ℓ ⊔ ℓ′)
Δ′ ⁏ Γ′ ⊇² Δ ⁏ Γ = Δ′ ⊇ Δ × Γ′ ⊇ Γ


mwkᵣ : ∀ {ℓ ℓ′} → {X : Set ℓ} {Y : Set ℓ′} {Δ Δ′ : List X} {Γ Γ′ : List Y} {A : X}
                → Δ′ ⁏ Γ′ ⊇² Δ ⁏ Γ
                → Δ′ , A ⁏ Γ′ ⊇² Δ ⁏ Γ
mwkᵣ η = wkᵣ (proj₁ η) , proj₂ η

rwkᵣ : ∀ {ℓ ℓ′} → {X : Set ℓ} {Y : Set ℓ′} {Δ Δ′ : List X} {Γ Γ′ : List Y} {A : Y}
                → Δ′ ⁏ Γ′ ⊇² Δ ⁏ Γ
                → Δ′ ⁏ Γ′ , A ⊇² Δ ⁏ Γ
rwkᵣ η = proj₁ η , wkᵣ (proj₂ η)


idᵣ² : ∀ {ℓ ℓ′} → {X : Set ℓ} {Y : Set ℓ′} {Δ : List X} {Γ : List Y}
                → Δ ⁏ Γ ⊇² Δ ⁏ Γ
idᵣ² = idᵣ , idᵣ

_∘ᵣ²_ : ∀ {ℓ ℓ′} → {X : Set ℓ} {Y : Set ℓ′} {Δ Δ′ Δ″ : List X} {Γ Γ′ Γ″ : List Y}
                 → Δ′ ⁏ Γ′ ⊇² Δ ⁏ Γ → Δ″ ⁏ Γ″ ⊇² Δ′ ⁏ Γ′
                 → Δ″ ⁏ Γ″ ⊇² Δ ⁏ Γ
η ∘ᵣ² η′ = (proj₁ η ∘ᵣ proj₁ η′) , (proj₂ η ∘ᵣ proj₂ η′)


mlookupᵣ : ∀ {ℓ ℓ′} → {X : Set ℓ} {Y : Set ℓ′} {Δ Δ′ : List X} {Γ Γ′ : List Y} {A : X}
                    → Δ′ ⁏ Γ′ ⊇² Δ ⁏ Γ → Δ ∋ A
                    → Δ′ ∋ A
mlookupᵣ η i = lookupᵣ (proj₁ η) i

rlookupᵣ : ∀ {ℓ ℓ′} → {X : Set ℓ} {Y : Set ℓ′} {Δ Δ′ : List X} {Γ Γ′ : List Y} {A : Y}
                    → Δ′ ⁏ Γ′ ⊇² Δ ⁏ Γ → Γ ∋ A
                    → Γ′ ∋ A
rlookupᵣ η i = lookupᵣ (proj₂ η) i


--------------------------------------------------------------------------------
