module TNT where

open import Prelude public
  renaming (suc to S ; zero to Z)


--------------------------------------------------------------------------------
--
-- Syntax


-- Numeric variables
data NVar : Set
  where
    mkNV : String → NVar

injmkNV : ∀ {s₁ s₂} → mkNV s₁ ≡ mkNV s₂ → s₁ ≡ s₂
injmkNV refl = refl

_≟ₙᵥ_ : (x₁ x₂ : NVar) → Dec (x₁ ≡ x₂)
mkNV s₁ ≟ₙᵥ mkNV s₂ = mapDec (mkNV &_) injmkNV (s₁ ≟ₛ s₂)

instance
  nvarIsString : IsString NVar
  nvarIsString =
    record
      { Constraint = λ s → ⊤
      ; fromString = λ s → mkNV s
      }


-- Numeric expressions
infixl 17 _+_
infixl 18 _*_
data NExp : Set
  where
    ⁿ   : Nat → NExp
    ⁿᵛ  : NVar → NExp
    S   : NExp → NExp
    _+_ : NExp → NExp → NExp
    _*_ : NExp → NExp → NExp

instance
  nexpIsNumber : Number NExp
  nexpIsNumber =
    record
      { Constraint = λ n → ⊤
      ; fromNat    = λ n → ⁿ n
      }

instance
  nexpIsString : IsString NExp
  nexpIsString =
    record
      { Constraint = λ s → ⊤
      ; fromString = λ s → ⁿᵛ (mkNV s)
      }


-- Types
infix  10 ∇_∶_
infix  11 ∃_∶_
infixr 12 _⊃_
infixl 13 _∨_
infixl 14 _∧_
infix  15 _==_
infix  16 ~_
data Type : Set
  where
    _==_ : NExp → NExp → Type
    ~_   : Type → Type
    _∧_  : Type → Type → Type
    _⊃_  : Type → Type → Type
    ∇_∶_ : NVar → Type → Type

_∨_ : Type → Type → Type
A ∨ B = ~ A ⊃ B

∃_∶_ : NVar → Type → Type
∃ x ∶ A = ~ (∇ x ∶ ~ A)


-- Substitution of numeric variables in numeric expressions
nsub[_≔_]_ : NVar → NExp → NExp → NExp
nsub[ x ≔ s ] ⁿ n     = ⁿ n
nsub[ x ≔ s ] ⁿᵛ y    with x ≟ₙᵥ y
...                   | yes refl = s
...                   | no x≢y   = ⁿᵛ y
nsub[ x ≔ s ] S e     = S (nsub[ x ≔ s ] e)
nsub[ x ≔ s ] (e + f) = nsub[ x ≔ s ] e + nsub[ x ≔ s ] f
nsub[ x ≔ s ] (e * f) = nsub[ x ≔ s ] e * nsub[ x ≔ s ] f


-- Substitution of numeric variables in types
sub[_≔_]_ : NVar → NExp → Type → Type
sub[ x ≔ s ] (e == f)  = nsub[ x ≔ s ] e == nsub[ x ≔ s ] f
sub[ x ≔ s ] (~ A)     = ~ sub[ x ≔ s ] A
sub[ x ≔ s ] (A ∧ B)   = sub[ x ≔ s ] A ∧ sub[ x ≔ s ] B
sub[ x ≔ s ] (A ⊃ B)   = sub[ x ≔ s ] A ⊃ sub[ x ≔ s ] B
sub[ x ≔ s ] (∇ y ∶ A) with x ≟ₙᵥ y
...                    | yes refl = ∇ y ∶ A
...                    | no x≢y   = ∇ y ∶ sub[ x ≔ s ] A


-- Contexts
Context = List Type


-- Terms
infix 3 _⊢_
data _⊢_ : Context → Type → Set
  where
    -- Assumption / Hypothesis / Carry-over
    ᵛ : ∀ {A Γ} → Γ ∋ A
                → Γ ⊢ A

    -- Fantasy
    ƛ : ∀ {A B Γ} → Γ , A ⊢ B
                  → Γ ⊢ A ⊃ B

    -- Detachment / Modus ponens
    _$_ : ∀ {A B Γ} → Γ ⊢ A ⊃ B → Γ ⊢ A
                    → Γ ⊢ B

    -- Joining
    _,_ : ∀ {A B Γ} → Γ ⊢ A → Γ ⊢ B
                    → Γ ⊢ A ∧ B

    -- Separation I
    fst : ∀ {A B Γ} → Γ ⊢ A ∧ B
                    → Γ ⊢ A

    -- Separation II
    snd : ∀ {A B Γ} → Γ ⊢ A ∧ B
                    → Γ ⊢ B

    -- Double negation introduction
    ≈₊ : ∀ {A Γ} → Γ ⊢ A
                 → Γ ⊢ ~ ~ A

    -- Double negation elimination
    ≈₋ : ∀ {A Γ} → Γ ⊢ ~ ~ A
                 → Γ ⊢ A

    -- Contraposition I
    contra : ∀ {A B Γ} → Γ ⊢ A ⊃ B
                       → Γ ⊢ ~ B ⊃ ~ A

    -- Specialisation
    -- TODO: s must not contain any variables bound in A
    spec[_≔_] : ∀ {A Γ} → (x : NVar) (s : NExp) → Γ ⊢ ∇ x ∶ A
                        → Γ ⊢ sub[ x ≔ s ] A

    -- Generalisation
    -- TODO: x must not be free in the premise of any fantasy containing A
    gen[_] : ∀ {A Γ} → (x : NVar) → Γ ⊢ A
                     → Γ ⊢ ∇ x ∶ A

    -- Symmetry
    sym : ∀ {e f Γ} → Γ ⊢ e == f
                    → Γ ⊢ f == e

    -- Transitivity
    trans : ∀ {e f g Γ} → Γ ⊢ e == f → Γ ⊢ f == g
                        → Γ ⊢ e == g

    -- Successor introduction
    S₊ : ∀ {e f Γ} → Γ ⊢ e == f
                   → Γ ⊢ S e == S f

    -- Successor elimination
    S₋ : ∀ {e f Γ} → Γ ⊢ S e == S f
                   → Γ ⊢ e == f

    -- Induction
    induc : ∀ {x A Γ} → Γ ⊢ sub[ x ≔ 0 ] A → Γ ⊢ ∇ x ∶ A ⊃ sub[ x ≔ S (ⁿᵛ x) ] A
                      → Γ ⊢ ∇ x ∶ A

    -- Axiom 1
    axm₁ : ∀ {Γ} → Γ ⊢ ∇ "a" ∶ ~ (S "a" == 0)

    -- Axiom 2
    axm₂ : ∀ {Γ} → Γ ⊢ ∇ "a" ∶ ("a" + 0) == "a"

    -- Axiom 3
    axm₃ : ∀ {Γ} → Γ ⊢ ∇ "a" ∶ ∇ "b" ∶ ("a" + S "b") == S ("a" + "b")

    -- Axiom 4
    axm₄ : ∀ {Γ} → Γ ⊢ ∇ "a" ∶ ("a" * 0) == 0

    -- Axiom 5
    axm₅ : ∀ {Γ} → Γ ⊢ ∇ "a" ∶ ∇ "b" ∶ ("a" * S "b") == ("a" * "b") + "a"


instance
  ⊢IsNumber : ∀ {Γ A} → Number (Γ ⊢ A)
  ⊢IsNumber {Γ} {A} =
    record
      { Constraint = λ i → Σ (True (len Γ ⩼ i))
                              (λ p → lookupList Γ i {{p}} ≡ A)
      ; fromNat    = λ { i {{p , refl}} → ᵛ (Nat→∋ i) }
      }


ren : ∀ {A Γ Γ′} → Γ′ ⊇ Γ → Γ ⊢ A
                 → Γ′ ⊢ A
ren η (ᵛ i)             = ᵛ (renᵢ η i)
ren η (ƛ M)             = ƛ (ren (keep η) M)
ren η (M $ N)           = ren η M $ ren η N
ren η (M , N)           = ren η M , ren η N
ren η (fst M)           = fst (ren η M)
ren η (snd M)           = snd (ren η M)
ren η (≈₊ M)            = ≈₊ (ren η M)
ren η (≈₋ M)            = ≈₋ (ren η M)
ren η (contra M)        = contra (ren η M)
ren η (spec[ x ≔ s ] M) = spec[ x ≔ s ] (ren η M)
ren η (gen[ x ] M)      = gen[ x ] (ren η M)
ren η (sym M)           = sym (ren η M)
ren η (trans M N)       = trans (ren η M) (ren η N)
ren η (S₊ M)            = S₊ (ren η M)
ren η (S₋ M)            = S₋ (ren η M)
ren η (induc M N)       = induc (ren η M) (ren η N)
ren η axm₁              = axm₁
ren η axm₂              = axm₂
ren η axm₃              = axm₃
ren η axm₄              = axm₄
ren η axm₅              = axm₅


-- Contraposition II
uncontra : ∀ {A B Γ} → Γ ⊢ ~ B ⊃ ~ A
                     → Γ ⊢ A ⊃ B
uncontra M = ƛ (≈₋ (ren (drop idᵣ) (contra M) $ ≈₊ 0))

-- Switcheroo I
∨→⊃ : ∀ {A B Γ} → Γ ⊢ A ∨ B
                 → Γ ⊢ ~ A ⊃ B
∨→⊃ M = M

-- Switcheroo II
⊃→∨ : ∀ {A B Γ} → Γ ⊢ ~ A ⊃ B
                 → Γ ⊢ A ∨ B
⊃→∨ M = M

-- DeMorgan's minor I
∧→∨ : ∀ {A B Γ} → Γ ⊢ ~ A ∧ ~ B
                 → Γ ⊢ ~ (A ∨ B)
∧→∨ M = {!!}

-- DeMorgan's minor II
∨→∧ : ∀ {A B Γ} → Γ ⊢ ~ (A ∨ B)
                 → Γ ⊢ ~ A ∧ ~ B
∨→∧ M = {!!}

-- DeMorgan's major I
∇→∃ : ∀ {x A Γ} → Γ ⊢ ∇ x ∶ ~ A
                 → Γ ⊢ ~ (∃ x ∶ A)
∇→∃ M = ≈₊ M

-- DeMorgan's major II
∃→∇ : ∀ {x A Γ} → Γ ⊢ ~ (∃ x ∶ A)
                 → Γ ⊢ ∇ x ∶ ~ A
∃→∇ M = ≈₋ M


-- Law of excluded middle
lem : ∀ {A Γ} → Γ ⊢ A ∨ ~ A
lem = ƛ 0


-- Equality is reflexive
thm₁ : ∀ {Γ} → Γ ⊢ ∇ "a" ∶ "a" == "a"
thm₁ = gen[ "a" ] (trans (sym (spec[ "a" ≔ "a" ] axm₂)) (spec[ "a" ≔ "a" ] axm₂))

thm₂ : ∀ {Γ} → Γ ⊢ ∇ "a" ∶ ~ (S "a" == "a")
thm₂ = induc (spec[ "a" ≔ 0 ] axm₁)
             (gen[ "a" ] (contra (ƛ (S₋ 0))))

-- Only 0 has no predecessor
thm₃ : ∀ {Γ} → Γ ⊢ ∇ "a" ∶ ∇ "b" ∶ ~ (S "b" == "a" ⊃ "a" == 0)
thm₃ = induc {!!}
             {!!}


-- ~sym : ∀ {e f Γ} → Γ ⊢ ~ (e == f)
--                  → Γ ⊢ ~ (f == e)
-- ~sym M = {!!}
--
-- -- Proof by contradiction
-- abort : ∀ {A Γ} → Γ , ~ A ⊢ 0 == S 0
--                 → Γ ⊢ A
-- abort M = ≈₋ (contra (ƛ M) $ ~sym (spec[ "a" ≔ 0 ] axm₁))
