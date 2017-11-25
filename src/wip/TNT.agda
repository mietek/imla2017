{-# OPTIONS --rewriting #-}

module TNT where

open import Prelude public
  hiding (tt)


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
infix  19 S_
data NExp : Set
  where
    nat  : Nat → NExp
    nvar : NVar → NExp
    suc  : NExp → NExp
    _+_  : NExp → NExp → NExp
    _*_  : NExp → NExp → NExp

instance
  nexpIsNumber : Number NExp
  nexpIsNumber =
    record
      { Constraint = λ n → ⊤
      ; fromNat    = λ n → nat n
      }

instance
  nexpIsString : IsString NExp
  nexpIsString =
    record
      { Constraint = λ s → ⊤
      ; fromString = λ s → nvar (mkNV s)
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
-- TODO: capture avoidance
nsub[_≔_]_ : NVar → NExp → NExp → NExp
nsub[ x ≔ s ] nat n   = nat n
nsub[ x ≔ s ] nvar y  with x ≟ₙᵥ y
...                   | yes refl = s
...                   | no x≢y   = nvar y
nsub[ x ≔ s ] (suc e) = suc (nsub[ x ≔ s ] e)
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
    var : ∀ {A Γ} → Γ ∋ A
                  → Γ ⊢ A

    -- Fantasy
    lam : ∀ {A B Γ} → Γ , A ⊢ B
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
    dni : ∀ {A Γ} → Γ ⊢ A
                  → Γ ⊢ ~ ~ A

    -- Double negation elimination
    dne : ∀ {A Γ} → Γ ⊢ ~ ~ A
                  → Γ ⊢ A

    -- Contraposition I
    contrapos : ∀ {A B Γ} → Γ ⊢ A ⊃ B
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
    suci : ∀ {e f Γ} → Γ ⊢ e == f
                     → Γ ⊢ suc e == suc f

    -- Successor elimination
    suce : ∀ {e f Γ} → Γ ⊢ suc e == suc f
                     → Γ ⊢ e == f

    -- Induction
    induc : ∀ {x A Γ} → Γ ⊢ sub[ x ≔ 0 ] A → Γ ⊢ ∇ x ∶ A ⊃ sub[ x ≔ suc (nvar x) ] A
                      → Γ ⊢ ∇ x ∶ A

    -- Axiom 1
    axm₁ : ∀ {Γ} → Γ ⊢ ∇ "a" ∶ ~ (suc "a" == 0)

    -- Axiom 2
    axm₂ : ∀ {Γ} → Γ ⊢ ∇ "a" ∶ ("a" + 0) == "a"

    -- Axiom 3
    axm₃ : ∀ {Γ} → Γ ⊢ ∇ "a" ∶ ∇ "b" ∶ ("a" + suc "b") == suc ("a" + "b")

    -- Axiom 4
    axm₄ : ∀ {Γ} → Γ ⊢ ∇ "a" ∶ ("a" * 0) == 0

    -- Axiom 5
    axm₅ : ∀ {Γ} → Γ ⊢ ∇ "a" ∶ ∇ "b" ∶ ("a" * suc "b") == ("a" * "b") + "a"


-- instance
--   ⊢IsNumber : ∀ {Γ A} → Number (Γ ⊢ A)
--   ⊢IsNumber {Γ} {A} =
--     record
--       { Constraint = λ i → Σ (True (len Γ ⩼ i))
--                               (λ p → lookupList Γ i {{p}} ≡ A)
--       ; fromNat    = λ { i {{p , refl}} → var (Nat→∋ i) }
--       }


ren : ∀ {A Γ Γ′} → Γ′ ⊇ Γ → Γ ⊢ A
                 → Γ′ ⊢ A
ren η (var i)           = var (renᵢ η i)
ren η (lam M)           = lam (ren (keep η) M)
ren η (M $ N)           = ren η M $ ren η N
ren η (M , N)           = ren η M , ren η N
ren η (fst M)           = fst (ren η M)
ren η (snd M)           = snd (ren η M)
ren η (dni M)           = dni (ren η M)
ren η (dne M)           = dne (ren η M)
ren η (contrapos M)     = contrapos (ren η M)
ren η (spec[ x ≔ s ] M) = spec[ x ≔ s ] (ren η M)
ren η (gen[ x ] M)      = gen[ x ] (ren η M)
ren η (sym M)           = sym (ren η M)
ren η (trans M N)       = trans (ren η M) (ren η N)
ren η (suci M)          = suci (ren η M)
ren η (suce M)          = suce (ren η M)
ren η (induc M N)       = induc (ren η M) (ren η N)
ren η axm₁              = axm₁
ren η axm₂              = axm₂
ren η axm₃              = axm₃
ren η axm₄              = axm₄
ren η axm₅              = axm₅


-- Law of excluded middle
lem : ∀ {A Γ} → Γ ⊢ A ∨ ~ A
lem = lam (var 0)


-- Truth
TT : Type
TT = ∇ "a" ∶ ~ (suc "a" == 0)

-- Triviality
tt : ∀ {Γ} → Γ ⊢ TT
tt = axm₁


-- Falsehood
FF : Type
FF = ~ TT

-- Proof of negation
ne : ∀ {A Γ} → Γ , A ⊢ FF
             → Γ ⊢ ~ A
ne M = contrapos (lam M) $ dni tt

-- Proof by contradiction
abort : ∀ {A Γ} → Γ , ~ A ⊢ FF
                → Γ ⊢ A
abort M = dne (ne M)


-- Ex falso quodlibet
efq : ∀ {C Γ} → Γ ⊢ FF
              → Γ ⊢ C
efq M = abort (ren (drop idᵣ) M)


-- Contraposition II
uncontrapos : ∀ {A B Γ} → Γ ⊢ ~ B ⊃ ~ A
                        → Γ ⊢ A ⊃ B
uncontrapos M = lam (dne (ren (drop idᵣ) (contrapos M) $ dni (var 0)))


-- Switcheroo I
∨→~⊃ : ∀ {A B Γ} → Γ ⊢ A ∨ B
                  → Γ ⊢ ~ A ⊃ B
∨→~⊃ M = M

-- Switcheroo II
~⊃→∨ : ∀ {A B Γ} → Γ ⊢ ~ A ⊃ B
                  → Γ ⊢ A ∨ B
~⊃→∨ M = M


-- TODO: what the fork?
contradic : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ ~ A
                    → Γ ⊢ FF
contradic M N = {!!}


-- TODO: substitution of variable by itself must be identity
postulate
  idsub : ∀ {x A} → sub[ x ≔ nvar x ] A ≡ A

{-# REWRITE idsub #-}

dni∇ : ∀ {x A Γ} → Γ ⊢ ∇ x ∶ A
                 → Γ ⊢ ∇ x ∶ ~ ~ A
dni∇ {x} M = gen[ x ] (dni (spec[ x ≔ nvar x ] M))

dne∇ : ∀ {x A Γ} → Γ ⊢ ∇ x ∶ ~ ~ A
                 → Γ ⊢ ∇ x ∶ A
dne∇ {x} M = gen[ x ] (dne (spec[ x ≔ nvar x ] M))

dni∃ : ∀ {x A Γ} → Γ ⊢ ∃ x ∶ A
                 → Γ ⊢ ∃ x ∶ ~ ~ A
dni∃ {x} M = ne (contradic (dne∇ (var 0))
                           (ren (drop idᵣ) M))

dne∃ : ∀ {x A Γ} → Γ ⊢ ∃ x ∶ ~ ~ A
                 → Γ ⊢ ∃ x ∶ A
dne∃ {x} M = ne (contradic (dni∇ (var 0))
                           (ren (drop idᵣ) M))


-- DeMorgan’s major law I
∇→~∃ : ∀ {x A Γ} → Γ ⊢ ∇ x ∶ ~ A
                  → Γ ⊢ ~ (∃ x ∶ A)
∇→~∃ M = dni M

-- DeMorgan’s major law II
~∃→∇ : ∀ {x A Γ} → Γ ⊢ ~ (∃ x ∶ A)
                  → Γ ⊢ ∇ x ∶ ~ A
~∃→∇ M = dne M

-- DeMorgan’s major law III
~∇→∃ : ∀ {x A Γ} → Γ ⊢ ~ (∇ x ∶ A)
                  → Γ ⊢ ∃ x ∶ ~ A
~∇→∃ M = ne (contradic (dne∇ (var 0))
                        (ren (drop idᵣ) M))

-- DeMorgan’s major law IV
∃→~∇ : ∀ {x A Γ} → Γ ⊢ ∃ x ∶ ~ A
                  → Γ ⊢ ~ (∇ x ∶ A)
∃→~∇ M = ne (contradic (dni∇ (var 0))
                        (ren (drop idᵣ) M))


-- Disjunction introduction I
left : ∀ {A B Γ} → Γ ⊢ A
                 → Γ ⊢ A ∨ B
left M = lam (efq (contradic (ren (drop idᵣ) M)
                             (var 0)))

-- Disjunction introduction II
right : ∀ {A B Γ} → Γ ⊢ B
                  → Γ ⊢ A ∨ B
right M = lam (ren (drop idᵣ) M)

-- Disjunction elimination
case : ∀ {A B C Γ} → Γ ⊢ A ∨ B → Γ , A ⊢ C → Γ , B ⊢ C
                   → Γ ⊢ C
case M N O = {!!}


-- DeMorgan’s minor law I
∧→~∨ : ∀ {A B Γ} → Γ ⊢ ~ A ∧ ~ B
                  → Γ ⊢ ~ (A ∨ B)
∧→~∨ M = ne (contradic (var 0 $ ren (drop idᵣ) (fst M))
                        (ren (drop idᵣ) (snd M)))

-- DeMorgan’s minor law II
~∨→∧ : ∀ {A B Γ} → Γ ⊢ ~ (A ∨ B)
                  → Γ ⊢ ~ A ∧ ~ B
~∨→∧ M = ne (contradic (left (var 0))
                        (ren (drop idᵣ) M)) ,
          ne (contradic (right (var 0))
                        (ren (drop idᵣ) M))

-- DeMorgan’s minor law III
~∧→∨ : ∀ {A B Γ} → Γ ⊢ ~ (A ∧ B)
                  → Γ ⊢ ~ A ∨ ~ B
~∧→∨ M = lam (ne (contradic (dne (var 1) , var 0)
                             (ren (drop (drop idᵣ)) M)))

-- DeMorgan’s minor law IV
∨→~∧ : ∀ {A B Γ} → Γ ⊢ ~ A ∨ ~ B
                  → Γ ⊢ ~ (A ∧ B)
∨→~∧ M = ne (contradic (snd (var zero))
                        (ren (drop idᵣ) M $ dni (fst (var zero))))


-- Equality is reflexive
thm₁ : ∀ {Γ} → Γ ⊢ ∇ "a" ∶ "a" == "a"
thm₁ = gen[ "a" ] (trans (sym (spec[ "a" ≔ "a" ] axm₂))
                         (spec[ "a" ≔ "a" ] axm₂))

thm₂ : ∀ {Γ} → Γ ⊢ ∇ "a" ∶ ~ (suc "a" == "a")
thm₂ = induc (spec[ "a" ≔ 0 ] axm₁)
             (gen[ "a" ] (contrapos (lam (suce (var 0)))))

-- Only 0 has no predecessor
thm₃ : ∀ {Γ} → Γ ⊢ ∇ "a" ∶ ∇ "b" ∶ ~ (suc "b" == "a" ⊃ "a" == 0)
thm₃ = induc {!!}
             {!!}
