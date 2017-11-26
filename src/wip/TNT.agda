{-# OPTIONS --rewriting #-}

module TNT where

open import Prelude public
  renaming (zero to Z ; suc to S)
  hiding (tt)


--------------------------------------------------------------------------------
--
-- Syntax


-- -- Numeric variables
-- data NVar : Set
--   where
--     mkNV : String → NVar
--
-- injmkNV : ∀ {s₁ s₂} → mkNV s₁ ≡ mkNV s₂ → s₁ ≡ s₂
-- injmkNV refl = refl
--
-- _≟ₙᵥ_ : (x₁ x₂ : NVar) → Dec (x₁ ≡ x₂)
-- mkNV s₁ ≟ₙᵥ mkNV s₂ = mapDec (mkNV &_) injmkNV (s₁ ≟ₛ s₂)
--
-- instance
--   nvarIsString : IsString NVar
--   nvarIsString =
--     record
--       { Constraint = λ s → ⊤
--       ; fromString = λ s → mkNV s
--       }

NVar : Set
NVar = String

_≟ₙᵥ_ : (x₁ x₂ : NVar) → Dec (x₁ ≡ x₂)
_≟ₙᵥ_ = _≟ₛ_


-- Numeric expressions
infixl 18 _+_
infixl 19 _*_
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
      ; fromString = λ s → ⁿᵛ s -- (mkNV s)
      }


-- Types
infix  10 ∇_∶_
infix  11 ∃_∶_
infixl 12 _⫗_
infixr 13 _⊃_
infixl 14 _∨_
infixl 15 _∧_
infix  16 _==_
infix  17 ~_
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

_⫗_ : Type → Type → Type
A ⫗ B = (A ⊃ B) ∧ (B ⊃ A)


-- Substitution of numeric variables in numeric expressions
-- TODO: capture avoidance?
nsub[_≔_]_ : NVar → NExp → NExp → NExp
nsub[ x ≔ s ] ⁿ n     = ⁿ n
nsub[ x ≔ s ] ⁿᵛ y    with x ≟ₙᵥ y
...                   | yes refl = s
...                   | no x≢y   = ⁿᵛ y
nsub[ x ≔ s ] (S e)   = S (nsub[ x ≔ s ] e)
nsub[ x ≔ s ] (e + f) = nsub[ x ≔ s ] e + nsub[ x ≔ s ] f
nsub[ x ≔ s ] (e * f) = nsub[ x ≔ s ] e * nsub[ x ≔ s ] f

idnsub : ∀ x e → nsub[ x ≔ ⁿᵛ x ] e ≡ e
idnsub x (ⁿ n)   = refl
idnsub x (ⁿᵛ y)  with x ≟ₙᵥ y
...                | yes refl = refl
...                | no x≢y   = refl
idnsub x (S e)   = S & idnsub x e
idnsub x (e + f) = _+_ & idnsub x e ⊗ idnsub x f
idnsub x (e * f) = _*_ & idnsub x e ⊗ idnsub x f


-- Substitution of numeric variables in types
-- TODO: capture avoidance?
sub[_≔_]_ : NVar → NExp → Type → Type
sub[ x ≔ s ] (e == f)  = nsub[ x ≔ s ] e == nsub[ x ≔ s ] f
sub[ x ≔ s ] (~ A)     = ~ sub[ x ≔ s ] A
sub[ x ≔ s ] (A ∧ B)   = sub[ x ≔ s ] A ∧ sub[ x ≔ s ] B
sub[ x ≔ s ] (A ⊃ B)   = sub[ x ≔ s ] A ⊃ sub[ x ≔ s ] B
sub[ x ≔ s ] (∇ y ∶ A) with x ≟ₙᵥ y
...                    | yes refl = ∇ y ∶ A
...                    | no x≢y   = ∇ y ∶ sub[ x ≔ s ] A

idsub : ∀ x A → sub[ x ≔ ⁿᵛ x ] A ≡ A
idsub x (e == f)  = _==_ & idnsub x e ⊗ idnsub x f
idsub x (~ A)     = ~_ & idsub x A
idsub x (A ∧ B)   = _∧_ & idsub x A ⊗ idsub x B
idsub x (A ⊃ B)   = _⊃_ & idsub x A ⊗ idsub x B
idsub x (∇ y ∶ A) with x ≟ₙᵥ y
...               | yes refl = refl
...               | no x≢y   = ∇ y ∶_ & idsub x A

{-# REWRITE idsub #-}


-- Contexts
Context = List Type


-- Terms
infix  3 _⊢_
infixl 9 _$_
data _⊢_ : Context → Type → Set
  where
    -- Assumption / Hypothesis / Carry-over
    ᵛ : ∀ {A Γ} → Γ ∋ A
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
    Si : ∀ {e f Γ} → Γ ⊢ e == f
                   → Γ ⊢ S e == S f

    -- Successor elimination
    Se : ∀ {e f Γ} → Γ ⊢ S e == S f
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


ᵛ0 : ∀ {A Γ} → Γ , A ⊢ A
ᵛ0 = ᵛ Z

ᵛ1 : ∀ {A B Γ} → Γ , A , B ⊢ A
ᵛ1 = ᵛ (S Z)

ᵛ2 : ∀ {A B C Γ} → Γ , A , B , C ⊢ A
ᵛ2 = ᵛ (S (S Z))


ren : ∀ {A Γ Γ′} → Γ′ ⊇ Γ → Γ ⊢ A
                 → Γ′ ⊢ A
ren η (ᵛ i)             = ᵛ (renᵢ η i)
ren η (lam M)           = lam (ren (keep η) M)
ren η (M $ N)           = ren η M $ ren η N
ren η (M , N)           = ren η M , ren η N
ren η (fst M)           = fst (ren η M)
ren η (snd M)           = snd (ren η M)
ren η (dni M)           = dni (ren η M)
ren η (dne M)           = dne (ren η M)
ren η (contra M)        = contra (ren η M)
ren η (spec[ x ≔ s ] M) = spec[ x ≔ s ] (ren η M)
ren η (gen[ x ] M)      = gen[ x ] (ren η M)
ren η (sym M)           = sym (ren η M)
ren η (trans M N)       = trans (ren η M) (ren η N)
ren η (Si M)            = Si (ren η M)
ren η (Se M)            = Se (ren η M)
ren η (induc M N)       = induc (ren η M) (ren η N)
ren η axm₁              = axm₁
ren η axm₂              = axm₂
ren η axm₃              = axm₃
ren η axm₄              = axm₄
ren η axm₅              = axm₅

wk : ∀ {A B Γ} → Γ ⊢ A
               → Γ , B ⊢ A
wk M = ren (drop idᵣ) M


-- Contraposition II
ntra : ∀ {A B Γ} → Γ ⊢ ~ B ⊃ ~ A
                 → Γ ⊢ A ⊃ B
ntra M = lam (dne (wk (contra M) $ dni ᵛ0))

-- Denial of antecendent
deny : ∀ {A C Γ} → Γ ⊢ A → Γ ⊢ ~ A
                 → Γ ⊢ C
deny M N = ntra (lam (wk N)) $ M


-- Law of excluded middle
lem : ∀ {A Γ} → Γ ⊢ A ∨ ~ A
lem = lam ᵛ0


-- Truth
TT : Type
TT = ∇ "a" ∶ ~ (S "a" == 0)

-- Triviality
tt : ∀ {Γ} → Γ ⊢ TT
tt = axm₁


-- Falsehood
FF : Type
FF = ~ TT

-- Proof of negation
ne : ∀ {A Γ} → Γ , A ⊢ FF
             → Γ ⊢ ~ A
ne M = contra (lam M) $ dni tt

-- Proof by contradiction
abort : ∀ {A Γ} → Γ , ~ A ⊢ FF
                → Γ ⊢ A
abort M = dne (ne M)

-- Principle of explosion
boom : ∀ {C Γ} → Γ ⊢ FF
               → Γ ⊢ C
boom M = abort (wk M)


-- Switcheroo I
∨→~⊃ : ∀ {A B Γ} → Γ ⊢ A ∨ B
                  → Γ ⊢ ~ A ⊃ B
∨→~⊃ M = M

-- Switcheroo II
~⊃→∨ : ∀ {A B Γ} → Γ ⊢ ~ A ⊃ B
                  → Γ ⊢ A ∨ B
~⊃→∨ M = M

-- Switcheroo III
⊃→~∨ : ∀ {A B Γ} → Γ ⊢ A ⊃ B
                  → Γ ⊢ ~ A ∨ B
⊃→~∨ M = lam (wk M $ dne ᵛ0)

-- Switcheroo IV
~∨→⊃ : ∀ {A B Γ} → Γ ⊢ ~ A ∨ B
                  → Γ ⊢ A ⊃ B
~∨→⊃ M = lam (wk M $ dni ᵛ0)


dni∇ : ∀ {x A Γ} → Γ ⊢ ∇ x ∶ A
                 → Γ ⊢ ∇ x ∶ ~ ~ A
dni∇ {x} M = gen[ x ] (dni (spec[ x ≔ ⁿᵛ x ] M))

dne∇ : ∀ {x A Γ} → Γ ⊢ ∇ x ∶ ~ ~ A
                 → Γ ⊢ ∇ x ∶ A
dne∇ {x} M = gen[ x ] (dne (spec[ x ≔ ⁿᵛ x ] M))

dni∃ : ∀ {x A Γ} → Γ ⊢ ∃ x ∶ A
                 → Γ ⊢ ∃ x ∶ ~ ~ A
dni∃ {x} M = ne (deny (dne∇ ᵛ0) (wk M))

dne∃ : ∀ {x A Γ} → Γ ⊢ ∃ x ∶ ~ ~ A
                 → Γ ⊢ ∃ x ∶ A
dne∃ {x} M = ne (deny (dni∇ ᵛ0) (wk M))


dni∧₁ : ∀ {A B Γ} → Γ ⊢ A ∧ B
                  → Γ ⊢ ~ ~ A ∧ B
dni∧₁ M = dni (fst M) , snd M

dne∧₁ : ∀ {A B Γ} → Γ ⊢ ~ ~ A ∧ B
                  → Γ ⊢ A ∧ B
dne∧₁ M = dne (fst M) , snd M

dni∧₂ : ∀ {A B Γ} → Γ ⊢ A ∧ B
                  → Γ ⊢ A ∧ ~ ~ B
dni∧₂ M = fst M , dni (snd M)

dne∧₂ : ∀ {A B Γ} → Γ ⊢ A ∧ ~ ~ B
                  → Γ ⊢ A ∧ B
dne∧₂ M = fst M , dne (snd M)


dni⊃₁ : ∀ {A B Γ} → Γ ⊢ A ⊃ B
                  → Γ ⊢ ~ ~ A ⊃ B
dni⊃₁ M = lam (wk M $ dne ᵛ0)

dne⊃₁ : ∀ {A B Γ} → Γ ⊢ ~ ~ A ⊃ B
                  → Γ ⊢ A ⊃ B
dne⊃₁ M = lam (wk M $ dni ᵛ0)

dni⊃₂ : ∀ {A B Γ} → Γ ⊢ A ⊃ B
                  → Γ ⊢ A ⊃ ~ ~ B
dni⊃₂ M = lam (dni (wk M $ ᵛ0))

dne⊃₂ : ∀ {A B Γ} → Γ ⊢ A ⊃ ~ ~ B
                  → Γ ⊢ A ⊃ B
dne⊃₂ M = lam (dne (wk M $ ᵛ0))


swap∧ : ∀ {A B Γ} → Γ ⊢ A ∧ B
                  → Γ ⊢ B ∧ A
swap∧ M = snd M , fst M

swap∨ : ∀ {A B Γ} → Γ ⊢ A ∨ B
                  → Γ ⊢ B ∨ A
swap∨ M = dne⊃₂ (contra M)


-- Disjunction introduction II
right : ∀ {A B Γ} → Γ ⊢ B
                  → Γ ⊢ A ∨ B
right M = lam (wk M)

-- Disjunction introduction I
left : ∀ {A B Γ} → Γ ⊢ A
                 → Γ ⊢ A ∨ B
left M = swap∨ (right M)


-- De Morgan’s major law I
∇→~∃ : ∀ {x A Γ} → Γ ⊢ ∇ x ∶ ~ A
                  → Γ ⊢ ~ (∃ x ∶ A)
∇→~∃ M = dni M

-- De Morgan’s major law II
~∃→∇ : ∀ {x A Γ} → Γ ⊢ ~ (∃ x ∶ A)
                  → Γ ⊢ ∇ x ∶ ~ A
~∃→∇ M = dne M

-- De Morgan’s major law III
~∇→∃ : ∀ {x A Γ} → Γ ⊢ ~ (∇ x ∶ A)
                  → Γ ⊢ ∃ x ∶ ~ A
~∇→∃ M = ne (deny (dne∇ ᵛ0) (wk M))

-- De Morgan’s major law IV
∃→~∇ : ∀ {x A Γ} → Γ ⊢ ∃ x ∶ ~ A
                  → Γ ⊢ ~ (∇ x ∶ A)
∃→~∇ M = ne (deny (dni∇ ᵛ0) (wk M))


-- De Morgan’s minor law I
~∨→∧ : ∀ {A B Γ} → Γ ⊢ ~ (A ∨ B)
                  → Γ ⊢ ~ A ∧ ~ B
~∨→∧ M = ne (deny (left ᵛ0) (wk M)) , ne (deny (right ᵛ0) (wk M))

-- De Morgan’s minor law II
∧→~∨ : ∀ {A B Γ} → Γ ⊢ ~ A ∧ ~ B
                  → Γ ⊢ ~ (A ∨ B)
∧→~∨ M = ne (deny (ᵛ0 $ wk (fst M)) (wk (snd M)))

-- De Morgan’s minor law III
~∧→∨ : ∀ {A B Γ} → Γ ⊢ ~ (A ∧ B)
                  → Γ ⊢ ~ A ∨ ~ B
~∧→∨ M = lam (ne (deny (dne ᵛ1 , ᵛ0) (wk (wk M))))

-- De Morgan’s minor law IV
∨→~∧ : ∀ {A B Γ} → Γ ⊢ ~ A ∨ ~ B
                  → Γ ⊢ ~ (A ∧ B)
∨→~∧ M = ne (deny (snd ᵛ0) (wk M $ dni (fst ᵛ0)))


module Kleene where
  mutual
    K1a : ∀ {A B Γ} → Γ ⊢ A ⊃ B ⊃ A
    K1a = lam (lam ᵛ1)

    K1b : ∀ {A B C Γ} → Γ ⊢ (A ⊃ B) ⊃ (A ⊃ B ⊃ C) ⊃ A ⊃ C
    K1b = lam (lam (lam (ᵛ1 $ ᵛ0 $ (ᵛ2 $ ᵛ0))))

    K3 : ∀ {A B Γ} → Γ ⊢ A ⊃ B ⊃ A ∧ B
    K3 = lam (lam (ᵛ1 , ᵛ0))

    K4a : ∀ {A B Γ} → Γ ⊢ A ∧ B ⊃ A
    K4a = lam (fst ᵛ0)

    K4b : ∀ {A B Γ} → Γ ⊢ A ∧ B ⊃ B
    K4b = lam (snd ᵛ0)

    K5a : ∀ {A B Γ} → Γ ⊢ A ⊃ A ∨ B
    K5a = lam (left ᵛ0)

    K5b : ∀ {A B Γ} → Γ ⊢ B ⊃ A ∨ B
    K5b = lam (right ᵛ0)

    woop : ∀ {A C Γ} → Γ ⊢ (A ⊃ C) ⊃ (~ A ⊃ C) ⊃ C
    woop = lam (lam (swap∨ (snd K*36 $ (swap∨ (dni⊃₁ ᵛ1) , swap∨ (dni⊃₁ ᵛ0))) $ ne (deny (fst ᵛ0) (snd ᵛ0))))

    K6 : ∀ {A B C Γ} → Γ ⊢ (A ⊃ C) ⊃ (B ⊃ C) ⊃ A ∨ B ⊃ C
    K6 = lam (lam (lam (woop $ ᵛ2 $ (K*2 $ ᵛ0 $ ᵛ1))))

    case : ∀ {A B C Γ} → Γ ⊢ A ∨ B → Γ , A ⊢ C → Γ , B ⊢ C
                       → Γ ⊢ C
    case M N O = K6 $ lam N $ lam O $ M

    K7 : ∀ {A B Γ} → Γ ⊢ (A ⊃ B) ⊃ (A ⊃ ~ B) ⊃ ~ A
    K7 = lam (lam (ne (deny (ᵛ2 $ ᵛ0) (ᵛ1 $ ᵛ0))))

    K8 : ∀ {A Γ} → Γ ⊢ ~ ~ A ⊃ A
    K8 = lam (dne ᵛ0)

    K9a : ∀ {A B Γ} → Γ ⊢ (A ⊃ B) ⊃ (B ⊃ A) ⊃ (A ⫗ B)
    K9a = lam (lam (ᵛ1 , ᵛ0))

    K10a : ∀ {A B Γ} → Γ ⊢ (A ⫗ B) ⊃ A ⊃ B
    K10a = lam (fst ᵛ0)

    K10b : ∀ {A B Γ} → Γ ⊢ (A ⫗ B) ⊃ B ⊃ A
    K10b = lam (snd ᵛ0)

    -- Principle of identity
    K*1 : ∀ {A Γ} → Γ ⊢ A ⊃ A
    K*1 = lam ᵛ0

    -- Chain inference
    K*2 : ∀ {A B C Γ} → Γ ⊢ (A ⊃ B) ⊃ (B ⊃ C) ⊃ A ⊃ C
    K*2 = lam (lam (lam (ᵛ1 $ (ᵛ2 $ ᵛ0))))

    -- Interchange of premises
    K*3 : ∀ {A B C Γ} → Γ ⊢ A ⊃ B ⊃ C ⫗ B ⊃ A ⊃ C
    K*3 = lam (lam (lam (ᵛ2 $ ᵛ0 $ ᵛ1))) ,
          lam (lam (lam (ᵛ2 $ ᵛ0 $ ᵛ1)))

    -- Importation and exportation
    K*4a : ∀ {A B C Γ} → Γ ⊢ A ⊃ B ⊃ C ⫗ A ∧ B ⊃ C
    K*4a = lam (lam (ᵛ1 $ fst ᵛ0 $ snd ᵛ0)) ,
           lam (lam (lam (ᵛ2 $ (ᵛ1 , ᵛ0))))

    -- Denial of the antecedent
    K*10a : ∀ {A B Γ} → Γ ⊢ ~ A ⊃ A ⊃ B
    K*10a = lam (lam (deny ᵛ0 ᵛ1))

    -- Contraposition
    K*12a° : ∀ {A B Γ} → Γ ⊢ A ⊃ B ⫗ ~ B ⊃ ~ A
    K*12a° = lam (contra ᵛ0) , lam (ntra ᵛ0)

    -- Reflexive property of equivalence
    K*19 : ∀ {A Γ} → Γ ⊢ A ⫗ A
    K*19 = K*1 , K*1

    -- Symmetric property of equivalence
    K*20 : ∀ {A B Γ} → Γ ⊢ (A ⫗ B) ⫗ (B ⫗ A)
    K*20 = lam (snd ᵛ0 , fst ᵛ0) ,
           lam (snd ᵛ0 , fst ᵛ0)

    -- Transitive property of equivalence
    K*21 : ∀ {A B C Γ} → Γ ⊢ (A ⫗ B) ∧ (B ⫗ C) ⊃ (A ⫗ C)
    K*21 = lam (lam (fst (snd ᵛ1) $ (fst (fst ᵛ1) $ ᵛ0)) ,
                lam (snd (fst ᵛ1) $ (snd (snd ᵛ1) $ ᵛ0)))

    -- Associative law of conjunction
    K*31 : ∀ {A B C Γ} → Γ ⊢ (A ∧ B) ∧ C ⫗ A ∧ (B ∧ C)
    K*31 = lam (fst (fst ᵛ0) , (snd (fst ᵛ0) , snd ᵛ0)) ,
           lam ((fst ᵛ0 , fst (snd ᵛ0)) , snd (snd ᵛ0))

    -- Associative law of disjunction
    K*32 : ∀ {A B C Γ} → Γ ⊢ (A ∨ B) ∨ C ⫗ A ∨ (B ∨ C)
    K*32 = lam (lam (lam (ᵛ2 $ (snd K*55a $ (ᵛ1 , ᵛ0))))) ,
           lam (lam (ᵛ1 $ fst (fst K*55a $ ᵛ0) $ snd (fst K*55a $ ᵛ0)))

    -- Commutative law of conjunction
    K*33 : ∀ {A B Γ} → Γ ⊢ A ∧ B ⫗ B ∧ A
    K*33 = lam (swap∧ ᵛ0) , lam (swap∧ ᵛ0)

    -- Commutative law of disjunction
    K*34 : ∀ {A B Γ} → Γ ⊢ A ∨ B ⫗ B ∨ A
    K*34 = lam (swap∨ ᵛ0) , lam (swap∨ ᵛ0)

    -- Distributive law of conjunction over disjunction
    K*35 : ∀ {A B C Γ} → Γ ⊢ A ∧ (B ∨ C) ⫗ (A ∧ B) ∨ (A ∧ C)
    K*35 = lam (case (snd ᵛ0) (left (fst ᵛ1 , ᵛ0))
                              (right (fst ᵛ1 , ᵛ0))) ,
           lam (case ᵛ0 (fst ᵛ0 , left (snd ᵛ0))
                        (fst ᵛ0 , right (snd ᵛ0)))

    -- Distributive law of disjunction over conjunction
    K*36 : ∀ {A B C Γ} → Γ ⊢ A ∨ (B ∧ C) ⫗ (A ∨ B) ∧ (A ∨ C)
    K*36 = lam (lam (fst (ᵛ1 $ ᵛ0)) , lam (snd (ᵛ1 $ ᵛ0))) ,
           lam (lam (fst ᵛ1 $ ᵛ0 , snd ᵛ1 $ ᵛ0))

    -- Idempotent law of conjunction
    K*37 : ∀ {A Γ} → Γ ⊢ A ∧ A ⫗ A
    K*37 = lam (fst ᵛ0) , lam (ᵛ0 , ᵛ0)

    -- Idempotent law of disjunction
    K*38 : ∀ {A Γ} → Γ ⊢ A ∨ A ⫗ A
    K*38 = ntra (lam (ne (deny (ᵛ0 $ ᵛ1) ᵛ1))) ,
           lam (left ᵛ0)

    -- Elimination law of conjunction over disjunction
    K*39 : ∀ {A B Γ} → Γ ⊢ A ∧ (A ∨ B) ⫗ A
    K*39 = lam (fst ᵛ0) , lam (ᵛ0 , left ᵛ0)

    -- Elimination law of disjunction over conjunction
    K*40 : ∀ {A B Γ} → Γ ⊢ A ∨ (A ∧ B) ⫗ A
    K*40 = ntra (lam (ne (deny (fst (ᵛ0 $ ᵛ1)) ᵛ1))) ,
           lam (lam (deny ᵛ1 ᵛ0))

    -- Law of double negation
    K*49° : ∀ {A Γ} → Γ ⊢ ~ ~ A ⫗ A
    K*49° = lam (dne ᵛ0) , lam (dni ᵛ0)

    -- Denial of contradiction
    K*50 : ∀ {A Γ} → Γ ⊢ ~ (A ∧ ~ A)
    K*50 = ne (deny (fst ᵛ0) (snd ᵛ0))

    -- Law of the excluded middle
    K*51° : ∀ {A Γ} → Γ ⊢ A ∨ ~ A
    K*51° = lem

    -- De Morgan’s law I
    K*55a : ∀ {A B Γ} → Γ ⊢ ~ (A ∨ B) ⫗ ~ A ∧ ~ B
    K*55a = lam (ne (deny (left ᵛ0) ᵛ1) , ne (deny (right ᵛ0) ᵛ1)) ,
            lam (ne (deny (ᵛ0 $ fst ᵛ1) (snd ᵛ1)))

    -- De Morgan’s law II
    K*55b° : ∀ {A B Γ} → Γ ⊢ ~ (A ∧ B) ⫗ ~ A ∨ ~ B
    K*55b° = lam (lam (ne (deny (dne ᵛ1 , ᵛ0) ᵛ2))) ,
             lam (ne (deny (snd ᵛ0) (ᵛ1 $ dni (fst ᵛ0))))

    -- Negation of an implication
    K*55c° : ∀ {A B Γ} → Γ ⊢ ~ (A ⊃ B) ⫗ A ∧ ~ B
    K*55c° = ntra (lam (dni (lam (dne (fst K*55b° $ ᵛ1 $ dni ᵛ0))))) ,
             lam (ne (deny (ᵛ0 $ fst ᵛ1) (snd ᵛ1)))

    -- Expression for disjunction in terms of conjunction
    K*56° : ∀ {A B Γ} → Γ ⊢ A ∨ B ⫗ ~ (~ A ∧ ~ B)
    K*56° = lam (ne (deny ᵛ1 (snd K*55a $ ᵛ0))) ,
            ntra (lam (dni (fst K*55a $ ᵛ0)))

    -- Expression for conjunction in terms of disjunction
    K*57° : ∀ {A B Γ} → Γ ⊢ A ∧ B ⫗ ~ (~ A ∨ ~ B)
    K*57° = lam (snd K*55a $ (dni (fst ᵛ0) , dni (snd ᵛ0))) ,
            lam (dne (fst (fst K*55a $ ᵛ0)) , dne (snd (fst K*55a $ ᵛ0)))

    -- Expression for implication in terms of conjunction
    K*58° : ∀ {A B Γ} → Γ ⊢ A ⊃ B ⫗ ~ (A ∧ ~ B)
    K*58° = lam (snd K*55b° $ lam (dni (ᵛ1 $ dne ᵛ0))) ,
            lam (lam (dne (fst K*55b° $ ᵛ1 $ dni ᵛ0)))

    -- Expression for implication in terms of disjunction
    K*59° : ∀ {A B Γ} → Γ ⊢ A ⊃ B ⫗ ~ A ∨ B
    K*59° = lam (lam (ᵛ1 $ dne ᵛ0)) ,
            lam (lam (ᵛ1 $ dni ᵛ0))

    -- Expression for conjunction in terms of implication
    K*60° : ∀ {A B Γ} → Γ ⊢ A ∧ B ⫗ ~ (A ⊃ ~ B)
    K*60° = lam (snd K*55c° $ (fst ᵛ0 , dni (snd ᵛ0))) ,
            lam (fst (fst K*55c° $ ᵛ0) , dne (snd (fst K*55c° $ ᵛ0)))

    -- Expression for disjunction in terms of implication
    K*61° : ∀ {A B Γ} → Γ ⊢ A ∨ B ⫗ ~ A ⊃ B
    K*61° = lam (lam (ᵛ1 $ ᵛ0)) ,
            lam (lam (ᵛ1 $ ᵛ0))

    -- Expression for equivalence in terms of conjunction of implications
    K*62° : ∀ {A B Γ} → Γ ⊢ (A ⫗ B) ⫗ (A ⊃ B) ∧ (B ⊃ A)
    K*62° = K*1 , K*1


module VonEitzen where
  -- Equality is reflexive
  thm₁ : ∀ {Γ} → Γ ⊢ ∇ "a" ∶ "a" == "a"
  thm₁ = gen[ "a" ] (trans (sym (spec[ "a" ≔ "a" ] axm₂))
                           (spec[ "a" ≔ "a" ] axm₂))

  thm₂ : ∀ {Γ} → Γ ⊢ ∇ "a" ∶ ~ (S "a" == "a")
  thm₂ = induc (spec[ "a" ≔ 0 ] axm₁)
               (gen[ "a" ] (contra (lam (Se ᵛ0))))

  -- Only 0 has no predecessor
  thm₃ : ∀ {Γ} → Γ ⊢ ∇ "a" ∶ ∇ "b" ∶ ~ (S "b" == "a") ⊃ "a" == 0
  thm₃ = induc (gen[ "b" ] (lam (spec[ "a" ≔ 0 ] thm₁)))
               (gen[ "a" ] (lam (gen[ "b" ] (lam
                 (dne (contra (lam (spec[ "a" ≔ S "a" ] thm₁)) $
                   spec[ "b" ≔ "a" ] (gen[ "b" ] ᵛ0)))))))
