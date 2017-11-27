{-# OPTIONS --rewriting #-}

module TNT where

open import Prelude public
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
    nat  : Nat → NExp
    nvar : NVar → NExp
    suc  : NExp → NExp
    _+_  : NExp → NExp → NExp
    _*_  : NExp → NExp → NExp

{-# DISPLAY nat n = n #-}
{-# DISPLAY nvar s = s #-}

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
      ; fromString = λ s → nvar s -- (mkNV s)
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
nsub[ x ≔ s ] nat n   = nat n
nsub[ x ≔ s ] nvar y  with x ≟ₙᵥ y
...                   | yes refl = s
...                   | no x≢y   = nvar y
nsub[ x ≔ s ] (suc e) = suc (nsub[ x ≔ s ] e)
nsub[ x ≔ s ] (e + f) = nsub[ x ≔ s ] e + nsub[ x ≔ s ] f
nsub[ x ≔ s ] (e * f) = nsub[ x ≔ s ] e * nsub[ x ≔ s ] f

idnsub : ∀ x e → nsub[ x ≔ nvar x ] e ≡ e
idnsub x (nat n)  = refl
idnsub x (nvar y) with x ≟ₙᵥ y
...               | yes refl = refl
...               | no x≢y   = refl
idnsub x (suc e)  = suc & idnsub x e
idnsub x (e + f)  = _+_ & idnsub x e ⊗ idnsub x f
idnsub x (e * f)  = _*_ & idnsub x e ⊗ idnsub x f


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

idsub : ∀ x A → sub[ x ≔ nvar x ] A ≡ A
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
data _⊢_ : Context → Type → Set
  where
    -- Assumption / Hypothesis
    var : ∀ {A Γ} → Γ ∋ A
                  → Γ ⊢ A

    -- Fantasy
    lam : ∀ {A B Γ} → Γ , A ⊢ B
                    → Γ ⊢ A ⊃ B

    -- Detachment / Modus ponens
    app : ∀ {A B Γ} → Γ ⊢ A ⊃ B → Γ ⊢ A
                    → Γ ⊢ B

    -- Joining
    pair : ∀ {A B Γ} → Γ ⊢ A → Γ ⊢ B
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
    suci : ∀ {e f Γ} → Γ ⊢ e == f
                     → Γ ⊢ suc e == suc f

    -- Successor elimination
    suce : ∀ {e f Γ} → Γ ⊢ suc e == suc f
                     → Γ ⊢ e == f

    -- Induction
    induct : ∀ {x A Γ} → Γ ⊢ sub[ x ≔ 0 ] A → Γ ⊢ ∇ x ∶ A ⊃ sub[ x ≔ suc (nvar x) ] A
                       → Γ ⊢ ∇ x ∶ A

    -- Axiom 1
    ax1 : ∀ {Γ} → Γ ⊢ ∇ "a" ∶ ~ (suc "a" == 0)

    -- Axiom 2
    ax2 : ∀ {Γ} → Γ ⊢ ∇ "a" ∶ ("a" + 0) == "a"

    -- Axiom 3
    ax3 : ∀ {Γ} → Γ ⊢ ∇ "a" ∶ ∇ "b" ∶ ("a" + suc "b") == suc ("a" + "b")

    -- Axiom 4
    ax4 : ∀ {Γ} → Γ ⊢ ∇ "a" ∶ ("a" * 0) == 0

    -- Axiom 5
    ax5 : ∀ {Γ} → Γ ⊢ ∇ "a" ∶ ∇ "b" ∶ ("a" * suc "b") == ("a" * "b") + "a"


v0 : ∀ {A Γ} → Γ , A ⊢ A
v0 = var 0

v1 : ∀ {A B Γ} → Γ , A , B ⊢ A
v1 = var 1

v2 : ∀ {A B C Γ} → Γ , A , B , C ⊢ A
v2 = var 2

v3 : ∀ {A B C D Γ} → Γ , A , B , C , D ⊢ A
v3 = var 3

v4 : ∀ {A B C D E Γ} → Γ , A , B , C , D , E ⊢ A
v4 = var 4

v5 : ∀ {A B C D E F Γ} → Γ , A , B , C , D , E , F ⊢ A
v5 = var 5


ren : ∀ {A Γ Γ′} → Γ′ ⊇ Γ → Γ ⊢ A
                 → Γ′ ⊢ A
ren η (var i)           = var (renᵢ η i)
ren η (lam M)           = lam (ren (keep η) M)
ren η (app M N)         = app (ren η M) (ren η N)
ren η (pair M N)        = pair (ren η M) (ren η N)
ren η (fst M)           = fst (ren η M)
ren η (snd M)           = snd (ren η M)
ren η (dni M)           = dni (ren η M)
ren η (dne M)           = dne (ren η M)
ren η (contra M)        = contra (ren η M)
ren η (spec[ x ≔ s ] M) = spec[ x ≔ s ] (ren η M)
ren η (gen[ x ] M)      = gen[ x ] (ren η M)
ren η (sym M)           = sym (ren η M)
ren η (trans M N)       = trans (ren η M) (ren η N)
ren η (suci M)          = suci (ren η M)
ren η (suce M)          = suce (ren η M)
ren η (induct M N)      = induct (ren η M) (ren η N)
ren η ax1               = ax1
ren η ax2               = ax2
ren η ax3               = ax3
ren η ax4               = ax4
ren η ax5               = ax5

wk : ∀ {A B Γ} → Γ ⊢ A
               → Γ , B ⊢ A
wk M = ren (drop idᵣ) M


-- Carry-over / Let
define : ∀ {A C Γ} → Γ ⊢ A → Γ , A ⊢ C
                   → Γ ⊢ C
define M N = app (lam N) M


-- Contraposition II
ntra : ∀ {A B Γ} → Γ ⊢ ~ B ⊃ ~ A
                 → Γ ⊢ A ⊃ B
ntra M = lam (dne (app (wk (contra M)) (dni v0)))

-- Denial of antecendent
deny : ∀ {A C Γ} → Γ ⊢ A → Γ ⊢ ~ A
                 → Γ ⊢ C
deny M N = app (ntra (lam (wk N))) M


-- Law of excluded middle
lem : ∀ {A Γ} → Γ ⊢ A ∨ ~ A
lem = lam v0


-- Truth
TT : Type
TT = ∇ "a" ∶ ~ (suc "a" == 0)

-- Triviality
tt : ∀ {Γ} → Γ ⊢ TT
tt = ax1


-- Falsehood
FF : Type
FF = ~ TT

-- Proof of negation
ne : ∀ {A Γ} → Γ , A ⊢ FF
             → Γ ⊢ ~ A
ne M = app (contra (lam M)) (dni tt)

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
⊃→~∨ M = lam (app (wk M) (dne v0))

-- Switcheroo IV
~∨→⊃ : ∀ {A B Γ} → Γ ⊢ ~ A ∨ B
                  → Γ ⊢ A ⊃ B
~∨→⊃ M = lam (app (wk M) (dni v0))


-- NOTE: Uses REWRITE idsub
dni∇ : ∀ {x A Γ} → Γ ⊢ ∇ x ∶ A
                 → Γ ⊢ ∇ x ∶ ~ ~ A
dni∇ {x} M = gen[ x ] (dni (spec[ x ≔ nvar x ] M))

-- NOTE: Uses REWRITE idsub
dne∇ : ∀ {x A Γ} → Γ ⊢ ∇ x ∶ ~ ~ A
                 → Γ ⊢ ∇ x ∶ A
dne∇ {x} M = gen[ x ] (dne (spec[ x ≔ nvar x ] M))

dni∃ : ∀ {x A Γ} → Γ ⊢ ∃ x ∶ A
                 → Γ ⊢ ∃ x ∶ ~ ~ A
dni∃ {x} M = ne (deny (dne∇ v0) (wk M))

dne∃ : ∀ {x A Γ} → Γ ⊢ ∃ x ∶ ~ ~ A
                 → Γ ⊢ ∃ x ∶ A
dne∃ {x} M = ne (deny (dni∇ v0) (wk M))


dni∧₁ : ∀ {A B Γ} → Γ ⊢ A ∧ B
                  → Γ ⊢ ~ ~ A ∧ B
dni∧₁ M = pair (dni (fst M)) (snd M)

dne∧₁ : ∀ {A B Γ} → Γ ⊢ ~ ~ A ∧ B
                  → Γ ⊢ A ∧ B
dne∧₁ M = pair (dne (fst M)) (snd M)

dni∧₂ : ∀ {A B Γ} → Γ ⊢ A ∧ B
                  → Γ ⊢ A ∧ ~ ~ B
dni∧₂ M = pair (fst M) (dni (snd M))

dne∧₂ : ∀ {A B Γ} → Γ ⊢ A ∧ ~ ~ B
                  → Γ ⊢ A ∧ B
dne∧₂ M = pair (fst M) (dne (snd M))


dni⊃₁ : ∀ {A B Γ} → Γ ⊢ A ⊃ B
                  → Γ ⊢ ~ ~ A ⊃ B
dni⊃₁ M = lam (app (wk M) (dne v0))

dne⊃₁ : ∀ {A B Γ} → Γ ⊢ ~ ~ A ⊃ B
                  → Γ ⊢ A ⊃ B
dne⊃₁ M = lam (app (wk M) (dni v0))

dni⊃₂ : ∀ {A B Γ} → Γ ⊢ A ⊃ B
                  → Γ ⊢ A ⊃ ~ ~ B
dni⊃₂ M = lam (dni (app (wk M) v0))

dne⊃₂ : ∀ {A B Γ} → Γ ⊢ A ⊃ ~ ~ B
                  → Γ ⊢ A ⊃ B
dne⊃₂ M = lam (dne (app (wk M) v0))


swap∧ : ∀ {A B Γ} → Γ ⊢ A ∧ B
                  → Γ ⊢ B ∧ A
swap∧ M = pair (snd M) (fst M)

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
~∇→∃ M = ne (deny (dne∇ v0) (wk M))

-- De Morgan’s major law IV
∃→~∇ : ∀ {x A Γ} → Γ ⊢ ∃ x ∶ ~ A
                  → Γ ⊢ ~ (∇ x ∶ A)
∃→~∇ M = ne (deny (dni∇ v0) (wk M))


-- De Morgan’s minor law I
~∨→∧ : ∀ {A B Γ} → Γ ⊢ ~ (A ∨ B)
                  → Γ ⊢ ~ A ∧ ~ B
~∨→∧ M = pair
            (ne (deny (left v0) (wk M)))
            (ne (deny (right v0) (wk M)))

-- De Morgan’s minor law II
∧→~∨ : ∀ {A B Γ} → Γ ⊢ ~ A ∧ ~ B
                  → Γ ⊢ ~ (A ∨ B)
∧→~∨ M = ne (deny
            (app v0 (wk (fst M)))
            (wk (snd M)))

-- De Morgan’s minor law III
~∧→∨ : ∀ {A B Γ} → Γ ⊢ ~ (A ∧ B)
                  → Γ ⊢ ~ A ∨ ~ B
~∧→∨ M = lam (ne (deny
            (pair (dne v1) v0)
            (wk (wk M))))

-- De Morgan’s minor law IV
∨→~∧ : ∀ {A B Γ} → Γ ⊢ ~ A ∨ ~ B
                  → Γ ⊢ ~ (A ∧ B)
∨→~∧ M = ne (deny
            (snd v0)
            (app
              (wk M)
              (dni (fst v0))))


module Kleene where
  mutual
    K1a : ∀ {A B Γ} → Γ ⊢ A ⊃ B ⊃ A
    K1a = lam (lam v1)

    K1b : ∀ {A B C Γ} → Γ ⊢ (A ⊃ B) ⊃ (A ⊃ B ⊃ C) ⊃ A ⊃ C
    K1b = lam (lam (lam (app
            (app v1 v0)
            (app v2 v0))))

    K3 : ∀ {A B Γ} → Γ ⊢ A ⊃ B ⊃ A ∧ B
    K3 = lam (lam (pair v1 v0))

    K4a : ∀ {A B Γ} → Γ ⊢ A ∧ B ⊃ A
    K4a = lam (fst v0)

    K4b : ∀ {A B Γ} → Γ ⊢ A ∧ B ⊃ B
    K4b = lam (snd v0)

    K5a : ∀ {A B Γ} → Γ ⊢ A ⊃ A ∨ B
    K5a = lam (left v0)

    K5b : ∀ {A B Γ} → Γ ⊢ B ⊃ A ∨ B
    K5b = lam (right v0)

    woop : ∀ {A C Γ} → Γ ⊢ (A ⊃ C) ⊃ (~ A ⊃ C) ⊃ C
    woop = lam (lam (app
             (swap∨ (app
               (snd K*36)
               (pair
                 (swap∨ (dni⊃₁ v1))
                 (swap∨ (dni⊃₁ v0)))))
             (ne (deny
               (fst v0)
               (snd v0)))))

    K6 : ∀ {A B C Γ} → Γ ⊢ (A ⊃ C) ⊃ (B ⊃ C) ⊃ A ∨ B ⊃ C
    K6 = lam (lam (lam (app
           (app woop v2)
           (app (app K*2 v0) v1))))

    case : ∀ {A B C Γ} → Γ ⊢ A ∨ B → Γ , A ⊢ C → Γ , B ⊢ C
                       → Γ ⊢ C
    case M N O = app (app (app K6 (lam N)) (lam O)) M

    K7 : ∀ {A B Γ} → Γ ⊢ (A ⊃ B) ⊃ (A ⊃ ~ B) ⊃ ~ A
    K7 = lam (lam (ne (deny
           (app v2 v0)
           (app v1 v0))))

    K8 : ∀ {A Γ} → Γ ⊢ ~ ~ A ⊃ A
    K8 = lam (dne v0)

    K9a : ∀ {A B Γ} → Γ ⊢ (A ⊃ B) ⊃ (B ⊃ A) ⊃ (A ⫗ B)
    K9a = lam (lam (pair v1 v0))

    K10a : ∀ {A B Γ} → Γ ⊢ (A ⫗ B) ⊃ A ⊃ B
    K10a = lam (fst v0)

    K10b : ∀ {A B Γ} → Γ ⊢ (A ⫗ B) ⊃ B ⊃ A
    K10b = lam (snd v0)

    -- Principle of identity
    K*1 : ∀ {A Γ} → Γ ⊢ A ⊃ A
    K*1 = lam v0

    -- Chain inference
    K*2 : ∀ {A B C Γ} → Γ ⊢ (A ⊃ B) ⊃ (B ⊃ C) ⊃ A ⊃ C
    K*2 = lam (lam (lam (app v1 (app v2 v0))))

    -- Interchange of premises
    K*3 : ∀ {A B C Γ} → Γ ⊢ A ⊃ B ⊃ C ⫗ B ⊃ A ⊃ C
    K*3 = pair
            (lam (lam (lam (app (app v2 v0) v1))))
            (lam (lam (lam (app (app v2 v0) v1))))

    -- Importation and exportation
    K*4a : ∀ {A B C Γ} → Γ ⊢ A ⊃ B ⊃ C ⫗ A ∧ B ⊃ C
    K*4a = pair
             (lam (lam (app (app v1 (fst v0)) (snd v0))))
             (lam (lam (lam (app v2 (pair v1 v0)))))

    -- Denial of the antecedent
    K*10a : ∀ {A B Γ} → Γ ⊢ ~ A ⊃ A ⊃ B
    K*10a = lam (lam (deny v0 v1))

    -- Contraposition
    K*12a° : ∀ {A B Γ} → Γ ⊢ A ⊃ B ⫗ ~ B ⊃ ~ A
    K*12a° = pair
               (lam (contra v0))
               (lam (ntra v0))

    -- Reflexive property of equivalence
    K*19 : ∀ {A Γ} → Γ ⊢ A ⫗ A
    K*19 = pair K*1 K*1

    -- Symmetric property of equivalence
    K*20 : ∀ {A B Γ} → Γ ⊢ (A ⫗ B) ⫗ (B ⫗ A)
    K*20 = pair
             (lam (pair (snd v0) (fst v0)))
             (lam (pair (snd v0) (fst v0)))

    -- Transitive property of equivalence
    K*21 : ∀ {A B C Γ} → Γ ⊢ (A ⫗ B) ∧ (B ⫗ C) ⊃ (A ⫗ C)
    K*21 = lam (pair
             (lam (app
               (fst (snd v1))
               (app (fst (fst v1)) v0)))
             (lam (app
               (snd (fst v1))
               (app (snd (snd v1)) v0))))

    -- Associative law of conjunction
    K*31 : ∀ {A B C Γ} → Γ ⊢ (A ∧ B) ∧ C ⫗ A ∧ (B ∧ C)
    K*31 = pair
             (lam (pair
               (fst (fst v0))
               (pair
                 (snd (fst v0))
                 (snd v0))))
             (lam (pair
               (pair
                 (fst v0)
                 (fst (snd v0)))
               (snd (snd v0))))

    -- Associative law of disjunction
    K*32 : ∀ {A B C Γ} → Γ ⊢ (A ∨ B) ∨ C ⫗ A ∨ (B ∨ C)
    K*32 = pair
             (lam (lam (lam (app
               v2
               (app
                 (snd K*55a)
                 (pair v1 v0))))))
             (lam (lam (app
               (app
                 v1
                 (fst (app (fst K*55a) v0)))
               (snd (app (fst K*55a) v0)))))

    -- Commutative law of conjunction
    K*33 : ∀ {A B Γ} → Γ ⊢ A ∧ B ⫗ B ∧ A
    K*33 = pair
             (lam (swap∧ v0))
             (lam (swap∧ v0))

    -- Commutative law of disjunction
    K*34 : ∀ {A B Γ} → Γ ⊢ A ∨ B ⫗ B ∨ A
    K*34 = pair
             (lam (swap∨ v0))
             (lam (swap∨ v0))

    -- Distributive law of conjunction over disjunction
    K*35 : ∀ {A B C Γ} → Γ ⊢ A ∧ (B ∨ C) ⫗ (A ∧ B) ∨ (A ∧ C)
    K*35 = pair
             (lam (case
               (snd v0)
               (left (pair (fst v1) v0))
               (right (pair (fst v1) v0))))
              (lam (case
                v0
                (pair
                  (fst v0)
                  (left (snd v0)))
                (pair
                  (fst v0)
                  (right (snd v0)))))

    -- Distributive law of disjunction over conjunction
    K*36 : ∀ {A B C Γ} → Γ ⊢ A ∨ (B ∧ C) ⫗ (A ∨ B) ∧ (A ∨ C)
    K*36 = pair
             (lam (pair
               (lam (fst (app v1 v0)))
               (lam (snd (app v1 v0)))))
             (lam (lam (pair
               (app (fst v1) v0)
               (app (snd v1) v0))))

    -- Idempotent law of conjunction
    K*37 : ∀ {A Γ} → Γ ⊢ A ∧ A ⫗ A
    K*37 = pair
             (lam (fst v0))
             (lam (pair v0 v0))

    -- Idempotent law of disjunction
    K*38 : ∀ {A Γ} → Γ ⊢ A ∨ A ⫗ A
    K*38 = pair
             (ntra (lam (ne (deny (app v0 v1) v1))))
             (lam (left v0))

    -- Elimination law of conjunction over disjunction
    K*39 : ∀ {A B Γ} → Γ ⊢ A ∧ (A ∨ B) ⫗ A
    K*39 = pair
             (lam (fst v0))
             (lam (pair v0 (left v0)))

    -- Elimination law of disjunction over conjunction
    K*40 : ∀ {A B Γ} → Γ ⊢ A ∨ (A ∧ B) ⫗ A
    K*40 = pair
             (ntra (lam (ne (deny (fst (app v0 v1)) v1))))
             (lam (lam (deny v1 v0)))

    -- Law of double negation
    K*49° : ∀ {A Γ} → Γ ⊢ ~ ~ A ⫗ A
    K*49° = pair
              (lam (dne v0))
              (lam (dni v0))

    -- Denial of contradiction
    K*50 : ∀ {A Γ} → Γ ⊢ ~ (A ∧ ~ A)
    K*50 = ne (deny (fst v0) (snd v0))

    -- Law of the excluded middle
    K*51° : ∀ {A Γ} → Γ ⊢ A ∨ ~ A
    K*51° = lem

    -- De Morgan’s law I
    K*55a : ∀ {A B Γ} → Γ ⊢ ~ (A ∨ B) ⫗ ~ A ∧ ~ B
    K*55a = pair
              (lam (pair
                (ne (deny (left v0) v1))
                (ne (deny (right v0) v1))))
              (lam (ne (deny
                (app v0 (fst v1))
                (snd v1))))

    -- De Morgan’s law II
    K*55b° : ∀ {A B Γ} → Γ ⊢ ~ (A ∧ B) ⫗ ~ A ∨ ~ B
    K*55b° = pair
               (lam (lam (ne (deny (pair (dne v1) v0) v2))))
               (lam (ne (deny
                 (snd v0)
                 (app v1 (dni (fst v0))))))

    -- Negation of an implication
    K*55c° : ∀ {A B Γ} → Γ ⊢ ~ (A ⊃ B) ⫗ A ∧ ~ B
    K*55c° = pair
               (ntra (lam (dni (lam (dne (app
                 (app (fst K*55b°) v1)
                 (dni v0)))))))
               (lam (ne (deny
                 (app v0 (fst v1))
                 (snd v1))))

    -- Expression for disjunction in terms of conjunction
    K*56° : ∀ {A B Γ} → Γ ⊢ A ∨ B ⫗ ~ (~ A ∧ ~ B)
    K*56° = pair
              (lam (ne (deny v1 (app (snd K*55a) v0))))
              (ntra (lam (dni (app (fst K*55a) v0))))

    -- Expression for conjunction in terms of disjunction
    K*57° : ∀ {A B Γ} → Γ ⊢ A ∧ B ⫗ ~ (~ A ∨ ~ B)
    K*57° = pair
              (lam (app
                (snd K*55a)
                (pair
                  (dni (fst v0))
                  (dni (snd v0)))))
              (lam (pair
                (dne (fst (app (fst K*55a) v0)))
                (dne (snd (app (fst K*55a) v0)))))

    -- Expression for implication in terms of conjunction
    K*58° : ∀ {A B Γ} → Γ ⊢ A ⊃ B ⫗ ~ (A ∧ ~ B)
    K*58° = pair
              (lam (app
                (snd K*55b°)
                (lam (dni (app v1 (dne v0))))))
              (lam (lam (dne (app
                (app (fst K*55b°) v1)
                (dni v0)))))

    -- Expression for implication in terms of disjunction
    K*59° : ∀ {A B Γ} → Γ ⊢ A ⊃ B ⫗ ~ A ∨ B
    K*59° = pair
              (lam (lam (app v1 (dne v0))))
              (lam (lam (app v1 (dni v0))))

    -- Expression for conjunction in terms of implication
    K*60° : ∀ {A B Γ} → Γ ⊢ A ∧ B ⫗ ~ (A ⊃ ~ B)
    K*60° = pair
              (lam (app
                (snd K*55c°)
                (pair (fst v0) (dni (snd v0)))))
              (lam (pair
                (fst (app (fst K*55c°) v0))
                (dne (snd (app (fst K*55c°) v0)))))

    -- Expression for disjunction in terms of implication
    K*61° : ∀ {A B Γ} → Γ ⊢ A ∨ B ⫗ ~ A ⊃ B
    K*61° = pair
              (lam (lam (app v1 v0)))
              (lam (lam (app v1 v0)))

    -- Expression for equivalence in terms of conjunction of implications
    K*62° : ∀ {A B Γ} → Γ ⊢ (A ⫗ B) ⫗ (A ⊃ B) ∧ (B ⊃ A)
    K*62° = pair K*1 K*1


module VonEitzen where
  -- Equality is reflexive
  th1 : ∀ {Γ} → Γ ⊢ ∇ "a" ∶ "a" == "a"
  th1 = gen[ "a" ] (trans
          (sym (spec[ "a" ≔ "a" ] ax2))
          (spec[ "a" ≔ "a" ] ax2))

  th2 : ∀ {Γ} → Γ ⊢ ∇ "a" ∶ ~ (suc "a" == "a")
  th2 = induct
          (spec[ "a" ≔ 0 ] ax1)
          (gen[ "a" ] (contra (lam (suce v0))))

  -- Only 0 has no predecessor
  th3 : ∀ {Γ} → Γ ⊢ ∇ "a" ∶ ∇ "b" ∶ ~ (suc "b" == "a") ⊃ "a" == 0
  th3 = induct
          (gen[ "b" ] (lam (spec[ "a" ≔ 0 ] th1)))
          (gen[ "a" ] (lam (gen[ "b" ] (lam (dne (app
            (contra (lam (spec[ "a" ≔ suc "a" ] th1)))
            (spec[ "b" ≔ "a" ] (gen[ "b" ] v0))))))))

  -- The result of addition is 0 only if both arguments are 0
  th4 : ∀ {Γ} → Γ ⊢ ∇ "a" ∶ ∇ "b" ∶ ("a" + "b") == 0 ⊃ ("a" == 0 ∧ "b" == 0)
  th4 = gen[ "a" ] (induct
          (lam (pair
            (trans (sym (spec[ "a" ≔ "a" ] ax2)) v0)
            (spec[ "a" ≔ 0 ] th1)))
          (gen[ "b" ] (lam (lam (dne (app
            (contra (lam (app
              (contra (lam (trans
                (sym (spec[ "b" ≔ "b" ] (spec[ "a" ≔ "a" ] ax3)))
                v2)))
              (spec[ "a" ≔ "a" + "b" ] ax1))))
            (dni v0)))))))

  -- 0 is also left-neutral in addition
  th5 : ∀ {Γ} → Γ ⊢ ∇ "a" ∶ (0 + "a") == "a"
  th5 = induct
          (spec[ "a" ≔ 0 ] ax2)
          (gen[ "a" ] (lam (trans
            (spec[ "b" ≔ "a" ] (spec[ "a" ≔ 0 ] ax3))
            (suci v0))))

  th6 : ∀ {Γ} → Γ ⊢ ∇ "a" ∶ ∇ "b" ∶ (suc "a" + "b") == suc ("a" + "b")
  th6 = gen[ "a" ] (induct
          (trans
            (spec[ "a" ≔ suc "a" ] ax2)
            (suci (sym (spec[ "a" ≔ "a" ] ax2))))
          (gen[ "b" ] (lam (trans
            (trans
              (spec[ "b" ≔ "b" ] (spec[ "a" ≔ suc "a" ] ax3))
              (suci v0))
            (sym (suci (spec[ "b" ≔ "b" ] (spec[ "a" ≔ "a" ] ax3))))))))

  th7 : ∀ {Γ} → Γ ⊢ ∇ "a" ∶ ∇ "b" ∶ ("a" + suc "b") == (suc "a" + "b")
  th7 = gen[ "a" ] (gen[ "b" ] (trans
          (spec[ "b" ≔ "b" ] (spec[ "a" ≔ "a" ] ax3))
          (sym (spec[ "b" ≔ "b" ] (spec[ "a" ≔ "a" ] th6)))))

  -- Addition is commutative
  th8 : ∀ {Γ} → Γ ⊢ ∇ "a" ∶ ∇ "b" ∶ ("a" + "b") == ("b" + "a")
  th8 = gen[ "a" ] (induct
          (trans
            (spec[ "a" ≔ "a" ] ax2)
            (sym (spec[ "a" ≔ "a" ] th5)))
          (gen[ "b" ] (lam (trans
            (trans
              (spec[ "b" ≔ "b" ] (spec[ "a" ≔ "a" ] ax3))
              (suci v0))
            (sym (spec[ "c" ≔ "b" ] (gen[ "c" ]
              (spec[ "b" ≔ "a" ] (spec[ "a" ≔ "c" ] th6)))))))))

  -- Addition is a function in the first argument
  th9 : ∀ {Γ} → Γ ⊢ ∇ "a" ∶ ∇ "b" ∶ ∇ "c" ∶ "a" == "b" ⊃ ("a" + "c") == ("b" + "c")
  th9 = define
          (spec[ "b" ≔ "c" ] (spec[ "a" ≔ "a" ] ax3))
          (gen[ "a" ] (gen[ "b" ] (induct
            (lam (trans
              (trans (spec[ "a" ≔ "a" ] ax2) v0)
              (sym (spec[ "a" ≔ "b" ] ax2))))
            (gen[ "c" ] (lam (lam (trans
              (trans v2 (suci (app v1 v0)))
              (sym (spec[ "a" ≔ "b" ] (gen[ "a" ] v2))))))))))

  -- Addition is a function in both arguments
  th10 : ∀ {Γ} → Γ ⊢ ∇ "a" ∶ ∇ "b" ∶ ∇ "c" ∶ ∇ "d" ∶ "a" == "c" ∧ "b" == "d" ⊃ ("a" + "b") == ("c" + "d")
  th10 = define
           (spec[ "b" ≔ "d" ] (spec[ "a" ≔ "a" ] th9))
           (define
             (spec[ "a" ≔ "c" ] th8)
             (gen[ "a" ] (gen[ "b" ] (gen[ "c" ] (gen[ "d" ] (lam (trans
               (trans
                 (trans
                   (app
                     (spec[ "d" ≔ "c" ] (gen[ "d" ] (spec[ "c" ≔ "b" ] v2)))
                     (fst v0))
                   (spec[ "b" ≔ "b" ] v1))
                 (app
                   (spec[ "a" ≔ "b" ] (gen[ "a" ] (spec[ "c" ≔ "c" ] v2)))
                   (snd v0)))
               (sym (spec[ "b" ≔ "d" ] v1)))))))))

  -- Axiom 2 in functional interpretation
  th11 : ∀ {Γ} → Γ ⊢ ∇ "a" ∶ ∇ "b" ∶ "b" == 0 ⊃ ("a" + "b") == "a"
  th11 = gen[ "a" ] (gen[ "b" ] (lam (trans
           (app
             (spec[ "d" ≔ 0 ] (spec[ "c" ≔ "a" ]
               (spec[ "b" ≔ "b" ] (spec[ "a" ≔ "c" ] th10))))
             (pair (spec[ "a" ≔ "a" ] th1) v0))
           (spec[ "a" ≔ "a" ] ax2))))

  -- Addition is associative
  th12 : ∀ {Γ} → Γ ⊢ ∇ "a" ∶ ∇ "b" ∶ ∇ "c" ∶ ("a" + ("b" + "c")) == (("a" + "b") + "c")
  th12 = define
           (spec[ "a" ≔ "a" ] th6)
           (gen[ "a" ] (gen[ "b" ] (gen[ "c" ] (spec[ "a" ≔ "a" ] (induct
             (trans
               (spec[ "a" ≔ "b" + "c" ] th5)
               (app
                 (spec[ "c" ≔ "c" ] (spec[ "a" ≔ "b" ] (gen[ "a" ]
                   (spec[ "b" ≔ 0 + "a" ] (spec[ "a" ≔ "a" ] th9)))))
                 (sym (spec[ "a" ≔ "b" ] th5))))
             (gen[ "a" ] (lam (trans
               (trans
                 (spec[ "b" ≔ "b" + "c" ] v1)
                 (suci v0))
               (sym (trans
                 (app
                   (spec[ "d" ≔ "b" ] (gen[ "d" ] (spec[ "c" ≔ "c" ]
                     (spec[ "b" ≔ suc ("a" + "d") ] (spec[ "a" ≔ suc "a" + "d" ] th9)))))
                   (spec[ "b" ≔ "b" ] v1))
                 (spec[ "a" ≔ "a" + "b" ] (gen[ "a" ] (spec[ "b" ≔ "c" ] v1)))))))))))))

  -- 0 is also left-zero in multiplication
  th13 : ∀ {Γ} → Γ ⊢ ∇ "a" ∶ (0 * "a") == 0
  th13 = induct
           (spec[ "a" ≔ 0 ] ax4)
           (gen[ "a" ] (lam (trans
             (trans
               (spec[ "b" ≔ "a" ] (spec[ "a" ≔ 0 ] ax5))
               (spec[ "a" ≔ 0 * "a" ] ax2))
             v0)))

  -- The result of multiplication is 0 only if an argument is 0
  th14 : ∀ {Γ} → Γ ⊢ ∇ "a" ∶ ∇ "b" ∶ ("a" * "b") == 0 ⊃ ~ (~ ("a" == 0) ∧ ~ ("b" == 0))
  th14 = gen[ "a" ] (induct
           (lam (app
             (contra (lam (snd v0)))
             (dni (spec[ "a" ≔ 0 ] th1))))
           (gen[ "b" ] (lam (lam (app
             (contra (lam (fst v0)))
             (dni (snd (app
               (spec[ "c" ≔ "b" ] (gen[ "c" ]
                 (spec[ "b" ≔ "a" ] (spec[ "a" ≔ "b" * "c" ] th4))))
               (trans
                 (sym (spec[ "b" ≔ "b" ] (spec[ "a" ≔ "a" ] ax5)))
                 v0)))))))))
