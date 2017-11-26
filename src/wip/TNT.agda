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
infixl 18 _+_
infixl 19 _*_
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

-- TODO: substitution of variable by itself must be identity
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
infixl 9 _$_
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


v₀ : ∀ {A Γ} → Γ , A ⊢ A
v₀ = var zero

v₁ : ∀ {A B Γ} → Γ , A , B ⊢ A
v₁ = var (suc zero)

v₂ : ∀ {A B C Γ} → Γ , A , B , C ⊢ A
v₂ = var (suc (suc zero))


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

wk : ∀ {A B Γ} → Γ ⊢ A
               → Γ , B ⊢ A
wk M = ren (drop idᵣ) M


-- Contraposition II
uncontrapos : ∀ {A B Γ} → Γ ⊢ ~ B ⊃ ~ A
                        → Γ ⊢ A ⊃ B
uncontrapos M = lam (dne (wk (contrapos M) $ dni v₀))

predeny : ∀ {A C Γ} → Γ ⊢ A ⊃ ~ A ⊃ C
predeny = lam (uncontrapos (lam (dni v₁)))

deny : ∀ {A C Γ} → Γ ⊢ A → Γ ⊢ ~ A
                 → Γ ⊢ C
deny M N = predeny $ M $ N


-- Law of excluded middle
lem : ∀ {A Γ} → Γ ⊢ A ∨ ~ A
lem = lam v₀


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
efq M = abort (wk M)


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
⊃→~∨ M = lam (wk M $ dne v₀)

-- Switcheroo IV
~∨→⊃ : ∀ {A B Γ} → Γ ⊢ ~ A ∨ B
                  → Γ ⊢ A ⊃ B
~∨→⊃ M = lam (wk M $ dni v₀)


dni∇ : ∀ {x A Γ} → Γ ⊢ ∇ x ∶ A
                 → Γ ⊢ ∇ x ∶ ~ ~ A
dni∇ {x} M = gen[ x ] (dni (spec[ x ≔ nvar x ] M))

dne∇ : ∀ {x A Γ} → Γ ⊢ ∇ x ∶ ~ ~ A
                 → Γ ⊢ ∇ x ∶ A
dne∇ {x} M = gen[ x ] (dne (spec[ x ≔ nvar x ] M))

-- DeMorgan’s major law I
∇→~∃ : ∀ {x A Γ} → Γ ⊢ ∇ x ∶ ~ A
                  → Γ ⊢ ~ (∃ x ∶ A)
∇→~∃ M = dni M

-- DeMorgan’s major law II
~∃→∇ : ∀ {x A Γ} → Γ ⊢ ~ (∃ x ∶ A)
                  → Γ ⊢ ∇ x ∶ ~ A
~∃→∇ M = dne M


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
dni⊃₁ M = lam (wk M $ dne v₀)

dne⊃₁ : ∀ {A B Γ} → Γ ⊢ ~ ~ A ⊃ B
                  → Γ ⊢ A ⊃ B
dne⊃₁ M = lam (wk M $ dni v₀)

dni⊃₂ : ∀ {A B Γ} → Γ ⊢ A ⊃ B
                  → Γ ⊢ A ⊃ ~ ~ B
dni⊃₂ M = lam (dni (wk M $ v₀))

dne⊃₂ : ∀ {A B Γ} → Γ ⊢ A ⊃ ~ ~ B
                  → Γ ⊢ A ⊃ B
dne⊃₂ M = lam (dne (wk M $ v₀))


dni∨₁ : ∀ {A B Γ} → Γ ⊢ A ∨ B
                  → Γ ⊢ ~ ~ A ∨ B
dni∨₁ M = dni⊃₁ M

dne∨₁ : ∀ {A B Γ} → Γ ⊢ ~ ~ A ∨ B
                  → Γ ⊢ A ∨ B
dne∨₁ M = dne⊃₁ M

dni∨₂ : ∀ {A B Γ} → Γ ⊢ A ∨ B
                  → Γ ⊢ A ∨ ~ ~ B
dni∨₂ M = dni⊃₂ M

dne∨₂ : ∀ {A B Γ} → Γ ⊢ A ∨ ~ ~ B
                  → Γ ⊢ A ∨ B
dne∨₂ M = dne⊃₂ M


swap∧ : ∀ {A B Γ} → Γ ⊢ A ∧ B
                  → Γ ⊢ B ∧ A
swap∧ M = snd M , fst M

swap∨ : ∀ {A B Γ} → Γ ⊢ A ∨ B
                  → Γ ⊢ B ∨ A
swap∨ M = dne∨₂ (contrapos M)


-- Disjunction introduction II
right : ∀ {A B Γ} → Γ ⊢ B
                  → Γ ⊢ A ∨ B
right M = lam (wk M)

-- Disjunction introduction I
left : ∀ {A B Γ} → Γ ⊢ A
                 → Γ ⊢ A ∨ B
left M = swap∨ (right M)


module Kleene where
  mutual
    K1a : ∀ {A B Γ} → Γ ⊢ A ⊃ B ⊃ A
    K1a = lam (lam v₁)

    K1b : ∀ {A B C Γ} → Γ ⊢ (A ⊃ B) ⊃ (A ⊃ B ⊃ C) ⊃ A ⊃ C
    K1b = lam (lam (lam (v₁ $ v₀ $ (v₂ $ v₀))))

    K3 : ∀ {A B Γ} → Γ ⊢ A ⊃ B ⊃ A ∧ B
    K3 = lam (lam (v₁ , v₀))

    K4a : ∀ {A B Γ} → Γ ⊢ A ∧ B ⊃ A
    K4a = lam (fst v₀)

    K4b : ∀ {A B Γ} → Γ ⊢ A ∧ B ⊃ B
    K4b = lam (snd v₀)

    K5a : ∀ {A B Γ} → Γ ⊢ A ⊃ A ∨ B
    K5a = lam (left v₀)

    K5b : ∀ {A B Γ} → Γ ⊢ B ⊃ A ∨ B
    K5b = lam (right v₀)

    woop : ∀ {A C Γ} → Γ ⊢ (A ⊃ C) ⊃ (~ A ⊃ C) ⊃ C
    woop = lam (lam (swap∨ (snd K*36 $ (swap∨ (dni⊃₁ v₁) , swap∨ (dni⊃₁ v₀))) $ ne (deny (fst v₀) (snd v₀))))

    K6 : ∀ {A B C Γ} → Γ ⊢ (A ⊃ C) ⊃ (B ⊃ C) ⊃ A ∨ B ⊃ C
    K6 = lam (lam (lam (woop $ v₂ $ (K*2 $ v₀ $ v₁))))

    K7 : ∀ {A B Γ} → Γ ⊢ (A ⊃ B) ⊃ (A ⊃ ~ B) ⊃ ~ A
    K7 = lam (lam (ne (deny (v₂ $ v₀) (v₁ $ v₀))))

    K8 : ∀ {A Γ} → Γ ⊢ ~ ~ A ⊃ A
    K8 = lam (dne v₀)

    K9a : ∀ {A B Γ} → Γ ⊢ (A ⊃ B) ⊃ (B ⊃ A) ⊃ (A ⫗ B)
    K9a = lam (lam (v₁ , v₀))

    K10a : ∀ {A B Γ} → Γ ⊢ (A ⫗ B) ⊃ A ⊃ B
    K10a = lam (fst v₀)

    K10b : ∀ {A B Γ} → Γ ⊢ (A ⫗ B) ⊃ B ⊃ A
    K10b = lam (snd v₀)

    -- Principle of identity
    K*1 : ∀ {A Γ} → Γ ⊢ A ⊃ A
    K*1 = lam v₀

    -- Chain inference
    K*2 : ∀ {A B C Γ} → Γ ⊢ (A ⊃ B) ⊃ (B ⊃ C) ⊃ A ⊃ C
    K*2 = lam (lam (lam (v₁ $ (v₂ $ v₀))))

    -- Interchange of premises
    K*3 : ∀ {A B C Γ} → Γ ⊢ A ⊃ B ⊃ C ⫗ B ⊃ A ⊃ C
    K*3 = lam (lam (lam (v₂ $ v₀ $ v₁))) ,
          lam (lam (lam (v₂ $ v₀ $ v₁)))

    -- Importation and exportation
    K*4a : ∀ {A B C Γ} → Γ ⊢ A ⊃ B ⊃ C ⫗ A ∧ B ⊃ C
    K*4a = lam (lam (v₁ $ fst v₀ $ snd v₀)) ,
           lam (lam (lam (v₂ $ (v₁ , v₀))))

    -- Denial of the antecedent
    K*10a : ∀ {A B Γ} → Γ ⊢ ~ A ⊃ A ⊃ B
    K*10a = lam (lam (deny v₀ v₁))

    -- Contraposition
    K*12a° : ∀ {A B Γ} → Γ ⊢ A ⊃ B ⫗ ~ B ⊃ ~ A
    K*12a° = lam (contrapos v₀) , lam (uncontrapos v₀)

    -- Reflexive property of equivalence
    K*19 : ∀ {A Γ} → Γ ⊢ A ⫗ A
    K*19 = K*1 , K*1

    -- Symmetric property of equivalence
    K*20 : ∀ {A B Γ} → Γ ⊢ (A ⫗ B) ⫗ (B ⫗ A)
    K*20 = lam (snd v₀ , fst v₀) ,
           lam (snd v₀ , fst v₀)

    -- Transitive property of equivalence
    K*21 : ∀ {A B C Γ} → Γ ⊢ (A ⫗ B) ∧ (B ⫗ C) ⊃ (A ⫗ C)
    K*21 = lam (lam (fst (snd v₁) $ (fst (fst v₁) $ v₀)) ,
                lam (snd (fst v₁) $ (snd (snd v₁) $ v₀)))

    -- Associative law of conjunction
    K*31 : ∀ {A B C Γ} → Γ ⊢ (A ∧ B) ∧ C ⫗ A ∧ (B ∧ C)
    K*31 = lam (fst (fst v₀) , (snd (fst v₀) , snd v₀)) ,
           lam ((fst v₀ , fst (snd v₀)) , snd (snd v₀))

    -- Associative law of disjunction
    K*32 : ∀ {A B C Γ} → Γ ⊢ (A ∨ B) ∨ C ⫗ A ∨ (B ∨ C)
    K*32 = {!!} ,
           {!!}

    -- Commutative law of conjunction
    K*33 : ∀ {A B Γ} → Γ ⊢ A ∧ B ⫗ B ∧ A
    K*33 = lam (swap∧ v₀) , lam (swap∧ v₀)

    -- Commutative law of disjunction
    K*34 : ∀ {A B Γ} → Γ ⊢ A ∨ B ⫗ B ∨ A
    K*34 = lam (swap∨ v₀) , lam (swap∨ v₀)

    -- Distributive law of conjunction over disjunction
    K*35 : ∀ {A B C Γ} → Γ ⊢ A ∧ (B ∨ C) ⫗ (A ∧ B) ∨ (A ∧ C)
    K*35 = {!!} ,
           {!!}

    -- Distributive law of disjunction over conjunction
    K*36 : ∀ {A B C Γ} → Γ ⊢ A ∨ (B ∧ C) ⫗ (A ∨ B) ∧ (A ∨ C)
    K*36 = lam (lam (fst (v₁ $ v₀)) , lam (snd (v₁ $ v₀))) ,
           lam (lam (fst v₁ $ v₀ , snd v₁ $ v₀))

    -- Idempotent law of conjunction
    K*37 : ∀ {A Γ} → Γ ⊢ A ∧ A ⫗ A
    K*37 = lam (fst v₀) , lam (v₀ , v₀)

    -- Idempotent law of disjunction
    K*38 : ∀ {A Γ} → Γ ⊢ A ∨ A ⫗ A
    K*38 = uncontrapos (lam (ne (deny (v₀ $ v₁) v₁))) ,
           lam (left v₀)

    -- Elimination law of conjunction over disjunction
    K*39 : ∀ {A B Γ} → Γ ⊢ A ∧ (A ∨ B) ⫗ A
    K*39 = lam (fst v₀) , lam (v₀ , left v₀)

    -- Elimination law of disjunction over conjunction
    K*40 : ∀ {A B Γ} → Γ ⊢ A ∨ (A ∧ B) ⫗ A
    K*40 = uncontrapos (lam (ne (deny (fst (v₀ $ v₁)) v₁))) ,
           lam (lam (deny v₁ v₀))

    -- Law of double negation
    K*49° : ∀ {A Γ} → Γ ⊢ ~ ~ A ⫗ A
    K*49° = lam (dne v₀) , lam (dni v₀)

    -- Denial of contradiction
    K*50 : ∀ {A Γ} → Γ ⊢ ~ (A ∧ ~ A)
    K*50 = ne (deny (fst v₀) (snd v₀))

    -- Law of the excluded middle
    K*51° : ∀ {A Γ} → Γ ⊢ A ∨ ~ A
    K*51° = lem

    -- De Morgan’s law I
    K*55a : ∀ {A B Γ} → Γ ⊢ ~ (A ∨ B) ⫗ ~ A ∧ ~ B
    K*55a = lam (ne (deny (left v₀) v₁) , ne (deny (right v₀) v₁)) ,
            lam (ne (deny (v₀ $ fst v₁) (snd v₁)))

    -- De Morgan’s law II
    K*55b° : ∀ {A B Γ} → Γ ⊢ ~ (A ∧ B) ⫗ ~ A ∨ ~ B
    K*55b° = lam (lam (ne (deny (dne v₁ , v₀) v₂))) ,
             lam (ne (deny (snd v₀) (v₁ $ dni (fst v₀))))

    -- Negation of an implication
    K*55c° : ∀ {A B Γ} → Γ ⊢ ~ (A ⊃ B) ⫗ A ∧ ~ B
    K*55c° = uncontrapos (lam (dni (lam (dne (fst K*55b° $ v₁ $ dni v₀))))) ,
             lam (ne (deny (v₀ $ fst v₁) (snd v₁)))

    -- Expression for disjunction in terms of conjunction
    K*56° : ∀ {A B Γ} → Γ ⊢ A ∨ B ⫗ ~ (~ A ∧ ~ B)
    K*56° = lam (ne (deny v₁ (snd K*55a $ v₀))) ,
            uncontrapos (lam (dni (fst K*55a $ v₀)))

    -- Expression for conjunction in terms of disjunction
    K*57° : ∀ {A B Γ} → Γ ⊢ A ∧ B ⫗ ~ (~ A ∨ ~ B)
    K*57° = lam (snd K*55a $ (dni (fst v₀) , dni (snd v₀))) ,
            lam (dne (fst (fst K*55a $ v₀)) , dne (snd (fst K*55a $ v₀)))

    -- Expression for implication in terms of conjunction
    K*58° : ∀ {A B Γ} → Γ ⊢ A ⊃ B ⫗ ~ (A ∧ ~ B)
    K*58° = lam (snd K*55b° $ lam (dni (v₁ $ dne v₀))) ,
            lam (lam (dne (fst K*55b° $ v₁ $ dni v₀)))

    -- Expression for implication in terms of disjunction
    K*59° : ∀ {A B Γ} → Γ ⊢ A ⊃ B ⫗ ~ A ∨ B
    K*59° = lam (lam (v₁ $ dne v₀)) ,
            lam (lam (v₁ $ dni v₀))

    -- Expression for conjunction in terms of implication
    K*60° : ∀ {A B Γ} → Γ ⊢ A ∧ B ⫗ ~ (A ⊃ ~ B)
    K*60° = lam (snd K*55c° $ (fst v₀ , dni (snd v₀))) ,
            lam (fst (fst K*55c° $ v₀) , dne (snd (fst K*55c° $ v₀)))

    -- Expression for disjunction in terms of implication
    K*61° : ∀ {A B Γ} → Γ ⊢ A ∨ B ⫗ ~ A ⊃ B
    K*61° = lam (lam (v₁ $ v₀)) ,
            lam (lam (v₁ $ v₀))

    -- Expression for equivalence in terms of conjunction of implications
    K*62° : ∀ {A B Γ} → Γ ⊢ (A ⫗ B) ⫗ (A ⊃ B) ∧ (B ⊃ A)
    K*62° = K*1 , K*1


-- -- TODO: what the fork?
-- contradic : ∀ {A Γ} → Γ ⊢ A → Γ ⊢ ~ A
--                     → Γ ⊢ FF
-- contradic M N = dne⊃₁ (contrapos (lam (wk lem″))) $ (M , N)


-- dni∃ : ∀ {x A Γ} → Γ ⊢ ∃ x ∶ A
--                  → Γ ⊢ ∃ x ∶ ~ ~ A
-- dni∃ {x} M = ne (contradic (dne∇ v₀)
--                            (wk M))

-- dne∃ : ∀ {x A Γ} → Γ ⊢ ∃ x ∶ ~ ~ A
--                  → Γ ⊢ ∃ x ∶ A
-- dne∃ {x} M = ne (contradic (dni∇ v₀)
--                            (wk M))


-- -- DeMorgan’s major law III
-- ~∇→∃ : ∀ {x A Γ} → Γ ⊢ ~ (∇ x ∶ A)
--                   → Γ ⊢ ∃ x ∶ ~ A
-- ~∇→∃ M = ne (contradic (dne∇ v₀)
--                         (wk M))

-- -- DeMorgan’s major law IV
-- ∃→~∇ : ∀ {x A Γ} → Γ ⊢ ∃ x ∶ ~ A
--                   → Γ ⊢ ~ (∇ x ∶ A)
-- ∃→~∇ M = ne (contradic (dni∇ v₀)
--                         (wk M))


-- -- -- Disjunction introduction I
-- -- left : ∀ {A B Γ} → Γ ⊢ A
-- --                  → Γ ⊢ A ∨ B
-- -- left M = lam (efq (contradic (wk M)
-- --                              v₀))


-- DeMorgan’s minor law I
∧→~∨ : ∀ {A B Γ} → Γ ⊢ ~ A ∧ ~ B
                  → Γ ⊢ ~ (A ∨ B)
∧→~∨ M = ne (deny (v₀ $ wk (fst M)) (wk (snd M)))

-- -- DeMorgan’s minor law II
-- ~∨→∧ : ∀ {A B Γ} → Γ ⊢ ~ (A ∨ B)
--                   → Γ ⊢ ~ A ∧ ~ B
-- ~∨→∧ M = ne (contradic (left v₀)
--                         (wk M)) ,
--           ne (contradic (right v₀)
--                         (wk M))

-- -- DeMorgan’s minor law III
-- ~∧→∨ : ∀ {A B Γ} → Γ ⊢ ~ (A ∧ B)
--                   → Γ ⊢ ~ A ∨ ~ B
-- ~∧→∨ M = contrapos {!!}
-- -- ~∧→∨ M = lam (ne (contradic (dne v₁ , v₀)
-- --                              (wk (wk M))))

-- -- DeMorgan’s minor law IV
-- ∨→~∧ : ∀ {A B Γ} → Γ ⊢ ~ A ∨ ~ B
--                   → Γ ⊢ ~ (A ∧ B)
-- ∨→~∧ M = {!!}
-- -- ∨→~∧ M = ne (contradic (snd v₀)
-- --                         (wk M $ dni (fst v₀))


-- lem‴ : ∀ {A Γ} → Γ ⊢ ~ (A ∧ ~ A)
-- lem‴ = ∨→~∧ lem


-- -- Disjunction elimination
-- case : ∀ {A B C Γ} → Γ ⊢ A ∨ B → Γ , A ⊢ C → Γ , B ⊢ C
--                    → Γ ⊢ C
-- case M N O = {!⊃→~∨ (lam O)!}

-- -- ∨→~∧ (dni∨₁ (dni∨₂ M))
-- -- A ∨ B
-- -- ~ ~ A ∨ ~ ~ B
-- -- ~ (~ A ∧ ~ B)

-- -- ⊃→~∨ (lam N)
-- -- ~ A ∨ C
-- -- ~ A ∨ ~ ~ C
-- -- ~ (A ∧ ~ C)

-- -- ⊃→~∨ (lam O)
-- -- ~ B ∨ C
-- -- ~ B ∨ ~ ~ C
-- -- ~ (B ∧ ~ C)


-- -- Equality is reflexive
-- thm₁ : ∀ {Γ} → Γ ⊢ ∇ "a" ∶ "a" == "a"
-- thm₁ = gen[ "a" ] (trans (sym (spec[ "a" ≔ "a" ] axm₂))
--                          (spec[ "a" ≔ "a" ] axm₂))

-- thm₂ : ∀ {Γ} → Γ ⊢ ∇ "a" ∶ ~ (suc "a" == "a")
-- thm₂ = induc (spec[ "a" ≔ 0 ] axm₁)
--              (gen[ "a" ] (contrapos (lam (suce v₀))))

-- -- Only 0 has no predecessor
-- thm₃ : ∀ {Γ} → Γ ⊢ ∇ "a" ∶ ∇ "b" ∶ ~ (suc "b" == "a" ⊃ "a" == 0)
-- thm₃ = induc {!!}
--              {!!}
