module TNT2 where

open import Prelude public


data NVar : Set
  where
    a  : NVar
    b  : NVar
    c  : NVar
    d  : NVar
    e  : NVar
    _′ : NVar → NVar

NContext : Set
NContext = List NVar

data NExp : NContext → Set
  where
    nat  : ∀ {ξ} → Nat → NExp ξ
    nvar : ∀ {ξ} → (x : NVar) {{_ : ξ ∋ x}} → NExp ξ
    suc  : ∀ {ξ} → NExp ξ → NExp ξ
    _+_  : ∀ {ξ} → NExp ξ → NExp ξ → NExp ξ
    _*_  : ∀ {ξ} → NExp ξ → NExp ξ → NExp ξ

{-# DISPLAY nat n = n #-}

instance
  nexpIsNumber : ∀ {ξ} → Number (NExp ξ)
  nexpIsNumber =
    record
      { Constraint = λ n → ⊤
      ; fromNat    = λ n → nat n
      }

nexp-ren : ∀ {ξ ξ′} → ξ′ ⊇ ξ → NExp ξ
                    → NExp ξ′
nexp-ren η (nat n)        = nat n
nexp-ren η (nvar x {{i}}) = nvar x {{renᵢ η i}}
nexp-ren η (suc M)        = suc (nexp-ren η M)
nexp-ren η (M + N)        = nexp-ren η M + nexp-ren η N
nexp-ren η (M * N)        = nexp-ren η M * nexp-ren η N

NSub : NContext → NContext → Set
NSub ξ ζ = All (λ x → NExp ξ) ζ

nsub-ren : ∀ {ξ ξ′ ζ} → ξ′ ⊇ ξ → NSub ξ ζ
                      → NSub ξ′ ζ
nsub-ren η σ = mapAll (nexp-ren η) σ

nsub-wk : ∀ {ξ ζ x} → NSub ξ ζ
                      → NSub (ξ , x) ζ
nsub-wk σ = nsub-ren (drop idᵣ) σ

nsub-lift : ∀ {ξ ζ x} → NSub ξ ζ
                      → NSub (ξ , x) (ζ , x)
nsub-lift {x = x} σ = nsub-wk σ , nvar x

nsub-id : ∀ {ξ} → NSub ξ ξ
nsub-id {∅}     = ∅
nsub-id {ξ , x} = nsub-lift nsub-id

nexp-sub : ∀ {ξ ζ} → NSub ξ ζ → NExp ζ
                   → NExp ξ
nexp-sub σ (nat n)        = nat n
nexp-sub σ (nvar x {{i}}) = lookupAll σ i
nexp-sub σ (suc M)        = suc (nexp-sub σ M)
nexp-sub σ (M + N)        = nexp-sub σ M + nexp-sub σ N
nexp-sub σ (M * N)        = nexp-sub σ M * nexp-sub σ N

data Type : NContext → Set
  where
    _==_ : ∀ {ξ} → NExp ξ → NExp ξ → Type ξ
    ~_   : ∀ {ξ} → Type ξ → Type ξ
    _∧_  : ∀ {ξ} → Type ξ → Type ξ → Type ξ
    _⊃_  : ∀ {ξ} → Type ξ → Type ξ → Type ξ
    ∇_∶_ : ∀ {ξ} → (x : NVar) → Type (ξ , x) → Type ξ

type-ren : ∀ {ξ ξ′} → ξ′ ⊇ ξ → Type ξ
                    → Type ξ′
type-ren η (M == N)  = nexp-ren η M == nexp-ren η N
type-ren η (~ A)     = ~ (type-ren η A)
type-ren η (A ∧ B)   = type-ren η A ∧ type-ren η B
type-ren η (A ⊃ B)   = type-ren η A ⊃ type-ren η B
type-ren η (∇ x ∶ A) = ∇ x ∶ type-ren (keep η) A

type-sub : ∀ {ξ ζ} → NSub ξ ζ → Type ζ
                   → Type ξ
type-sub σ (M == N)  = nexp-sub σ M == nexp-sub σ N
type-sub σ (~ A)     = ~ (type-sub σ A)
type-sub σ (A ∧ B)   = type-sub σ A ∧ type-sub σ B
type-sub σ (A ⊃ B)   = type-sub σ A ⊃ type-sub σ B
type-sub σ (∇ x ∶ A) = ∇ x ∶ type-sub (nsub-lift σ) A

_∨_ : ∀ {ξ} → Type ξ → Type ξ → Type ξ
A ∨ B = (~ A) ⊃ B

∃_∶_ : ∀ {ξ} → (x : NVar) → Type (ξ , x) → Type ξ
∃ x ∶ A = ~ (∇ x ∶ ~ A)

_⫗_ : ∀ {ξ} → Type ξ → Type ξ → Type ξ
A ⫗ B = (A ⊃ B) ∧ (B ⊃ A)

Context : NContext → Set
Context ξ = List (Type ξ)

infix  3 _⊢_
data _⊢_ {ξ} : Context ξ → Type ξ → Set
  where
    var : ∀ {A Γ} → Γ ∋ A
                  → Γ ⊢ A

    lam : ∀ {A B Γ} → Γ , A ⊢ B
                    → Γ ⊢ A ⊃ B

    app : ∀ {A B Γ} → Γ ⊢ A ⊃ B → Γ ⊢ A
                    → Γ ⊢ B

    pair : ∀ {A B Γ} → Γ ⊢ A → Γ ⊢ B
                     → Γ ⊢ A ∧ B

    fst : ∀ {A B Γ} → Γ ⊢ A ∧ B
                    → Γ ⊢ A

    snd : ∀ {A B Γ} → Γ ⊢ A ∧ B
                    → Γ ⊢ B

    dni : ∀ {A Γ} → Γ ⊢ A
                  → Γ ⊢ ~ ~ A

    dne : ∀ {A Γ} → Γ ⊢ ~ ~ A
                  → Γ ⊢ A

    contra : ∀ {A B Γ} → Γ ⊢ A ⊃ B
                       → Γ ⊢ (~ B) ⊃ (~ A)

    -- TODO: s must not contain any variables bound in A
    -- spec[_≔_] : ∀ {A Γ} → (x : NVar) (s : NExp) → Γ ⊢ ∇ x ∶ A
    --                     → Γ ⊢ sub[ x ≔ s ] A
    spec[_≔_] : ∀ {Γ ζ} → (x : NVar) (s : NExp {!!}) → {A : Type (ζ , x)} → Γ ⊢ {!!}
                        → Γ ⊢ type-sub {!!} A

    -- TODO: x must not be free in the premise of any fantasy containing A
    -- gen[_] : ∀ {A Γ} → (x : NVar) → Γ ⊢ A
    --                  → Γ ⊢ ∇ x ∶ A

    sym : ∀ {M N Γ} → Γ ⊢ M == N
                    → Γ ⊢ N == M

    trans : ∀ {M N O Γ} → Γ ⊢ M == N → Γ ⊢ N == O
                        → Γ ⊢ M == O

    suci : ∀ {M N Γ} → Γ ⊢ M == N
                     → Γ ⊢ suc M == suc N

    suce : ∀ {M N Γ} → Γ ⊢ suc M == suc N
                     → Γ ⊢ M == N

    -- induct : ∀ {x A Γ} → Γ ⊢ sub[ x ≔ 0 ] A → Γ ⊢ ∇ x ∶ A ⊃ sub[ x ≔ suc (nvar x) ] A
    --                    → Γ ⊢ ∇ x ∶ A

    ax1 : ∀ {Γ} → Γ ⊢ ∇ a ∶ ~ (suc (nvar a) == 0)

    ax2 : ∀ {Γ} → Γ ⊢ ∇ a ∶ ((nvar a + 0) == nvar a)

    ax3 : ∀ {Γ} → Γ ⊢ ∇ a ∶ ∇ b ∶ ((nvar a + nvar b) == suc (nvar a + nvar b))

    ax4 : ∀ {Γ} → Γ ⊢ ∇ a ∶ ((nvar a * 0) == 0)

    ax5 : ∀ {Γ} → Γ ⊢ ∇ a ∶ ∇ b ∶ ((nvar a * suc (nvar b)) == ((nvar a * nvar b) + nvar a))
