module Syntax where

open import Stack public


-- Abstract symbols, or atoms.

abstract
  Atom : Set
  Atom = Nat


-- Types, or propositions in constructive modal logic S4.

infixl 9 _⩕_
infixl 8 _⩖_
infixr 7 _⇒_
data Type : Set where
  α_   : Atom → Type
  _⇒_ : Type → Type → Type
  □_   : Type → Type
  _⩕_  : Type → Type → Type
  ⫪   : Type
  ⫫   : Type
  _⩖_  : Type → Type → Type

⫬_ : Type → Type
⫬ A = A ⇒ ⫫


-- Contexts, or stack pairs of types.

Context : Set
Context = Stack² Type Type


-- Derivations, or syntactic entailment.

infix 3 _⊢_
data _⊢_ : Context → Type → Set where
  var   : ∀ {A Γ Δ}     → A ∈ Γ → Γ ⁏ Δ ⊢ A
  mvar  : ∀ {A Γ Δ}     → A ∈ Δ → Γ ⁏ Δ ⊢ A
  lam   : ∀ {A B Γ Δ}   → Γ , A ⁏ Δ ⊢ B → Γ ⁏ Δ ⊢ A ⇒ B
  app   : ∀ {A B Γ Δ}   → Γ ⁏ Δ ⊢ A ⇒ B → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ B
  box   : ∀ {A Γ Δ}     → ∅ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ □ A
  unbox : ∀ {A C Γ Δ}   → Γ ⁏ Δ ⊢ □ A → Γ ⁏ Δ , A ⊢ C → Γ ⁏ Δ ⊢ C
  pair  : ∀ {A B Γ Δ}   → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ B → Γ ⁏ Δ ⊢ A ⩕ B
  fst   : ∀ {A B Γ Δ}   → Γ ⁏ Δ ⊢ A ⩕ B → Γ ⁏ Δ ⊢ A
  snd   : ∀ {A B Γ Δ}   → Γ ⁏ Δ ⊢ A ⩕ B → Γ ⁏ Δ ⊢ B
  unit  : ∀ {Γ Δ}       → Γ ⁏ Δ ⊢ ⫪
  boom  : ∀ {C Γ Δ}     → Γ ⁏ Δ ⊢ ⫫ → Γ ⁏ Δ ⊢ C
  left  : ∀ {A B Γ Δ}   → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ A ⩖ B
  right : ∀ {A B Γ Δ}   → Γ ⁏ Δ ⊢ B → Γ ⁏ Δ ⊢ A ⩖ B
  case  : ∀ {A B C Γ Δ} → Γ ⁏ Δ ⊢ A ⩖ B → Γ , A ⁏ Δ ⊢ C → Γ , B ⁏ Δ ⊢ C → Γ ⁏ Δ ⊢ C


-- Shorthand for variables.

v₀ : ∀ {Γ Δ A} → Γ , A ⁏ Δ ⊢ A
v₀ = var i₀

v₁ : ∀ {Γ Δ A B} → Γ , A , B ⁏ Δ ⊢ A
v₁ = var i₁

v₂ : ∀ {Γ Δ A B C} → Γ , A , B , C ⁏ Δ ⊢ A
v₂ = var i₂

mv₀ : ∀ {Γ Δ A} → Γ ⁏ Δ , A ⊢ A
mv₀ = mvar i₀

mv₁ : ∀ {Γ Δ A B} → Γ ⁏ Δ , A , B ⊢ A
mv₁ = mvar i₁

mv₂ : ∀ {Γ Δ A B C} → Γ ⁏ Δ , A , B , C ⊢ A
mv₂ = mvar i₂


-- Stacks of derivations, or simultaneous syntactic entailment.

infix 3 _⊢⋆_
_⊢⋆_ : Context → Stack Type → Set
Γ ⁏ Δ ⊢⋆ ∅     = ⊤
Γ ⁏ Δ ⊢⋆ Ξ , A = Γ ⁏ Δ ⊢⋆ Ξ ∧ Γ ⁏ Δ ⊢ A


-- Monotonicity of syntactic entailment with respect to context inclusion.

mono⊢ : ∀ {Γ Γ′ Δ Δ′ A} → Γ ⁏ Δ ⊆² Γ′ ⁏ Δ′ → Γ ⁏ Δ ⊢ A → Γ′ ⁏ Δ′ ⊢ A
mono⊢ (η , ρ) (var i)      = var (mono∈ η i)
mono⊢ (η , ρ) (mvar i)     = mvar (mono∈ ρ i)
mono⊢ (η , ρ) (lam d)      = lam (mono⊢ (keep η , ρ) d)
mono⊢ ψ       (app d e)    = app (mono⊢ ψ d) (mono⊢ ψ e)
mono⊢ (η , ρ) (box d)      = box (mono⊢ (bot , ρ) d)
mono⊢ (η , ρ) (unbox d e)  = unbox (mono⊢ (η , ρ) d) (mono⊢ (η , keep ρ) e)
mono⊢ ψ       (pair d e)   = pair (mono⊢ ψ d) (mono⊢ ψ e)
mono⊢ ψ       (fst d)      = fst (mono⊢ ψ d)
mono⊢ ψ       (snd d)      = snd (mono⊢ ψ d)
mono⊢ ψ       unit         = unit
mono⊢ ψ       (boom d)     = boom (mono⊢ ψ d)
mono⊢ ψ       (left d)     = left (mono⊢ ψ d)
mono⊢ ψ       (right d)    = right (mono⊢ ψ d)
mono⊢ (η , ρ) (case d e f) = case (mono⊢ (η , ρ) d) (mono⊢ (keep η , ρ) e)
                                                      (mono⊢ (keep η , ρ) f)

mono⊢⋆ : ∀ {Ξ Γ Γ′ Δ Δ′} → Γ ⁏ Δ ⊆² Γ′ ⁏ Δ′ → Γ ⁏ Δ ⊢⋆ Ξ → Γ′ ⁏ Δ′ ⊢⋆ Ξ
mono⊢⋆ {∅}     ψ ∙       = ∙
mono⊢⋆ {Ξ , A} ψ (ξ , d) = mono⊢⋆ ψ ξ , mono⊢ ψ d


-- Reflexivity of simultaneous syntactic entailment.

refl⊢⋆ : ∀ {Γ Δ} → Γ ⁏ Δ ⊢⋆ Γ
refl⊢⋆ {∅}     = ∙
refl⊢⋆ {Γ , A} = mono⊢⋆ (weak⊆ , refl⊆) refl⊢⋆ , v₀

mrefl⊢⋆ : ∀ {Δ Γ} → Γ ⁏ Δ ⊢⋆ Δ
mrefl⊢⋆ {∅}     = ∙
mrefl⊢⋆ {Δ , A} = mono⊢⋆ (refl⊆ , weak⊆) mrefl⊢⋆ , mv₀


-- Grafting of derivation trees, or simultaneous substitution, or cut.

graft∈ : ∀ {Ξ Γ Δ C} → Γ ⁏ Δ ⊢⋆ Ξ → C ∈ Ξ → Γ ⁏ Δ ⊢ C
graft∈ (ξ , d) top     = d
graft∈ (ξ , d) (pop i) = graft∈ ξ i

graft⊢ : ∀ {Γ Γ′ Δ Δ′ C} → Γ′ ⁏ Δ′ ⊢⋆ Γ → ∅ ⁏ Δ′ ⊢⋆ Δ → Γ ⁏ Δ ⊢ C → Γ′ ⁏ Δ′ ⊢ C
graft⊢ σ τ (var i)      = graft∈ σ i
graft⊢ σ τ (mvar i)     = mono⊢ (bot , refl⊆) (graft∈ τ i)
graft⊢ σ τ (lam d)      = lam (graft⊢ (mono⊢⋆ (weak⊆ , refl⊆) σ , v₀) τ d)
graft⊢ σ τ (app d e)    = app (graft⊢ σ τ d) (graft⊢ σ τ e)
graft⊢ σ τ (box d)      = box (graft⊢ ∙ τ d)
graft⊢ σ τ (unbox d e)  = unbox (graft⊢ σ τ d) (graft⊢ (mono⊢⋆ (refl⊆ , weak⊆) σ)
                                                          (mono⊢⋆ (refl⊆ , weak⊆) τ , mv₀) e)
graft⊢ σ τ (pair d e)   = pair (graft⊢ σ τ d) (graft⊢ σ τ e)
graft⊢ σ τ (fst d)      = fst (graft⊢ σ τ d)
graft⊢ σ τ (snd d)      = snd (graft⊢ σ τ d)
graft⊢ σ τ unit         = unit
graft⊢ σ τ (boom d)     = boom (graft⊢ σ τ d)
graft⊢ σ τ (left d)     = left (graft⊢ σ τ d)
graft⊢ σ τ (right d)    = right (graft⊢ σ τ d)
graft⊢ σ τ (case d e f) = case (graft⊢ σ τ d) (graft⊢ (mono⊢⋆ (weak⊆ , refl⊆) σ , v₀) τ e)
                                                (graft⊢ (mono⊢⋆ (weak⊆ , refl⊆) σ , v₀) τ f)


-- Derivations, or syntactic entailment, in normal form.

mutual
  infix 3 _⊢ⁿᶠ_
  data _⊢ⁿᶠ_ : Context → Type → Set where
    lamⁿᶠ   : ∀ {A B Γ Δ}   → Γ , A ⁏ Δ ⊢ⁿᶠ B → Γ ⁏ Δ ⊢ⁿᶠ A ⇒ B
    boxⁿᶠ   : ∀ {A Γ Δ}     → ∅ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ⁿᶠ □ A
    pairⁿᶠ  : ∀ {A B Γ Δ}   → Γ ⁏ Δ ⊢ⁿᶠ A → Γ ⁏ Δ ⊢ⁿᶠ B → Γ ⁏ Δ ⊢ⁿᶠ A ⩕ B
    unitⁿᶠ  : ∀ {Γ Δ}       → Γ ⁏ Δ ⊢ⁿᶠ ⫪
    leftⁿᶠ  : ∀ {A B Γ Δ}   → Γ ⁏ Δ ⊢ⁿᶠ A → Γ ⁏ Δ ⊢ⁿᶠ A ⩖ B
    rightⁿᶠ : ∀ {A B Γ Δ}   → Γ ⁏ Δ ⊢ⁿᶠ B → Γ ⁏ Δ ⊢ⁿᶠ A ⩖ B
    neⁿᶠ    : ∀ {A Γ Δ}     → Γ ⁏ Δ ⊢ⁿᵉ A → Γ ⁏ Δ ⊢ⁿᶠ A

  infix 3 _⊢ⁿᵉ_
  data _⊢ⁿᵉ_ : Context → Type → Set where
    varⁿᵉ   : ∀ {A Γ Δ}     → A ∈ Γ → Γ ⁏ Δ ⊢ⁿᵉ A
    mvarⁿᵉ  : ∀ {A Γ Δ}     → A ∈ Δ → Γ ⁏ Δ ⊢ⁿᵉ A
    appⁿᵉ   : ∀ {A B Γ Δ}   → Γ ⁏ Δ ⊢ⁿᵉ A ⇒ B → Γ ⁏ Δ ⊢ⁿᶠ A → Γ ⁏ Δ ⊢ⁿᵉ B
    unboxⁿᵉ : ∀ {A C Γ Δ}   → Γ ⁏ Δ ⊢ⁿᵉ □ A → Γ ⁏ Δ , A ⊢ⁿᶠ C → Γ ⁏ Δ ⊢ⁿᵉ C
    fstⁿᵉ   : ∀ {A B Γ Δ}   → Γ ⁏ Δ ⊢ⁿᵉ A ⩕ B → Γ ⁏ Δ ⊢ⁿᵉ A
    sndⁿᵉ   : ∀ {A B Γ Δ}   → Γ ⁏ Δ ⊢ⁿᵉ A ⩕ B → Γ ⁏ Δ ⊢ⁿᵉ B
    boomⁿᵉ  : ∀ {C Γ Δ}     → Γ ⁏ Δ ⊢ⁿᵉ ⫫ → Γ ⁏ Δ ⊢ⁿᵉ C
    caseⁿᵉ  : ∀ {A B C Γ Δ} → Γ ⁏ Δ ⊢ⁿᵉ A ⩖ B → Γ , A ⁏ Δ ⊢ⁿᶠ C → Γ , B ⁏ Δ ⊢ⁿᶠ C → Γ ⁏ Δ ⊢ⁿᵉ C


-- Shorthand for variables.

v₀ⁿᵉ : ∀ {Γ Δ A} → Γ , A ⁏ Δ ⊢ⁿᵉ A
v₀ⁿᵉ = varⁿᵉ top

mv₀ⁿᵉ : ∀ {Γ Δ A} → Γ ⁏ Δ , A ⊢ⁿᵉ A
mv₀ⁿᵉ = mvarⁿᵉ top


-- Stacks of derivations, or simultaneous syntactic entailment, in normal form.

infix 3 _⊢⋆ⁿᵉ_
_⊢⋆ⁿᵉ_ : Context → Stack Type → Set
Γ ⁏ Δ ⊢⋆ⁿᵉ ∅     = ⊤
Γ ⁏ Δ ⊢⋆ⁿᵉ Ξ , A = Γ ⁏ Δ ⊢⋆ⁿᵉ Ξ ∧ Γ ⁏ Δ ⊢ⁿᵉ A


-- Translation from normal form to arbitrary form.

mutual
  nf→af : ∀ {Γ Δ A} → Γ ⁏ Δ ⊢ⁿᶠ A → Γ ⁏ Δ ⊢ A
  nf→af (neⁿᶠ d)       = ne→af d
  nf→af (lamⁿᶠ d)      = lam (nf→af d)
  nf→af (boxⁿᶠ d)      = box d
  nf→af (pairⁿᶠ d e)   = pair (nf→af d) (nf→af e)
  nf→af unitⁿᶠ         = unit
  nf→af (leftⁿᶠ d)     = left (nf→af d)
  nf→af (rightⁿᶠ d)    = right (nf→af d)

  ne→af : ∀ {Γ Δ A} → Γ ⁏ Δ ⊢ⁿᵉ A → Γ ⁏ Δ ⊢ A
  ne→af (varⁿᵉ i)      = var i
  ne→af (mvarⁿᵉ i)     = mvar i
  ne→af (appⁿᵉ d e)    = app (ne→af d) (nf→af e)
  ne→af (unboxⁿᵉ d e)  = unbox (ne→af d) (nf→af e)
  ne→af (fstⁿᵉ d)      = fst (ne→af d)
  ne→af (sndⁿᵉ d)      = snd (ne→af d)
  ne→af (boomⁿᵉ d)     = boom (ne→af d)
  ne→af (caseⁿᵉ d e f) = case (ne→af d) (nf→af e) (nf→af f)


-- Monotonicity of syntactic entailment with respect to context inclusion, in normal form.

mutual
  mono⊢ⁿᶠ : ∀ {Γ Γ′ Δ Δ′ A} → Γ ⁏ Δ ⊆² Γ′ ⁏ Δ′ → Γ ⁏ Δ ⊢ⁿᶠ A → Γ′ ⁏ Δ′ ⊢ⁿᶠ A
  mono⊢ⁿᶠ (η , ρ) (lamⁿᶠ d)      = lamⁿᶠ (mono⊢ⁿᶠ (keep η , ρ) d)
  mono⊢ⁿᶠ (η , ρ) (boxⁿᶠ d)      = boxⁿᶠ (mono⊢ (bot , ρ) d)
  mono⊢ⁿᶠ ψ       (pairⁿᶠ d e)   = pairⁿᶠ (mono⊢ⁿᶠ ψ d) (mono⊢ⁿᶠ ψ e)
  mono⊢ⁿᶠ ψ       unitⁿᶠ         = unitⁿᶠ
  mono⊢ⁿᶠ ψ       (leftⁿᶠ d)     = leftⁿᶠ (mono⊢ⁿᶠ ψ d)
  mono⊢ⁿᶠ ψ       (rightⁿᶠ d)    = rightⁿᶠ (mono⊢ⁿᶠ ψ d)
  mono⊢ⁿᶠ ψ       (neⁿᶠ d)       = neⁿᶠ (mono⊢ⁿᵉ ψ d)

  mono⊢ⁿᵉ : ∀ {Γ Γ′ Δ Δ′ A} → Γ ⁏ Δ ⊆² Γ′ ⁏ Δ′ → Γ ⁏ Δ ⊢ⁿᵉ A → Γ′ ⁏ Δ′ ⊢ⁿᵉ A
  mono⊢ⁿᵉ (η , ρ) (varⁿᵉ i)      = varⁿᵉ (mono∈ η i)
  mono⊢ⁿᵉ (η , ρ) (mvarⁿᵉ i)     = mvarⁿᵉ (mono∈ ρ i)
  mono⊢ⁿᵉ ψ       (appⁿᵉ d e)    = appⁿᵉ (mono⊢ⁿᵉ ψ d) (mono⊢ⁿᶠ ψ e)
  mono⊢ⁿᵉ (η , ρ) (unboxⁿᵉ d e)  = unboxⁿᵉ (mono⊢ⁿᵉ (η , ρ) d) (mono⊢ⁿᶠ (η , keep ρ) e)
  mono⊢ⁿᵉ ψ       (fstⁿᵉ d)      = fstⁿᵉ (mono⊢ⁿᵉ ψ d)
  mono⊢ⁿᵉ ψ       (sndⁿᵉ d)      = sndⁿᵉ (mono⊢ⁿᵉ ψ d)
  mono⊢ⁿᵉ ψ       (boomⁿᵉ d)     = boomⁿᵉ (mono⊢ⁿᵉ ψ d)
  mono⊢ⁿᵉ (η , ρ) (caseⁿᵉ d e f) = caseⁿᵉ (mono⊢ⁿᵉ (η , ρ) d) (mono⊢ⁿᶠ (keep η , ρ) e)
                                                                (mono⊢ⁿᶠ (keep η , ρ) f)

mono⊢⋆ⁿᵉ : ∀ {Ξ Γ Γ′ Δ Δ′} → Γ ⁏ Δ ⊆² Γ′ ⁏ Δ′ → Γ ⁏ Δ ⊢⋆ⁿᵉ Ξ → Γ′ ⁏ Δ′ ⊢⋆ⁿᵉ Ξ
mono⊢⋆ⁿᵉ {∅}     ψ ∙       = ∙
mono⊢⋆ⁿᵉ {Ξ , A} ψ (ξ , d) = mono⊢⋆ⁿᵉ ψ ξ , mono⊢ⁿᵉ ψ d


-- Reflexivity of simultaneous syntactic entailment, in normal form.

refl⊢⋆ⁿᵉ : ∀ {Γ Δ} → Γ ⁏ Δ ⊢⋆ⁿᵉ Γ
refl⊢⋆ⁿᵉ {∅}     = ∙
refl⊢⋆ⁿᵉ {Γ , A} = mono⊢⋆ⁿᵉ (weak⊆ , refl⊆) refl⊢⋆ⁿᵉ , v₀ⁿᵉ

mrefl⊢⋆ⁿᵉ : ∀ {Δ Γ} → Γ ⁏ Δ ⊢⋆ⁿᵉ Δ
mrefl⊢⋆ⁿᵉ {∅}     = ∙
mrefl⊢⋆ⁿᵉ {Δ , A} = mono⊢⋆ⁿᵉ (refl⊆ , weak⊆) mrefl⊢⋆ⁿᵉ , mv₀ⁿᵉ
