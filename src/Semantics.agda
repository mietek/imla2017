module Semantics where

open import Syntax


-- Vindicative Kripke models.

record Model : Set₁ where
  infix 3 _⊩ᵅ_
  field
    World   : Set
    _≤_     : World → World → Set
    refl≤   : ∀ {w} → w ≤ w
    trans≤  : ∀ {w w′ w″} → w ≤ w′ → w′ ≤ w″ → w ≤ w″
    _R_     : World → World → Set
    reflR   : ∀ {w} → w R w
    transR  : ∀ {w w′ w″} → w R w′ → w′ R w″ → w R w″
    _⊩ᵅ_   : World → Atom → Set
    mono⊩ᵅ : ∀ {w w′ P} → w ≤ w′ → w ⊩ᵅ P → w′ ⊩ᵅ P

  -- Vindication, a consequence of brilliance and persistence.
  field
    ≤→R : ∀ {v′ w} → w ≤ v′ → w R v′

open Model {{…}} public


-- Forcing in a particular world of a particular model.

module _ {{_ : Model}} where
  infix 3 _⊩_
  _⊩_ : World → Type → Set
  w ⊩ α P    = w ⊩ᵅ P
  w ⊩ A ⇒ B = ∀ {w′} → w ≤ w′ → w′ ⊩ A → w′ ⊩ B
  w ⊩ □ A    = ∀ {v′} → w R v′ → v′ ⊩ A
  w ⊩ A ⩕ B  = w ⊩ A ∧ w ⊩ B
  w ⊩ ⫪     = ⊤
  w ⊩ ⫫     = ⊥
  w ⊩ A ⩖ B  = w ⊩ A ∨ w ⊩ B

  infix 3 _⊩⋆_
  _⊩⋆_ : World → Stack Type → Set
  w ⊩⋆ ∅     = ⊤
  w ⊩⋆ Ξ , A = w ⊩⋆ Ξ ∧ w ⊩ A


-- Monotonicity of forcing with respect to constructive accessibility.

module _ {{_ : Model}} where
  mono⊩ : ∀ {A w w′} → w ≤ w′ → w ⊩ A → w′ ⊩ A
  mono⊩ {α P}    ψ s       = mono⊩ᵅ ψ s
  mono⊩ {A ⇒ B} ψ f       = λ ψ′ a → f (trans≤ ψ ψ′) a
  mono⊩ {□ A}    ψ f       = λ ρ → f (transR (≤→R ψ) ρ)
  mono⊩ {A ⩕ B}  ψ (a , b) = mono⊩ {A} ψ a , mono⊩ {B} ψ b
  mono⊩ {⫪}     ψ ∙       = ∙
  mono⊩ {⫫}     ψ ()
  mono⊩ {A ⩖ B}  ψ (ι₁ a)  = ι₁ (mono⊩ {A} ψ a)
  mono⊩ {A ⩖ B}  ψ (ι₂ b)  = ι₂ (mono⊩ {B} ψ b)

  mono⊩⋆ : ∀ {Ξ w w′} → w ≤ w′ → w ⊩⋆ Ξ → w′ ⊩⋆ Ξ
  mono⊩⋆ {∅}     ψ ∙       = ∙
  mono⊩⋆ {Ξ , A} ψ (ξ , s) = mono⊩⋆ {Ξ} ψ ξ , mono⊩ {A} ψ s


-- Additional equipment.

module _ {{_ : Model}} where
  lookup : ∀ {Ξ A w} → A ∈ Ξ → w ⊩⋆ Ξ → w ⊩ A
  lookup top     (ξ , s) = s
  lookup (pop i) (ξ , s) = lookup i ξ


-- Forcing in all worlds of all models, or semantic entailment.

infix 3 _⊨_
_⊨_ : Context → Type → Set₁
Γ ⁏ Δ ⊨ A = ∀ {{_ : Model}} {w} →
             w ⊩⋆ Γ →
             (∀ {v′} → w R v′ → v′ ⊩⋆ Δ) →
             w ⊩ A


-- Soundness of syntax with respect to the semantics.

reflect : ∀ {Γ Δ A} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊨ A
reflect (var i)      γ δ = lookup i γ
reflect (mvar i)     γ δ = lookup i (δ reflR)
reflect (lam d)      γ δ = λ ψ a → reflect d (mono⊩⋆ ψ γ , a)
                                              (λ ρ → δ (transR (≤→R ψ) ρ))
reflect (app d e)    γ δ = (reflect d γ δ) refl≤ (reflect e γ δ)
reflect (box d)      γ δ = λ ρ → reflect d ∙
                                            (λ ρ′ → δ (transR ρ ρ′))
reflect (unbox d e)  γ δ = reflect e γ (λ ρ → δ ρ , (reflect d γ δ) ρ)
reflect (pair d e)   γ δ = reflect d γ δ , reflect e γ δ
reflect (fst d)      γ δ = π₁ (reflect d γ δ)
reflect (snd d)      γ δ = π₂ (reflect d γ δ)
reflect unit         γ δ = ∙
reflect (boom d)     γ δ = elim⊥ (reflect d γ δ)
reflect (left d)     γ δ = ι₁ (reflect d γ δ)
reflect (right d)    γ δ = ι₂ (reflect d γ δ)
reflect (case d e f) γ δ = elim∨ (reflect d γ δ) (λ a → reflect e (γ , a) δ)
                                                 (λ b → reflect f (γ , b) δ)
