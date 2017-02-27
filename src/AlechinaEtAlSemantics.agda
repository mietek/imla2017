module AlechinaEtAlSemantics where

open import Syntax


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

  _≤⨾R_ : World → World → Set
  _≤⨾R_ = _≤_ ⨾ _R_

  _R⨾≤_ : World → World → Set
  _R⨾≤_ = _R_ ⨾ _≤_

  -- Minor brilliance condition.
  field
    R⨾≤→≤⨾R : ∀ {w v′} → w R⨾≤ v′ → w ≤⨾R v′

  refl≤⨾R : ∀ {w} → w ≤⨾R w
  refl≤⨾R {w} = w , (refl≤ , reflR)

  trans≤⨾R : ∀ {w′ w w″} → w ≤⨾R w′ → w′ ≤⨾R w″ → w ≤⨾R w″
  trans≤⨾R {w′} (v , (ξ , ζ)) (v′ , (ξ′ , ζ′)) = let v″ , (ξ″ , ζ″) = R⨾≤→≤⨾R (w′ , (ζ , ξ′))
                                                 in  v″ , (trans≤ ξ ξ″ , transR ζ″ ζ′)

open Model {{…}} public

module _ {{_ : Model}} where
  infix 3 _⊩_
  _⊩_ : World → Type → Set
  w ⊩ α P    = w ⊩ᵅ P
  w ⊩ A ⇒ B = ∀ {w′} → w ≤ w′ → w′ ⊩ A → w′ ⊩ B
  w ⊩ □ A    = ∀ {w′} → w ≤ w′ → ∀ {v′} → w′ R v′ → v′ ⊩ A
  w ⊩ A ⩕ B  = w ⊩ A ∧ w ⊩ B
  w ⊩ ⫪     = ⊤
  w ⊩ ⫫     = ⊥
  w ⊩ A ⩖ B  = w ⊩ A ∨ w ⊩ B

  infix 3 _⊩⋆_
  _⊩⋆_ : World → Stack Type → Set
  w ⊩⋆ ∅     = ⊤
  w ⊩⋆ Ψ , A = w ⊩⋆ Ψ ∧ w ⊩ A

  mono⊩ : ∀ {A w w′} → w ≤ w′ → w ⊩ A → w′ ⊩ A
  mono⊩ {α P}    ψ s       = mono⊩ᵅ ψ s
  mono⊩ {A ⇒ B} ψ f       = λ ψ′ a → f (trans≤ ψ ψ′) a
  mono⊩ {□ A}    ψ f       = λ ψ′ ρ → f (trans≤ ψ ψ′) ρ
  mono⊩ {A ⩕ B}  ψ (a , b) = mono⊩ {A} ψ a , mono⊩ {B} ψ b
  mono⊩ {⫪}     ψ ∙       = ∙
  mono⊩ {⫫}     ψ ()
  mono⊩ {A ⩖ B}  ψ (ι₁ a)  = ι₁ (mono⊩ {A} ψ a)
  mono⊩ {A ⩖ B}  ψ (ι₂ b)  = ι₂ (mono⊩ {B} ψ b)

  mono⊩⋆ : ∀ {Ξ w w′} → w ≤ w′ → w ⊩⋆ Ξ → w′ ⊩⋆ Ξ
  mono⊩⋆ {∅}     ψ ∙       = ∙
  mono⊩⋆ {Ξ , A} ψ (ξ , s) = mono⊩⋆ {Ξ} ψ ξ , mono⊩ {A} ψ s

  lookup : ∀ {Ξ A w} → A ∈ Ξ → w ⊩⋆ Ξ → w ⊩ A
  lookup top     (ξ , s) = s
  lookup (pop i) (ξ , s) = lookup i ξ

infix 3 _⊨_
_⊨_ : Context → Type → Set₁
Γ ⁏ Δ ⊨ A = ∀ {{_ : Model}} {w} →
             w ⊩⋆ Γ →
             (∀ {w′} → w ≤ w′ → ∀ {v′} → w′ R v′ → v′ ⊩⋆ Δ) →
             w ⊩ A

reflect : ∀ {Γ Δ A} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊨ A
reflect (var i)      γ δ = lookup i γ
reflect (mvar i)     γ δ = lookup i (δ refl≤ reflR)
reflect (lam d)      γ δ = λ ψ a → reflect d (mono⊩⋆ ψ γ , a)
                                              (λ ψ′ ρ → δ (trans≤ ψ ψ′) ρ)
reflect (app d e)    γ δ = (reflect d γ δ) refl≤ (reflect e γ δ)
reflect (box d)      γ δ = λ ψ ρ → reflect d ∙
                                              (λ ψ′ ρ′ → let _ , (ψ″ , ρ″) = R⨾≤→≤⨾R (_ , (ρ , ψ′))
                                                          in  δ (trans≤ ψ ψ″) (transR ρ″ ρ′))
reflect (unbox d e)  γ δ = reflect e γ (λ ψ ρ → δ ψ ρ , (reflect d γ δ) ψ ρ)
reflect (pair d e)   γ δ = reflect d γ δ , reflect e γ δ
reflect (fst d)      γ δ = π₁ (reflect d γ δ)
reflect (snd d)      γ δ = π₂ (reflect d γ δ)
reflect unit         γ δ = ∙
reflect (boom d)     γ δ = elim⊥ (reflect d γ δ)
reflect (left d)     γ δ = ι₁ (reflect d γ δ)
reflect (right d)    γ δ = ι₂ (reflect d γ δ)
reflect (case d e f) γ δ = elim∨ (reflect d γ δ) (λ a → reflect e (γ , a) δ)
                                                 (λ b → reflect f (γ , b) δ)