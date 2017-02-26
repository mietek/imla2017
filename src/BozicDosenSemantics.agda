module BozicDosenSemantics where

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

  -- Minor persistence condition.
  field
    ≤⨾R→R⨾≤ : ∀ {v′ w} → w ≤⨾R v′ → w R⨾≤ v′

  reflR⨾≤ : ∀ {w} → w R⨾≤ w
  reflR⨾≤ {w} = w , (reflR , refl≤)

  transR⨾≤ : ∀ {w′ w w″} → w R⨾≤ w′ → w′ R⨾≤ w″ → w R⨾≤ w″
  transR⨾≤ {w′} (v , (ζ , ξ)) (v′ , (ζ′ , ξ′)) = let v″ , (ζ″ , ξ″) = ≤⨾R→R⨾≤ (w′ , (ξ , ζ′))
                                                 in  v″ , (transR ζ ζ″ , trans≤ ξ″ ξ′)

open Model {{…}} public

module _ {{_ : Model}} where
  infix 3 _⊩_
  _⊩_ : World → Type → Set
  w ⊩ α P    = w ⊩ᵅ P
  w ⊩ A ⇒ B = ∀ {w′} → w ≤ w′ → w′ ⊩ A → w′ ⊩ B
  w ⊩ □ A    = ∀ {v′} → w R v′ → v′ ⊩ A
  w ⊩ A ⩕ B  = w ⊩ A ∧ w ⊩ B
  w ⊩ ⫪     = ⊤

  infix 3 _⊩⋆_
  _⊩⋆_ : World → Stack Type → Set
  w ⊩⋆ ∅     = ⊤
  w ⊩⋆ Ψ , A = w ⊩⋆ Ψ ∧ w ⊩ A

  mono⊩ : ∀ {A w w′} → w ≤ w′ → w ⊩ A → w′ ⊩ A
  mono⊩ {α P}    ψ s       = mono⊩ᵅ ψ s
  mono⊩ {A ⇒ B} ψ f       = λ ψ′ a → f (trans≤ ψ ψ′) a
  mono⊩ {□ A}    ψ f       = λ ρ → let _ , (ρ′ , ψ′) = ≤⨾R→R⨾≤ (_ , (ψ , ρ))
                                     in  mono⊩ {A} ψ′ (f ρ′)
  mono⊩ {A ⩕ B}  ψ (a , b) = mono⊩ {A} ψ a , mono⊩ {B} ψ b
  mono⊩ {⫪}     ψ ∙       = ∙

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
             (∀ {v′} → w R v′ → v′ ⊩⋆ Δ) →
             w ⊩ A

reflect : ∀ {Γ Δ A} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊨ A
reflect (var i)     γ δ = lookup i γ
reflect (mvar i)    γ δ = lookup i (δ reflR)
reflect (lam d)     γ δ = λ ψ a → reflect d (mono⊩⋆ ψ γ , a)
                                             (λ ρ → let _ , (ρ′ , ψ′) = ≤⨾R→R⨾≤ (_ , (ψ , ρ))
                                                     in  mono⊩⋆ ψ′ (δ ρ′))
reflect (app d e)   γ δ = (reflect d γ δ) refl≤ (reflect e γ δ)
reflect (box d)     γ δ = λ ρ → reflect d ∙
                                           (λ ρ′ → δ (transR ρ ρ′))
reflect (unbox d e) γ δ = reflect e γ (λ ρ → δ ρ , (reflect d γ δ) ρ)
reflect (pair d e)  γ δ = reflect d γ δ , reflect e γ δ
reflect (fst d)     γ δ = π₁ (reflect d γ δ)
reflect (snd d)     γ δ = π₂ (reflect d γ δ)
reflect unit        γ δ = ∙
