module CompleteSemantics.AlechinaEtAl where

open import Syntax public


-- Introspective minor brilliant Kripke models.

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

  -- Introspection.
  field
    peek : World → Context

  _≤⨾R_ : World → World → Set
  _≤⨾R_ = _≤_ ⨾ _R_

  _R⨾≤_ : World → World → Set
  _R⨾≤_ = _R_ ⨾ _≤_

  -- Minor brilliance.
  field
    R⨾≤→≤⨾R : ∀ {w v′} → w R⨾≤ v′ → w ≤⨾R v′

open Model {{…}} public


-- Forcing in a particular world of a particular model.

module _ {{_ : Model}} where
  mutual
    infix 3 _⊪_
    _⊪_ : World → Type → Set
    w ⊪ α P    = w ⊩ᵅ P
    w ⊪ A ⇒ B = ∀ {w′} → w ≤ w′ → w′ ⊩ A → w′ ⊩ B
    w ⊪ □ A    = ∀ {w′} → w ≤ w′ → ∀ {v′} → w′ R v′ → ∅ ⁏ π₂ (peek v′) ⊢ A ∧ v′ ⊩ A
    w ⊪ A ⩕ B  = w ⊩ A ∧ w ⊩ B
    w ⊪ ⫪     = ⊤
    w ⊪ ⫫     = ⊥
    w ⊪ A ⩖ B  = w ⊩ A ∨ w ⊩ B

    infix 3 _⊩_
    _⊩_ : World → Type → Set
    w ⊩ A = ∀ {C w′} → w ≤ w′ →
             (∀ {w″} → w′ ≤ w″ → w″ ⊪ A → peek w″ ⊢ⁿᶠ C) →
             peek w′ ⊢ⁿᶠ C

  infix 3 _⊩⋆_
  _⊩⋆_ : World → Stack Type → Set
  w ⊩⋆ ∅     = ⊤
  w ⊩⋆ Ξ , A = w ⊩⋆ Ξ ∧ w ⊩ A


-- Monotonicity of forcing with respect to constructive accessibility.

module _ {{_ : Model}} where
  mutual
    mono⊪ : ∀ {A w w′} → w ≤ w′ → w ⊪ A → w′ ⊪ A
    mono⊪ {α P}    ψ s       = mono⊩ᵅ ψ s
    mono⊪ {A ⇒ B} ψ f       = λ ψ′ a → f (trans≤ ψ ψ′) a
    mono⊪ {□ A}    ψ f       = λ ψ′ ρ → f (trans≤ ψ ψ′) ρ
    mono⊪ {A ⩕ B}  ψ (a , b) = mono⊩ {A} ψ a , mono⊩ {B} ψ b
    mono⊪ {⫪}     ψ ∙       = ∙
    mono⊪ {⫫}     ψ ()
    mono⊪ {A ⩖ B}  ψ (ι₁ a)  = ι₁ (mono⊩ {A} ψ a)
    mono⊪ {A ⩖ B}  ψ (ι₂ b)  = ι₂ (mono⊩ {B} ψ b)

    mono⊩ : ∀ {A w w′} → w ≤ w′ → w ⊩ A → w′ ⊩ A
    mono⊩ ψ a = λ ψ′ κ → a (trans≤ ψ ψ′) κ

  mono⊩⋆ : ∀ {Ξ w w′} → w ≤ w′ → w ⊩⋆ Ξ → w′ ⊩⋆ Ξ
  mono⊩⋆ {∅}     ψ ∙       = ∙
  mono⊩⋆ {Ξ , A} ψ (ξ , s) = mono⊩⋆ {Ξ} ψ ξ , mono⊩ {A} ψ s


-- Continuation-passing equipment.

module _ {{_ : Model}} where
  return : ∀ {A w} → w ⊪ A → w ⊩ A
  return {A} a = λ ψ κ → κ refl≤ (mono⊪ {A} ψ a)

  bind : ∀ {A B w} → w ⊩ A →
         (∀ {w′} → w ≤ w′ → w′ ⊪ A → w′ ⊩ B) →
         w ⊩ B
  bind a κ = λ ψ κ′ → a ψ
               λ ψ′ a′ → κ (trans≤ ψ ψ′) a′ refl≤
                 λ ψ″ a″ → κ′ (trans≤ ψ′ ψ″) a″


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
             (∀ {w′} → w ≤ w′ → ∀ {v′} → w′ R v′ → ∅ ⁏ π₂ (peek v′) ⊢⋆ Δ) →
             (∀ {w′} → w ≤ w′ → ∀ {v′} → w′ R v′ → v′ ⊩⋆ Δ) →
             w ⊩ A


-- Soundness of the semantics with respect to the syntax.

reflect : ∀ {Γ Δ A} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊨ A
reflect (var i)                  γ τ δ = lookup i γ
reflect (mvar i)                 γ τ δ = lookup i (δ refl≤ reflR)
reflect (lam {A} {B} d)          γ τ δ = return {A ⇒ B}
                                           λ ψ a → reflect d (mono⊩⋆ ψ γ , a)
                                                              (λ ψ′ ρ → τ (trans≤ ψ ψ′) ρ)
                                                              (λ ψ′ ρ → δ (trans≤ ψ ψ′) ρ)
reflect (app {A} {B} d e)        γ τ δ = bind {A ⇒ B} {B} (reflect d γ τ δ)
                                           λ ψ f → f refl≤ (mono⊩ {A} ψ (reflect e γ τ δ))
reflect (box {A} d)              γ τ δ = return {□ A}
                                           λ ψ ρ → graft⊢ ∙ (τ ψ ρ) d ,
                                                    reflect d ∙
                                                              (λ ψ′ ρ′ → let _ , (ψ″ , ρ″) = R⨾≤→≤⨾R (_ , (ρ , ψ′))
                                                                          in  τ (trans≤ ψ ψ″) (transR ρ″ ρ′))
                                                              (λ ψ′ ρ′ → let _ , (ψ″ , ρ″) = R⨾≤→≤⨾R (_ , (ρ , ψ′))
                                                                          in  δ (trans≤ ψ ψ″) (transR ρ″ ρ′))
reflect (unbox {A} {C} d e)      γ τ δ = bind {□ A} {C} (reflect d γ τ δ)
                                           λ ψ s → reflect e (mono⊩⋆ ψ γ)
                                                              (λ ψ′ ρ → τ (trans≤ ψ ψ′) ρ , π₁ (s ψ′ ρ))
                                                              (λ ψ′ ρ → δ (trans≤ ψ ψ′) ρ , π₂ (s ψ′ ρ))
reflect (pair {A} {B} d e)       γ τ δ = return {A ⩕ B} (reflect d γ τ δ , reflect e γ τ δ)
reflect (fst {A} {B} d)          γ τ δ = bind {A ⩕ B} {A} (reflect d γ τ δ)
                                           λ { ψ (a , b) → a }
reflect (snd {A} {B} d)          γ τ δ = bind {A ⩕ B} {B} (reflect d γ τ δ)
                                           λ { ψ (a , b) → b }
reflect unit                     γ τ δ = return {⫪} ∙
reflect (boom {C} d)             γ τ δ = bind {⫫} {C} (reflect d γ τ δ)
                                           λ ψ → elim⊥
reflect (left {A} {B} d)         γ τ δ = return {A ⩖ B} (ι₁ (reflect d γ τ δ))
reflect (right {A} {B} d)        γ τ δ = return {A ⩖ B} (ι₂ (reflect d γ τ δ))
reflect (case {A} {B} {C} d e f) γ τ δ = bind {A ⩖ B} {C} (reflect d γ τ δ)
                                           λ { ψ (ι₁ a) → reflect e (mono⊩⋆ ψ γ , a)
                                                                     (λ ψ′ ρ → τ (trans≤ ψ ψ′) ρ)
                                                                     (λ ψ′ ρ → δ (trans≤ ψ ψ′) ρ)
                                             ; ψ (ι₂ b) → reflect f (mono⊩⋆ ψ γ , b)
                                                                     (λ ψ′ ρ → τ (trans≤ ψ ψ′) ρ)
                                                                     (λ ψ′ ρ → δ (trans≤ ψ ψ′) ρ)
                                             }


-- The canonical model.

private
  instance
    canon : Model
    canon = record
      { World    = Context
      ; _≤_      = _⊆²_
      ; refl≤    = refl⊆²
      ; trans≤   = trans⊆²
      ; _R_      = λ { (_ ⁏ Δ) (_ ⁏ Δ′) → Δ ⊆ Δ′ }
      ; reflR    = refl⊆
      ; transR   = trans⊆
      ; _⊩ᵅ_    = λ { (Γ ⁏ Δ) P → Γ ⁏ Δ ⊢ⁿᵉ α P }
      ; mono⊩ᵅ  = mono⊢ⁿᵉ
      ; peek     = id
      ; R⨾≤→≤⨾R = λ { (_ , (ρ , (_ , ρ′))) → _ , (refl⊆² , trans⊆ ρ ρ′) }
      }


-- Soundness and completeness of the canonical model with respect to the syntax.

mutual
  reflectᶜ : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ⁿᵉ A → Γ ⁏ Δ ⊩ A
  reflectᶜ {α P}    d = return {α P} d
  reflectᶜ {A ⇒ B} d = return {A ⇒ B}
                          λ ψ a → reflectᶜ (appⁿᵉ (mono⊢ⁿᵉ ψ d) (reifyᶜ a))
  reflectᶜ {□ A}    d = λ ψ κ → neⁿᶠ (unboxⁿᵉ (mono⊢ⁿᵉ ψ d)
                                               (κ (refl⊆ , weak⊆)
                                                  λ { (η , ρ′) ρ″ → mono⊢ (bot , trans⊆ ρ′ ρ″) mv₀ ,
                                                                     reflectᶜ (mono⊢ⁿᵉ (bot , trans⊆ ρ′ ρ″) mv₀ⁿᵉ) } ))
  reflectᶜ {A ⩕ B}  d = return {A ⩕ B} (reflectᶜ (fstⁿᵉ d) , reflectᶜ (sndⁿᵉ d))
  reflectᶜ {⫪}     d = return {⫪} ∙
  reflectᶜ {⫫}     d = λ ψ κ → neⁿᶠ (boomⁿᵉ (mono⊢ⁿᵉ ψ d))
  reflectᶜ {A ⩖ B}  d = λ ψ κ → neⁿᶠ (caseⁿᵉ (mono⊢ⁿᵉ ψ d)
                                              (κ (weak⊆ , refl⊆) (ι₁ (reflectᶜ v₀ⁿᵉ)))
                                              (κ (weak⊆ , refl⊆) (ι₂ (reflectᶜ v₀ⁿᵉ))))

  reifyᶜ : ∀ {A Γ Δ} → Γ ⁏ Δ ⊩ A → Γ ⁏ Δ ⊢ⁿᶠ A
  reifyᶜ {α P}    κ = κ refl⊆²
                        λ ψ s → neⁿᶠ s
  reifyᶜ {A ⇒ B} κ = κ refl⊆²
                        λ ψ f → lamⁿᶠ (reifyᶜ (f (weak⊆ , refl⊆) (reflectᶜ v₀ⁿᵉ)))
  reifyᶜ {□ A}    κ = κ refl⊆²
                        λ ψ f → boxⁿᶠ (π₁ (f refl⊆² {(∅ ⁏ _)} refl⊆))
  reifyᶜ {A ⩕ B}  κ = κ refl⊆²
                        λ { ψ (a , b) → pairⁿᶠ (reifyᶜ a) (reifyᶜ b) }
  reifyᶜ {⫪}     κ = κ refl⊆²
                        λ { ψ ∙ → unitⁿᶠ }
  reifyᶜ {⫫}     κ = κ refl⊆²
                        λ ψ ()
  reifyᶜ {A ⩖ B}  κ = κ refl⊆²
                        λ { ψ (ι₁ a) → leftⁿᶠ (reifyᶜ a)
                          ; ψ (ι₂ b) → rightⁿᶠ (reifyᶜ b)
                          }


-- Reflexivity of simultaneous forcing.

refl⊩⋆ : ∀ {Γ Δ} → Γ ⁏ Δ ⊩⋆ Γ
refl⊩⋆ {∅}     = ∙
refl⊩⋆ {Γ , A} = mono⊩⋆ (weak⊆ , refl⊆) refl⊩⋆ , reflectᶜ v₀ⁿᵉ

mrefl⊩⋆ : ∀ {Δ Γ} → Γ ⁏ Δ ⊩⋆ Δ
mrefl⊩⋆ {∅}     = ∙
mrefl⊩⋆ {Δ , A} = mono⊩⋆ (refl⊆ , weak⊆) mrefl⊩⋆ , reflectᶜ mv₀ⁿᵉ


-- Completeness of the semantics with respect to the syntax.

reify : ∀ {Γ Δ A} → Γ ⁏ Δ ⊨ A → Γ ⁏ Δ ⊢ⁿᶠ A
reify s = reifyᶜ (s refl⊩⋆ (λ { (η , ρ) ρ′ → mono⊢⋆ (refl⊆ , trans⊆ ρ ρ′) mrefl⊢⋆ })
                            (λ { (η , ρ) ρ′ → mono⊩⋆ (refl⊆ , trans⊆ ρ ρ′) mrefl⊩⋆ }))


-- Normalisation by evaluation.

nbe : ∀ {Γ Δ A} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ⁿᶠ A
nbe = reify ∘ reflect
