module CompleteIemhoffSemantics where

open import Syntax public


-- Introspective brilliant Kripke models.

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
    peek    : World → Context

  _R⨾≤_ : World → World → Set
  _R⨾≤_ = _R_ ⨾ _≤_

  -- Brilliance.
  field
    R⨾≤→R : ∀ {w v′} → w R⨾≤ v′ → w R v′

  -- Vindication, as a consequence of brilliance.
  ≤→R : ∀ {w v′} → w ≤ v′ → w R v′
  ≤→R {w} ψ = R⨾≤→R (w , (reflR , ψ))

open Model {{…}} public


-- Forcing in a particular world of a particular model.

module _ {{_ : Model}} where
  mutual
    infix 3 _⊪_
    _⊪_ : World → Type → Set
    w ⊪ α P    = w ⊩ᵅ P
    w ⊪ A ⇒ B = ∀ {w′} → w ≤ w′ → w′ ⊩ A → w′ ⊩ B
    w ⊪ □ A    = ∀ {v′} → w R v′ → ∅ ⁏ π₂ (peek v′) ⊢ A ∧ v′ ⊩ A
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
    mono⊪ {□ A}    ψ f       = λ ρ → f (transR (≤→R ψ) ρ)
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
             (∀ {v′} → w R v′ → ∅ ⁏ π₂ (peek v′) ⊢⋆ Δ) →
             (∀ {v′} → w R v′ → v′ ⊩⋆ Δ) →
             w ⊩ A


-- Soundness of syntax with respect to the semantics.

reflect : ∀ {Γ Δ A} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊨ A
reflect (var i)                  γ τ δ = lookup i γ
reflect (mvar i)                 γ τ δ = lookup i (δ reflR)
reflect (lam {A} {B} d)          γ τ δ = return {A ⇒ B}
                                           λ ψ a → reflect d (mono⊩⋆ ψ γ , a)
                                                              (λ ρ → τ (transR (≤→R ψ) ρ))
                                                              (λ ρ → δ (transR (≤→R ψ) ρ))
reflect (app {A} {B} d e)        γ τ δ = bind {A ⇒ B} {B} (reflect d γ τ δ)
                                           λ ψ f → f refl≤ (mono⊩ {A} ψ (reflect e γ τ δ))
reflect (box {A} d)              γ τ δ = return {□ A}
                                           λ ρ → graft⊢ ∙ (τ ρ) d ,
                                                  reflect d ∙
                                                            (λ ρ′ → τ (transR ρ ρ′))
                                                            (λ ρ′ → δ (transR ρ ρ′))
reflect (unbox {A} {C} d e)      γ τ δ = bind {□ A} {C} (reflect d γ τ δ)
                                           λ ψ s → reflect e (mono⊩⋆ ψ γ)
                                                              (λ ρ → τ (transR (≤→R ψ) ρ) , π₁ (s ρ))
                                                              (λ ρ → δ (transR (≤→R ψ) ρ) , π₂ (s ρ))
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
                                                                     (λ ρ → τ (transR (≤→R ψ) ρ))
                                                                     (λ ρ → δ (transR (≤→R ψ) ρ))
                                             ; ψ (ι₂ b) → reflect f (mono⊩⋆ ψ γ , b)
                                                                     (λ ρ → τ (transR (≤→R ψ) ρ))
                                                                     (λ ρ → δ (transR (≤→R ψ) ρ))
                                             }


-- The canonical model.

private
  instance
    canon : Model
    canon = record
      { World   = Context
      ; _≤_     = _⊆²_
      ; refl≤   = refl⊆²
      ; trans≤  = trans⊆²
      ; _R_     = λ { (_ ⁏ Δ) (_ ⁏ Δ′) → Δ ⊆ Δ′ }
      ; reflR   = refl⊆
      ; transR  = trans⊆
      ; _⊩ᵅ_   = λ { (Γ ⁏ Δ) P → Γ ⁏ Δ ⊢ⁿᵉ α P }
      ; mono⊩ᵅ = mono⊢ⁿᵉ
      ; peek    = id
      ; R⨾≤→R  = λ { (_ , (ρ , (_ , ρ′))) → trans⊆ ρ ρ′ }
      }


-- Soundness and completeness of syntax with respect to the canonical model.

mutual
  reflectᶜ : ∀ {A Γ Δ} → Γ ⁏ Δ ⊢ⁿᵉ A → Γ ⁏ Δ ⊩ A
  reflectᶜ {α P}    d = return {α P} d
  reflectᶜ {A ⇒ B} d = return {A ⇒ B}
                          λ ψ a → reflectᶜ (appⁿᵉ (mono⊢ⁿᵉ ψ d) (reifyᶜ a))
  reflectᶜ {□ A}    d = λ ψ κ → neⁿᶠ (unboxⁿᵉ (mono⊢ⁿᵉ ψ d)
                                               (κ (refl⊆ , weak⊆)
                                                  λ ρ′ → mono⊢ (done , ρ′) (mvar top) ,
                                                          reflectᶜ (mono⊢ⁿᵉ (done , ρ′) (mvarⁿᵉ top))))
  reflectᶜ {A ⩕ B}  d = return {A ⩕ B} (reflectᶜ (fstⁿᵉ d) , reflectᶜ (sndⁿᵉ d))
  reflectᶜ {⫪}     d = return {⫪} ∙
  reflectᶜ {⫫}     d = λ ψ κ → neⁿᶠ (boomⁿᵉ (mono⊢ⁿᵉ ψ d))
  reflectᶜ {A ⩖ B}  d = λ ψ κ → neⁿᶠ (caseⁿᵉ (mono⊢ⁿᵉ ψ d)
                                              (κ (weak⊆ , refl⊆) (ι₁ (reflectᶜ (varⁿᵉ top))))
                                              (κ (weak⊆ , refl⊆) (ι₂ (reflectᶜ (varⁿᵉ top)))))

  reifyᶜ : ∀ {A Γ Δ} → Γ ⁏ Δ ⊩ A → Γ ⁏ Δ ⊢ⁿᶠ A
  reifyᶜ {α P}    κ = κ refl⊆²
                        λ ψ s → neⁿᶠ s
  reifyᶜ {A ⇒ B} κ = κ refl⊆²
                        λ ψ f → lamⁿᶠ (reifyᶜ (f (weak⊆ , refl⊆) (reflectᶜ (varⁿᵉ top))))
  reifyᶜ {□ A}    κ = κ refl⊆²
                        λ ψ f → boxⁿᶠ (π₁ (f {∅ ⁏ _} refl⊆))
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
refl⊩⋆ {Γ , A} = mono⊩⋆ (weak⊆ , refl⊆) refl⊩⋆ , reflectᶜ (varⁿᵉ top)

mrefl⊩⋆ : ∀ {Δ Γ} → Γ ⁏ Δ ⊩⋆ Δ
mrefl⊩⋆ {∅}     = ∙
mrefl⊩⋆ {Δ , A} = mono⊩⋆ (refl⊆ , weak⊆) mrefl⊩⋆ , reflectᶜ (mvarⁿᵉ top)

reify : ∀ {Γ Δ A} → Γ ⁏ Δ ⊨ A → Γ ⁏ Δ ⊢ⁿᶠ A
reify s = reifyᶜ (s refl⊩⋆ (λ ρ → mono⊢⋆ (refl⊆ , ρ) mrefl⊢⋆)
                            (λ ρ → mono⊩⋆ (refl⊆ , ρ) mrefl⊩⋆))


-- Normalisation by evaluation.

nbe : ∀ {Γ Δ A} → Γ ⁏ Δ ⊢ A → Γ ⁏ Δ ⊢ⁿᶠ A
nbe = reify ∘ reflect
