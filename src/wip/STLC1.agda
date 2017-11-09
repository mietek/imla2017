module STLC1 where

open import Prelude


--------------------------------------------------------------------------------
--
-- Syntax


-- Types
infixr 7 _⇒_
data Type : Set
  where
    •    : Type
    _⇒_ : Type → Type → Type


-- Contexts
Context : Set
Context = List Type


-- Terms
infix 3 _⊢_
data _⊢_ : Context → Type → Set
  where
    var : ∀ {A Γ} → Γ ∋ A
                  ---------
                  → Γ ⊢ A

    lam : ∀ {A B Γ} → Γ , A ⊢ B
                    --------------
                    → Γ ⊢ A ⇒ B

    _$_ : ∀ {A B Γ} → Γ ⊢ A ⇒ B → Γ ⊢ A
                    ------------------------
                    → Γ ⊢ B


-- Renaming
ren : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢ A
                 -------------------
                 → Γ′ ⊢ A

ren η (var i) = var (lookupᵣ η i)
ren η (lam M) = lam (ren (lift η) M)
ren η (M $ N) = ren η M $ ren η N


-- Values
infix 3 _⊩_
_⊩_ : Context → Type → Set

w ⊩ •      = w ⊢ •

w ⊩ A ⇒ B = ∀ {w′} → w′ ⊇ w → w′ ⊩ A
                     --------------------
                     → w′ ⊩ B


-- Environments
infix 3 _⊩⋆_
_⊩⋆_ : Context → List Type → Set
w ⊩⋆ ∅     = ⊤
w ⊩⋆ Γ , A = w ⊩⋆ Γ × w ⊩ A


-- Semantic entailment
infix 3 _⊨_
_⊨_ : Context → Type → Set
Γ ⊨ A = ∀ {w} → w ⊩⋆ Γ
               ----------
               → w ⊩ A


-- Accessibility
mov : ∀ {A w w′} → w′ ⊇ w → w ⊩ A
                 -------------------
                 → w′ ⊩ A

mov {•}      η v = ren η v
mov {A ⇒ B} η f = λ η′ → f (η ∘ᵣ η′)


mov⋆ : ∀ {Γ w w′} → w′ ⊇ w → w ⊩⋆ Γ
                  --------------------
                  → w′ ⊩⋆ Γ

mov⋆ {∅}     η tt      = tt
mov⋆ {Γ , A} η (γ , a) = mov⋆ η γ , mov {A} η a


lookup : ∀ {Γ A w} → w ⊩⋆ Γ → Γ ∋ A
                   -------------------
                   → w ⊩ A

lookup {∅}     tt      ()
lookup {Γ , A} (γ , a) zero    = a
lookup {Γ , B} (γ , b) (suc i) = lookup γ i


-- Evaluation
↓ : ∀ {Γ A} → Γ ⊢ A
            ---------
            → Γ ⊨ A

↓ (var i) = λ γ → lookup γ i
↓ (lam M) = λ γ η a → ↓ M (mov⋆ η γ , a)
↓ (M $ N) = λ γ → (↓ M γ) idᵣ (↓ N γ)


-- Soundness and completeness with respect to the universal model
mutual
  ↓ᵤ : ∀ {A Γ} → Γ ⊢ A
               ---------
               → Γ ⊩ A

  ↓ᵤ {•}      M = M
  ↓ᵤ {A ⇒ B} M = λ η a → ↓ᵤ (ren η M $ ↑ᵤ a)


  ↑ᵤ : ∀ {A Γ} → Γ ⊩ A
               ---------
               → Γ ⊢ A

  ↑ᵤ {•}      v = v
  ↑ᵤ {A ⇒ B} f = lam (↑ᵤ (f (wk idᵣ) (↓ᵤ {A} (var zero))))


idₑ : ∀ {Γ} → Γ ⊩⋆ Γ

idₑ {∅}     = tt
idₑ {Γ , A} = mov⋆ (wk idᵣ) idₑ , ↓ᵤ {A} (var zero)


-- Completeness
↑ : ∀ {Γ A} → Γ ⊨ A
            ---------
            → Γ ⊢ A

↑ f = ↑ᵤ (f idₑ)


-- Normalisation
nm : ∀ {Γ A} → Γ ⊢ A
             ---------
             → Γ ⊢ A
nm = ↑ ∘ ↓
