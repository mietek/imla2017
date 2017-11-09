module STLC-Base-ANSI where

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


-- Terms, or syntactic entailment
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


mutual
  -- Terms in normal form
  infix 3 _⊢ₙₘ_
  data _⊢ₙₘ_ : Context → Type → Set
    where
      lam : ∀ {A B Γ} → Γ , A ⊢ₙₘ B
                      ----------------
                      → Γ ⊢ₙₘ A ⇒ B

      nt  : ∀ {Γ} → Γ ⊢ₙₜ •
                  -----------
                  → Γ ⊢ₙₘ •

  -- Terms in neutral form
  infix 3 _⊢ₙₜ_
  data _⊢ₙₜ_ : Context → Type → Set
    where
      var : ∀ {A Γ} → Γ ∋ A
                    -----------
                    → Γ ⊢ₙₜ A

      _$_ : ∀ {A B Γ} → Γ ⊢ₙₜ A ⇒ B → Γ ⊢ₙₘ A
                      ----------------------------
                      → Γ ⊢ₙₜ B


mutual
  embₙₘ : ∀ {Γ A} → Γ ⊢ₙₘ A
                  -----------
                  → Γ ⊢ A

  embₙₘ (lam M) = lam (embₙₘ M)
  embₙₘ (nt M)  = embₙₜ M


  embₙₜ : ∀ {Γ A} → Γ ⊢ₙₜ A
                  -----------
                  → Γ ⊢ A

  embₙₜ (var i) = var i
  embₙₜ (M $ N) = embₙₜ M $ embₙₘ N


--------------------------------------------------------------------------------
--
-- Renaming


ren : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢ A
                 -------------------
                 → Γ′ ⊢ A

ren η (var i) = var (lookupᵣ η i)
ren η (lam M) = lam (ren (lift η) M)
ren η (M $ N) = ren η M $ ren η N


mutual
  renₙₘ : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢ₙₘ A
                     ---------------------
                     → Γ′ ⊢ₙₘ A

  renₙₘ η (lam M) = lam (renₙₘ (lift η) M)
  renₙₘ η (nt M)  = nt (renₙₜ η M)


  renₙₜ : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢ₙₜ A
                     ---------------------
                     → Γ′ ⊢ₙₜ A

  renₙₜ η (var i) = var (lookupᵣ η i)
  renₙₜ η (M $ N) = renₙₜ η M $ renₙₘ η N


--------------------------------------------------------------------------------
--
-- Semantics


-- Kripke models
record 𝔎 : Set₁ where
  field
    𝒲    : Set

    𝒱    : 𝒲 → Set

    _≥_  : 𝒲 → 𝒲 → Set

    idₐ  : ∀ {w} → w ≥ w

    _∘ₐ_ : ∀ {w w′ w″} → w′ ≥ w → w″ ≥ w′
                       --------------------
                       → w″ ≥ w

    movᵥ : ∀ {w w′} → w′ ≥ w → 𝒱 w
                    ----------------
                    → 𝒱 w′

open 𝔎 {{…}} public


-- Values
infix 3 _⊩_
_⊩_ : ∀ {{𝔐 : 𝔎}} → 𝒲 → Type → Set

w ⊩ •      = 𝒱 w

w ⊩ A ⇒ B = ∀ {w′} → (η : w′ ≥ w) (k : w′ ⊩ A)
                     → w′ ⊩ B


-- Environments
infix 3 _⊩⋆_
_⊩⋆_ : ∀ {{𝔐 : 𝔎}} → 𝒲 → List Type → Set
w ⊩⋆ ∅     = ⊤
w ⊩⋆ Γ , A = w ⊩⋆ Γ × w ⊩ A


-- Semantic entailment
infix 3 _⊨_
_⊨_ : Context → Type → Set₁
Γ ⊨ A = ∀ {{𝔐 : 𝔎}} {w} → w ⊩⋆ Γ
                         → w ⊩ A


-- Accessibility
mov : ∀ {{𝔐 : 𝔎}} {A w w′} → w′ ≥ w → w ⊩ A
                           -------------------
                           → w′ ⊩ A
mov {•}      η v = movᵥ η v
mov {A ⇒ B} η f = λ η′ → f (η ∘ₐ η′)


mov⋆ : ∀ {{𝔐 : 𝔎}} {Γ w w′} → w′ ≥ w → w ⊩⋆ Γ
                            --------------------
                            → w′ ⊩⋆ Γ

mov⋆ {Γ = ∅}     η tt      = tt
mov⋆ {Γ = Γ , A} η (γ , a) = mov⋆ η γ , mov {A} η a


lookup : ∀ {{𝔐 : 𝔎}} {Γ A w} → w ⊩⋆ Γ → Γ ∋ A
                             -------------------
                             → w ⊩ A

lookup {Γ = ∅}     tt      ()
lookup {Γ = Γ , A} (γ , a) zero    = a
lookup {Γ = Γ , B} (γ , b) (suc i) = lookup γ i


-- Soundness
↓ : ∀ {Γ A} → Γ ⊢ A
            ---------
            → Γ ⊨ A

↓ (var i) = λ γ → lookup γ i
↓ (lam M) = λ γ η a → ↓ M (mov⋆ η γ , a)
↓ (M $ N) = λ γ → (↓ M γ) idₐ (↓ N γ)


--------------------------------------------------------------------------------
--
-- Completeness


-- Universal model
instance
  𝔐ᵤ : 𝔎
  𝔐ᵤ = record
         { 𝒲    = Context
         ; 𝒱    = _⊢ₙₘ •
         ; _≥_  = _⊇_
         ; idₐ  = idᵣ
         ; _∘ₐ_ = _∘ᵣ_
         ; movᵥ = renₙₘ
         }


-- Soundness and completeness with respect to the universal model
mutual
  ↓ᵤ : ∀ {A Γ} → Γ ⊢ₙₜ A
               → Γ ⊩ A
  ↓ᵤ {•}      M = nt M
  ↓ᵤ {A ⇒ B} M = λ η a → ↓ᵤ (renₙₜ η M $ ↑ᵤ a)

  ↑ᵤ : ∀ {A Γ} → Γ ⊩ A
               → Γ ⊢ₙₘ A
  ↑ᵤ {•}      v = v
  ↑ᵤ {A ⇒ B} f = lam (↑ᵤ (f (wk idᵣ) (↓ᵤ {A} (var zero))))


idₑ : ∀ {Γ} → Γ ⊩⋆ Γ
idₑ {∅}     = tt
idₑ {Γ , A} = mov⋆ (wk idᵣ) idₑ , ↓ᵤ {A} (var zero)


-- Completeness
↑ : ∀ {Γ A} → Γ ⊨ A
            → Γ ⊢ₙₘ A
↑ f = ↑ᵤ (f idₑ)


-- Normalisation
nm : ∀ {Γ A} → Γ ⊢ A
             → Γ ⊢ₙₘ A
nm = ↑ ∘ ↓



--------------------------------------------------------------------------------
--
-- Examples


v0 : ∀ {Γ A} → Γ , A ⊢ A
v0 = var zero

v1 : ∀ {Γ A B} → Γ , A , B ⊢ A
v1 = var (suc zero)

v2 : ∀ {Γ A B C} → Γ , A , B , C ⊢ A
v2 = var (suc (suc zero))


ᵃˣI : ∀ {A Γ} → Γ ⊢ A ⇒ A
ᵃˣI = lam v0

ᵃˣK : ∀ {A B Γ} → Γ ⊢ A ⇒ B ⇒ A
ᵃˣK = lam (lam v1)

ᵃˣS : ∀ {A B C Γ} → Γ ⊢ (A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C
ᵃˣS = lam (lam (lam ((v2 $ v0) $ (v1 $ v0))))


--------------------------------------------------------------------------------
--
-- Conversion tests


test∼ : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A → Set
test∼ M₁ M₂ = embₙₘ (nm M₁) ≡ M₂


-- red⇒ : ∀ {Γ A B} → (M : Γ , A ⊢ B) (N : Γ ⊢ A)
--                  → lam M $ N ∼ sub (idₛ , N) M

test∼red⇒ : test∼ {∅ , •}
                   ((lam v0) $ v0)
                   v0
test∼red⇒ = refl


-- exp⇒ : ∀ {Γ A B} → (M : Γ ⊢ A ⇒ B)
--                  → M ∼ lam (ren (wk idᵣ) M $ v0)

test∼exp⇒ : test∼ {∅ , • ⇒ •}
                   v0
                   (lam (ren (wk idᵣ) v0 $ v0))
test∼exp⇒ = refl


--------------------------------------------------------------------------------
