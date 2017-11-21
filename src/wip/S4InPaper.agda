module S4InPaper where

open import Prelude public


--------------------------------------------------------------------------------
--
-- Syntax


-- Types
infixr 7 _⊃_
data Tp : Set where
  ♭   : Tp
  _⊃_ : Tp → Tp → Tp
  □_  : Tp → Tp


-- Contexts
Cx : Set
Cx = List² Tp Tp


-- Syntactic entailment
infix 3 _⊢_
data _⊢_ : Cx → Tp → Set
  where
    ᵐᵛ  : ∀ {A Δ Γ} → Δ ∋ A
                    → Δ ⁏ Γ ⊢ A

    ᵛ   : ∀ {A Δ Γ} → Γ ∋ A
                    → Δ ⁏ Γ ⊢ A

    ƛ   : ∀ {A B Δ Γ} → Δ ⁏ Γ , A ⊢ B
                      → Δ ⁏ Γ ⊢ A ⊃ B

    _$_ : ∀ {A B Δ Γ} → Δ ⁏ Γ ⊢ A ⊃ B → Δ ⁏ Γ ⊢ A
                      → Δ ⁏ Γ ⊢ B

    ⌜_⌝ : ∀ {A Δ Γ} → Δ ⁏ ∅ ⊢ A
                    → Δ ⁏ Γ ⊢ □ A

    ⌞_⌟ : ∀ {A C Δ Γ} → Δ ⁏ Γ ⊢ □ A → Δ , A ⁏ Γ ⊢ C
                      → Δ ⁏ Γ ⊢ C


-- Normal and neutral forms
mutual
  infix 3 _⊢ₙ_
  data _⊢ₙ_ : Cx → Tp → Set
    where
      ƛ   : ∀ {A B Δ Γ} → Δ ⁏ Γ , A ⊢ₙ B
                        → Δ ⁏ Γ ⊢ₙ A ⊃ B

      ⌜_⌝ : ∀ {A Δ Γ} → Δ ⁏ ∅ ⊢ A
                      → Δ ⁏ Γ ⊢ₙ □ A

      ⌞_⌟ : ∀ {A C Δ Γ} → Δ ⁏ Γ ⊢ₙₑ □ A → Δ , A ⁏ Γ ⊢ₙ C
                        → Δ ⁏ Γ ⊢ₙ C

      ⁿᵉ  : ∀ {Δ Γ} → Δ ⁏ Γ ⊢ₙₑ ♭
                    → Δ ⁏ Γ ⊢ₙ ♭

  infix 3 _⊢ₙₑ_
  data _⊢ₙₑ_ : Cx → Tp → Set
    where
      ᵐᵛ  : ∀ {A Δ Γ} → Δ ∋ A
                      → Δ ⁏ Γ ⊢ₙₑ A

      ᵛ   : ∀ {A Δ Γ} → Γ ∋ A
                      → Δ ⁏ Γ ⊢ₙₑ A

      _$_ : ∀ {A B Δ Γ} → Δ ⁏ Γ ⊢ₙₑ A ⊃ B → Δ ⁏ Γ ⊢ₙ A
                        → Δ ⁏ Γ ⊢ₙₑ B


mutual
  embₙ : ∀ {Δ Γ A} → Δ ⁏ Γ ⊢ₙ A → Δ ⁏ Γ ⊢ A
  embₙ (ƛ M)     = ƛ (embₙ M)
  embₙ (⌜ M ⌝)   = ⌜ M ⌝
  embₙ (⌞ M ⌟ N) = ⌞ embₙₑ M ⌟ (embₙ N)
  embₙ (ⁿᵉ M)    = embₙₑ M

  embₙₑ : ∀ {Δ Γ A} → Δ ⁏ Γ ⊢ₙₑ A → Δ ⁏ Γ ⊢ A
  embₙₑ (ᵐᵛ i)  = ᵐᵛ i
  embₙₑ (ᵛ i)   = ᵛ i
  embₙₑ (M $ N) = embₙₑ M $ embₙ N


--------------------------------------------------------------------------------
--
-- Renaming


ᵐren : ∀ {Δ Δ′ Γ A} → Δ′ ⊇ Δ → Δ ⁏ Γ ⊢ A
                    → Δ′ ⁏ Γ ⊢ A
ᵐren η (ᵐᵛ i)    = ᵐᵛ (renᵢ η i)
ᵐren η (ᵛ i)     = ᵛ i
ᵐren η (ƛ M)     = ƛ (ᵐren η M)
ᵐren η (M $ N)   = ᵐren η M $ ᵐren η N
ᵐren η (⌜ M ⌝)   = ⌜ ᵐren η M ⌝
ᵐren η (⌞ M ⌟ N) = ⌞ ᵐren η M ⌟ (ᵐren (keep η) N)

ren : ∀ {Δ Γ Γ′ A} → Γ′ ⊇ Γ → Δ ⁏ Γ ⊢ A
                   → Δ ⁏ Γ′ ⊢ A
ren η (ᵐᵛ i)    = ᵐᵛ i
ren η (ᵛ i)     = ᵛ (renᵢ η i)
ren η (ƛ M)     = ƛ (ren (keep η) M)
ren η (M $ N)   = ren η M $ ren η N
ren η (⌜ M ⌝)   = ⌜ M ⌝
ren η (⌞ M ⌟ N) = ⌞ ren η M ⌟ (ren η N)


mutual
  ᵐrenₙ : ∀ {Δ Δ′ Γ A} → Δ′ ⊇ Δ → Δ ⁏ Γ ⊢ₙ A
                       → Δ′ ⁏ Γ ⊢ₙ A
  ᵐrenₙ η (ƛ M)     = ƛ (ᵐrenₙ η M)
  ᵐrenₙ η (⌜ M ⌝)   = ⌜ ᵐren η M ⌝
  ᵐrenₙ η (⌞ M ⌟ N) = ⌞ ᵐrenₙₑ η M ⌟ (ᵐrenₙ (keep η) N)
  ᵐrenₙ η (ⁿᵉ M)    = ⁿᵉ (ᵐrenₙₑ η M)

  ᵐrenₙₑ : ∀ {Δ Δ′ Γ A} → Δ′ ⊇ Δ → Δ ⁏ Γ ⊢ₙₑ A
                        → Δ′ ⁏ Γ ⊢ₙₑ A
  ᵐrenₙₑ η (ᵐᵛ i)  = ᵐᵛ (renᵢ η i)
  ᵐrenₙₑ η (ᵛ i )  = ᵛ i
  ᵐrenₙₑ η (M $ N) = ᵐrenₙₑ η M $ ᵐrenₙ η N


mutual
  renₙ : ∀ {Δ Γ Γ′ A} → Γ′ ⊇ Γ → Δ ⁏ Γ ⊢ₙ A
                      → Δ ⁏ Γ′ ⊢ₙ A
  renₙ η (ƛ M)     = ƛ (renₙ (keep η) M)
  renₙ η (⌜ M ⌝)   = ⌜ M ⌝
  renₙ η (⌞ M ⌟ N) = ⌞ renₙₑ η M ⌟ (renₙ η N)
  renₙ η (ⁿᵉ M)    = ⁿᵉ (renₙₑ η M)

  renₙₑ : ∀ {Δ Γ Γ′ A} → Γ′ ⊇ Γ → Δ ⁏ Γ ⊢ₙₑ A
                       → Δ ⁏ Γ′ ⊢ₙₑ A
  renₙₑ η (ᵐᵛ i)  = ᵐᵛ i
  renₙₑ η (ᵛ i)   = ᵛ (renᵢ η i)
  renₙₑ η (M $ N) = renₙₑ η M $ renₙ η N


renₙ² : ∀ {Δ Δ′ Γ Γ′ A} → Δ′ ⁏ Γ′ ⊇² Δ ⁏ Γ → Δ ⁏ Γ ⊢ₙ A
                        → Δ′ ⁏ Γ′ ⊢ₙ A
renₙ² η M = (ᵐrenₙ (proj₁ η) ∘ renₙ (proj₂ η)) M

renₙₑ² : ∀ {Δ Δ′ Γ Γ′ A} → Δ′ ⁏ Γ′ ⊇² Δ ⁏ Γ → Δ ⁏ Γ ⊢ₙₑ A
                         → Δ′ ⁏ Γ′ ⊢ₙₑ A
renₙₑ² η M = (ᵐrenₙₑ (proj₁ η) ∘ renₙₑ (proj₂ η)) M


--------------------------------------------------------------------------------
--
-- Substitution


-- Simultaneous substitutions
infix 3 _⊢⋆_
_⊢⋆_ : Cx → List Tp → Set
Δ ⁏ Γ ⊢⋆ Ξ = All (Δ ⁏ Γ ⊢_) Ξ


ᵐren⋆ : ∀ {Δ Δ′ Γ Ξ} → Δ′ ⊇ Δ → Δ ⁏ Γ ⊢⋆ Ξ
                     → Δ′ ⁏ Γ ⊢⋆ Ξ
ᵐren⋆ η σ = mapAll (ᵐren η) σ

ren⋆ : ∀ {Δ Γ Γ′ Ξ} → Γ′ ⊇ Γ → Δ ⁏ Γ ⊢⋆ Ξ
                     → Δ ⁏ Γ′ ⊢⋆ Ξ
ren⋆ η σ = mapAll (ren η) σ


ᵐdropₛ : ∀ {Δ Γ Ξ A} → Δ ⁏ Γ ⊢⋆ Ξ
                     → Δ , A ⁏ Γ ⊢⋆ Ξ
ᵐdropₛ σ = ᵐren⋆ (drop idᵣ) σ

dropₛ : ∀ {Δ Γ Ξ A} → Δ ⁏ Γ ⊢⋆ Ξ
                    → Δ ⁏ Γ , A ⊢⋆ Ξ
dropₛ σ = ren⋆ (drop idᵣ) σ

ᵐkeepₛ : ∀ {Δ Γ Ξ A} → Δ ⁏ Γ ⊢⋆ Ξ
                     → Δ , A ⁏ Γ ⊢⋆ Ξ , A
ᵐkeepₛ σ = ᵐdropₛ σ , ᵐᵛ zero

keepₛ : ∀ {Δ Γ Ξ A} → Δ ⁏ Γ ⊢⋆ Ξ
                    → Δ ⁏ Γ , A ⊢⋆ Ξ , A
keepₛ σ = dropₛ σ , ᵛ zero


ᵐidₛ : ∀ {Δ Γ} → Δ ⁏ Γ ⊢⋆ Δ
ᵐidₛ {∅}     = ∅
ᵐidₛ {Γ , A} = ᵐkeepₛ ᵐidₛ

idₛ : ∀ {Γ Δ} → Δ ⁏ Γ ⊢⋆ Γ
idₛ {∅}     = ∅
idₛ {Γ , A} = keepₛ idₛ


subᵢ : ∀ {Δ Γ Ξ A} → Δ ⁏ Γ ⊢⋆ Ξ → Ξ ∋ A
                   → Δ ⁏ Γ ⊢ A
subᵢ σ i = lookupAll σ i


-- Substitution
ᵐsub : ∀ {Δ Γ Ξ A} → Δ ⁏ ∅ ⊢⋆ Ξ → Ξ ⁏ Γ ⊢ A
                   → Δ ⁏ Γ ⊢ A
ᵐsub σ (ᵐᵛ i)    = ren infᵣ (subᵢ σ i)
ᵐsub σ (ᵛ i)     = ᵛ i
ᵐsub σ (ƛ M)     = ƛ (ᵐsub σ M)
ᵐsub σ (M $ N)   = ᵐsub σ M $ ᵐsub σ N
ᵐsub σ ⌜ M ⌝     = ⌜ ᵐsub σ M ⌝
ᵐsub σ (⌞ M ⌟ N) = ⌞ ᵐsub σ M ⌟ (ᵐsub (ᵐkeepₛ σ) N)

sub : ∀ {Δ Γ Ξ A} → Δ ⁏ Γ ⊢⋆ Ξ → Δ ⁏ Ξ ⊢ A
                  → Δ ⁏ Γ ⊢ A
sub σ (ᵐᵛ i)    = ᵐᵛ i
sub σ (ᵛ i)     = subᵢ σ i
sub σ (ƛ M)     = ƛ (sub (keepₛ σ) M)
sub σ (M $ N)   = sub σ M $ sub σ N
sub σ ⌜ M ⌝     = ⌜ M ⌝
sub σ (⌞ M ⌟ N) = ⌞ sub σ M ⌟ (sub (ᵐdropₛ σ) N)


--------------------------------------------------------------------------------
--
-- 3. Semantics


-- Definition 3.1 (Introspective Kripke models)
record 𝔎 : Set₁ where
  field
    𝒲    : Set

    𝒱    : 𝒲 → Set

    _≥_  : 𝒲 → 𝒲 → Set

    idₐ  : ∀ {w} → w ≥ w

    _∘ₐ_ : ∀ {w w′ w″} → w′ ≥ w → w″ ≥ w′
                       → w″ ≥ w

    relᵥ : ∀ {w w′} → w′ ≥ w → 𝒱 w
                    → 𝒱 w′

    ⌊_⌋  : 𝒲 → Cx

    ⌊_⌋ₐ : ∀ {w w′} → w′ ≥ w
                    → ⌊ w′ ⌋ ⊇² ⌊ w ⌋

  ᵐ⌊_⌋ : 𝒲 → List Tp
  ᵐ⌊ w ⌋ = proj₁ ⌊ w ⌋

  ᵐ⌊_⌋ₐ : ∀ {w w′} → w′ ≥ w
                   → ᵐ⌊ w′ ⌋ ⊇ ᵐ⌊ w ⌋
  ᵐ⌊ η ⌋ₐ = proj₁ ⌊ η ⌋ₐ

open 𝔎 {{...}} public


-- Definition 3.2 (Values)
mutual
  infix 3 _∣_⊩_
  _∣_⊩_ : ∀ {{𝔐 : 𝔎}} (𝔐′ : 𝔎) {{_ : 𝔐 ≡ 𝔐′}} → 𝒲 → Tp → Set

  𝔐 ∣ w ⊩ ♭     = 𝒱 w

  𝔐 ∣ w ⊩ A ⊃ B = ∀ {w′} → w′ ≥ w → 𝔐 ∣ w′ ⊩ₖ A
                          → 𝔐 ∣ w′ ⊩ₖ B

  𝔐 ∣ w ⊩ □ A   = 𝔐 ∣ w ⊩ⱼₖ A

  infix 3 _∣_⊩ₖ_
  _∣_⊩ₖ_ : ∀ {{𝔐 : 𝔎}} (𝔐′ : 𝔎) {{_ : 𝔐 ≡ 𝔐′}} → 𝒲 → Tp → Set
  𝔐 ∣ w ⊩ₖ A = ∀ {C w′} → w′ ≥ w → (∀ {w″} → w″ ≥ w′ → 𝔐 ∣ w″ ⊩ A
                                              → ⌊ w″ ⌋ ⊢ₙ C)
                         → ⌊ w′ ⌋ ⊢ₙ C

  infix 3 _∣_⊩ⱼₖ_
  _∣_⊩ⱼₖ_ : ∀ {{𝔐 : 𝔎}} (𝔐′ : 𝔎) {{_ : 𝔐 ≡ 𝔐′}} → 𝒲 → Tp → Set
  𝔐 ∣ w ⊩ⱼₖ A = ᵐ⌊ w ⌋ ⁏ ∅ ⊢ A × 𝔐 ∣ w ⊩ₖ A


-- Lemma 3.3
syn : ∀ {{𝔐 : 𝔎}} {A w} → 𝔐 ∣ w ⊩ⱼₖ A
                        → ᵐ⌊ w ⌋ ⁏ ∅ ⊢ A
syn p = proj₁ p

sem : ∀ {{𝔐 : 𝔎}} {A w} → 𝔐 ∣ w ⊩ⱼₖ A
                        → 𝔐 ∣ w ⊩ₖ A
sem p = proj₂ p


-- Lemma 3.4
mutual
  rel : ∀ {{𝔐 : 𝔎}} {A w w′} → w′ ≥ w → 𝔐 ∣ w ⊩ A
                             → 𝔐 ∣ w′ ⊩ A
  rel {♭}     ξ v = relᵥ ξ v
  rel {A ⊃ B} ξ f = \ ξ′ k → f (ξ ∘ₐ ξ′) k
  rel {□ A}   ξ p = relⱼₖ ξ p

  relₖ : ∀ {{𝔐 : 𝔎}} {A w w′} → w′ ≥ w → 𝔐 ∣ w ⊩ₖ A
                              → 𝔐 ∣ w′ ⊩ₖ A
  relₖ ξ k = \ ξ′ f → k (ξ ∘ₐ ξ′) f

  relⱼₖ : ∀ {{𝔐 : 𝔎}} {A w w′} → w′ ≥ w → 𝔐 ∣ w ⊩ⱼₖ A
                               → 𝔐 ∣ w′ ⊩ⱼₖ A
  relⱼₖ {A} ξ p = ᵐren ᵐ⌊ ξ ⌋ₐ (syn p) , relₖ {A} ξ (sem p)


-- Lemma 3.5
return : ∀ {{𝔐 : 𝔎}} {A w} → 𝔐 ∣ w ⊩ A
                           → 𝔐 ∣ w ⊩ₖ A
return {A} a = \ ξ f → f idₐ (rel {A} ξ a)

bind : ∀ {{𝔐 : 𝔎}} {A C w} → 𝔐 ∣ w ⊩ₖ A → (∀ {w′} → w′ ≥ w → 𝔐 ∣ w′ ⊩ A
                                                     → 𝔐 ∣ w′ ⊩ₖ C)
                           → 𝔐 ∣ w ⊩ₖ C
bind k f = \ ξ f′ →
             k ξ (\ ξ′ a →
               f (ξ ∘ₐ ξ′) a idₐ (\ ξ″ b →
                 f′ (ξ′ ∘ₐ ξ″) b))


-- Definition 3.6 (Environments)
infix 3 _∣_⊩ₖ⋆_
_∣_⊩ₖ⋆_ : ∀ {{𝔐 : 𝔎}} (𝔐′ : 𝔎) {{_ : 𝔐 ≡ 𝔐′}} → 𝒲 → List Tp → Set
𝔐 ∣ w ⊩ₖ⋆ Γ = All (𝔐 ∣ w ⊩ₖ_) Γ

infix 3 _∣_⊩ⱼₖ⋆_
_∣_⊩ⱼₖ⋆_ : ∀ {{𝔐 : 𝔎}} (𝔐′ : 𝔎) {{_ : 𝔐 ≡ 𝔐′}} → 𝒲 → List Tp → Set
𝔐 ∣ w ⊩ⱼₖ⋆ Δ = All (𝔐 ∣ w ⊩ⱼₖ_) Δ


-- Lemma 3.7
syn⋆ : ∀ {{𝔐 : 𝔎}} {Δ w} → 𝔐 ∣ w ⊩ⱼₖ⋆ Δ
                         → ᵐ⌊ w ⌋ ⁏ ∅ ⊢⋆ Δ
syn⋆ δ = mapAll syn δ

sem⋆ : ∀ {{𝔐 : 𝔎}} {Δ w} → 𝔐 ∣ w ⊩ⱼₖ⋆ Δ
                         → 𝔐 ∣ w ⊩ₖ⋆ Δ
sem⋆ δ = mapAll sem δ


-- Lemma 3.8
relₖ⋆ : ∀ {{𝔐 : 𝔎}} {Γ w w′} → w′ ≥ w → 𝔐 ∣ w ⊩ₖ⋆ Γ
                             → 𝔐 ∣ w′ ⊩ₖ⋆ Γ
relₖ⋆ ξ γ = mapAll (\ {A} k {C} {w′} → relₖ {A} ξ (\ {D} {w″} → k {D} {w″})) γ
-- NOTE: We should be able to write this as follows:
-- relₖ⋆ ξ γ = mapAll (relₖ ξ) γ

relⱼₖ⋆ : ∀ {{𝔐 : 𝔎}} {Δ w w′} → w′ ≥ w → 𝔐 ∣ w ⊩ⱼₖ⋆ Δ
                              → 𝔐 ∣ w′ ⊩ⱼₖ⋆ Δ
relⱼₖ⋆ ξ δ = mapAll (relⱼₖ ξ) δ


-- Lemma 3.9
lookup : ∀ {{𝔐 : 𝔎}} {Γ A w} → 𝔐 ∣ w ⊩ₖ⋆ Γ → Γ ∋ A
                             → 𝔐 ∣ w ⊩ₖ A
lookup γ i = lookupAll γ i


-- Definition 3.10 (Semantic entailment)
infix 3 _⊨_
_⊨_ : Cx → Tp → Set₁
Δ ⁏ Γ ⊨ A = ∀ {{𝔐 : 𝔎}} {w} → 𝔐 ∣ w ⊩ⱼₖ⋆ Δ → 𝔐 ∣ w ⊩ₖ⋆ Γ
                             → 𝔐 ∣ w ⊩ₖ A


-- Theorem 3.11 (Soundness)
↓ : ∀ {Δ Γ A} → Δ ⁏ Γ ⊢ A
              → Δ ⁏ Γ ⊨ A
↓ (ᵐᵛ i)            = \ δ γ → lookup (sem⋆ δ) i
↓ (ᵛ i)             = \ δ γ → lookup γ i
↓ (ƛ {A} {B} M)     = \ δ γ → return {A ⊃ B} (\ ξ k →
                        ↓ M (relⱼₖ⋆ ξ δ) (relₖ⋆ ξ γ , k))
↓ (_$_ {A} {B} M N) = \ δ γ → bind {A ⊃ B} {B} (↓ M δ γ) (\ ξ f →
                        f idₐ (↓ N (relⱼₖ⋆ ξ δ) (relₖ⋆ ξ γ)))
↓ (⌜_⌝ {A} M)       = \ δ γ → return {□ A} (ᵐsub (syn⋆ δ) M , ↓ M δ ∅)
↓ (⌞_⌟ {A} {C} M N) = \ δ γ → bind {□ A} {C} (↓ M δ γ) (\ ξ p →
                        ↓ N (relⱼₖ⋆ ξ δ , p) (relₖ⋆ ξ γ))


-- -- --------------------------------------------------------------------------------
-- -- --
-- -- -- Completeness


-- -- -- Universal model
-- -- instance
-- --   𝔐ᵤ : 𝔎
-- --   𝔐ᵤ = record
-- --          { 𝒲    = Cx
-- --          ; _𝒱_  = _𝒱ᵤ_
-- --          ; _≥_  = _⊇²_
-- --          ; idₐ  = idᵣ²
-- --          ; _∘ₐ_ = _∘ᵣ²_
-- --          ; relᵥ = renₙ²
-- --          ; ⌊_⌋  = id
-- --          ; ⌊_⌋ₐ = id
-- --          }
-- --     where
-- --       infix 3 _𝒱ᵤ_
-- --       _𝒱ᵤ_ : Cx → TVar → Set
-- --       Δ ⁏ Γ 𝒱ᵤ x = Δ ⁏ Γ ⊢ₙ ᵗᵛ x


-- -- -- Soundness and completeness with respect to the universal model
-- -- mutual
-- --   ↓ᵤ : ∀ {A Δ Γ} → Δ ⁏ Γ ⊢ₙₑ A
-- --                  → Δ ⁏ Γ ⊩ₖ A
-- --   ↓ᵤ {ᵗᵛ x}  M = return {ᵗᵛ x} (ⁿᵉ M)
-- --   ↓ᵤ {A ⊃ B} M = return {A ⊃ B} (\ η k → ↓ᵤ (renₙₑ² η M $ ↑ᵤ k))
-- --   ↓ᵤ {A ∧ B} M = return {A ∧ B} (↓ᵤ (π₁ M) , ↓ᵤ (π₂ M))
-- --   ↓ᵤ {TT}    M = return {TT} tt
-- --   ↓ᵤ {□ A}   M = \ η f → ⌞ renₙₑ² η M ⌟ (f (ᵐdrop² idᵣ²) (ᵐᵛ zero , ↓ᵤ (ᵐᵛ zero)))

-- --   ↑ᵤ : ∀ {A Δ Γ} → Δ ⁏ Γ ⊩ₖ A
-- --                  → Δ ⁏ Γ ⊢ₙ A
-- --   ↑ᵤ {ᵗᵛ x}  k = k idᵣ² (\ η v → v)
-- --   ↑ᵤ {A ⊃ B} k = k idᵣ² (\ η f → ƛ (↑ᵤ (f (drop² idᵣ²) (↓ᵤ (ᵛ zero)))))
-- --   ↑ᵤ {A ∧ B} k = k idᵣ² (\ η p → ↑ᵤ (proj₁ p) , ↑ᵤ (proj₂ p))
-- --   ↑ᵤ {TT}    k = k idᵣ² (\ η t → tt)
-- --   ↑ᵤ {□ A}   k = k idᵣ² (\ η p → ⌜ syn p ⌝)


-- -- ᵐidₑ : ∀ {Δ Γ} → Δ ⁏ Γ ⊩ⱼₖ⋆ Δ
-- -- ᵐidₑ {∅}     = ∅
-- -- ᵐidₑ {Δ , A} = relⱼₖ⋆ (ᵐdrop² idᵣ²) ᵐidₑ , (ᵐᵛ zero , ↓ᵤ (ᵐᵛ zero))

-- -- idₑ : ∀ {Γ Δ} → Δ ⁏ Γ ⊩ₖ⋆ Γ
-- -- idₑ {∅}     = ∅
-- -- idₑ {Γ , A} = relₖ⋆ (drop² idᵣ²) idₑ , ↓ᵤ (ᵛ zero)


-- -- -- Completeness
-- -- ↑ : ∀ {Δ Γ A} → Δ ⁏ Γ ⊨ A
-- --               → Δ ⁏ Γ ⊢ₙ A
-- -- ↑ f = ↑ᵤ (f ᵐidₑ idₑ)


-- -- -- Normalisation
-- -- nbe : ∀ {Δ Γ A} → Δ ⁏ Γ ⊢ A
-- --                 → Δ ⁏ Γ ⊢ₙ A
-- -- nbe = ↑ ∘ ↓


-- -- --------------------------------------------------------------------------------
-- -- --
-- -- -- Examples


-- -- ᵐᵛ0 : ∀ {Δ Γ A} → Δ , A ⁏ Γ ⊢ A
-- -- ᵐᵛ0 = ᵐᵛ zero

-- -- ᵐᵛ1 : ∀ {Δ Γ A B} → Δ , A , B ⁏ Γ ⊢ A
-- -- ᵐᵛ1 = ᵐᵛ (suc zero)

-- -- ᵐᵛ2 : ∀ {Δ Γ A B C} → Δ , A , B , C ⁏ Γ ⊢ A
-- -- ᵐᵛ2 = ᵐᵛ (suc (suc zero))


-- -- ᵛ0 : ∀ {Δ Γ A} → Δ ⁏ Γ , A ⊢ A
-- -- ᵛ0 = ᵛ zero

-- -- ᵛ1 : ∀ {Δ Γ A B} → Δ ⁏ Γ , A , B ⊢ A
-- -- ᵛ1 = ᵛ (suc zero)

-- -- ᵛ2 : ∀ {Δ Γ A B C} → Δ ⁏ Γ , A , B , C ⊢ A
-- -- ᵛ2 = ᵛ (suc (suc zero))


-- -- ᵃˣI : ∀ {A Δ Γ} → Δ ⁏ Γ ⊢ A ⊃ A
-- -- ᵃˣI = ƛ ᵛ0

-- -- ᵃˣK : ∀ {A B Δ Γ} → Δ ⁏ Γ ⊢ A ⊃ B ⊃ A
-- -- ᵃˣK = ƛ (ƛ ᵛ1)

-- -- ᵃˣS : ∀ {A B C Δ Γ} → Δ ⁏ Γ ⊢ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
-- -- ᵃˣS = ƛ (ƛ (ƛ ((ᵛ2 $ ᵛ0) $ (ᵛ1 $ ᵛ0))))


-- -- ᵃˣD : ∀ {A B Δ Γ} → Δ ⁏ Γ ⊢ □ (A ⊃ B) ⊃ □ A ⊃ □ B
-- -- ᵃˣD = ƛ (ƛ (⌞ ᵛ1 ⌟ (⌞ ᵛ0 ⌟ ⌜ ᵐᵛ1 $ ᵐᵛ0 ⌝)))

-- -- ᵃˣT : ∀ {A Δ Γ} → Δ ⁏ Γ ⊢ □ A ⊃ A
-- -- ᵃˣT = ƛ (⌞ ᵛ0 ⌟ ᵐᵛ0)

-- -- ᵃˣ4 : ∀ {A Δ Γ} → Δ ⁏ Γ ⊢ □ A ⊃ □ □ A
-- -- ᵃˣ4 = ƛ (⌞ ᵛ0 ⌟ ⌜ ⌜ ᵐᵛ0 ⌝ ⌝)


-- -- --------------------------------------------------------------------------------
-- -- --
-- -- -- Conversion tests


-- -- test∼ : ∀ {Δ Γ A} → Δ ⁏ Γ ⊢ A → Δ ⁏ Γ ⊢ A → Set
-- -- test∼ M₁ M₂ = embₙ (nbe M₁) ≡ M₂


-- -- -- red⊃ : ∀ {Δ Γ A B} → (M : Δ ⁏ Γ , A ⊢ B) (N : Δ ⁏ Γ ⊢ A)
-- -- --                    → ƛ M $ N ∼ sub (idₛ , N) M

-- -- test∼red⊃ : test∼ {∅} {∅ , "A"}
-- --                   ((ƛ ᵛ0) $ ᵛ0)
-- --                   ᵛ0
-- -- test∼red⊃ = refl


-- -- -- red∧₁ : ∀ {Δ Γ A B} → (M : Δ ⁏ Γ ⊢ A) (N : Δ ⁏ Γ ⊢ B)
-- -- --                     → π₁ (M , N) ∼ M

-- -- test∼red∧₁ : test∼ {∅} {∅ , "A" , "B"}
-- --                    (π₁ (ᵛ1 , ᵛ0))
-- --                    ᵛ1
-- -- test∼red∧₁ = refl


-- -- -- red∧₂ : ∀ {Δ Γ A B} → (M : Δ ⁏ Γ ⊢ A) (N : Δ ⁏ Γ ⊢ B)
-- -- --                     → π₂ (M , N) ∼ N

-- -- test∼red∧₂ : test∼ {∅} {∅ , "A" , "B"}
-- --                    (π₂ (ᵛ1 , ᵛ0))
-- --                    ᵛ0
-- -- test∼red∧₂ = refl


-- -- -- red□ : ∀ {Δ Γ A C} → (M : Δ ⁏ ∅ ⊢ A) (N : Δ , A ⁏ Γ ⊢ C)
-- -- --                    → ⌞ ⌜ M ⌝ ⌟ N ∼ ᵐsub (ᵐidₛ , M) N

-- -- test∼red□ : test∼ {∅ , "A"} {∅}
-- --                   (⌞ ⌜ ᵐᵛ0 ⌝ ⌟ ᵐᵛ0)
-- --                   ᵐᵛ0
-- -- test∼red□ = refl


-- -- -- exp⊃ : ∀ {Δ Γ A B} → (M : Δ ⁏ Γ ⊢ A ⊃ B)
-- -- --                    → M ∼ ƛ (ren (drop idᵣ) M $ ᵛ0)

-- -- test∼exp⊃ : test∼ {∅} {∅ , "A" ⊃ "B"}
-- --                   ᵛ0
-- --                   (ƛ (ren (drop idᵣ) ᵛ0 $ ᵛ0))
-- -- test∼exp⊃ = refl


-- -- -- exp∧ : ∀ {Δ Γ A B} → (M : Δ ⁏ Γ ⊢ A ∧ B)
-- -- --                    → M ∼ π₁ M , π₂ M

-- -- test∼exp∧ : test∼ {∅} {∅ , "A" ∧ "B"}
-- --                   ᵛ0
-- --                   (π₁ ᵛ0 , π₂ ᵛ0)
-- -- test∼exp∧ = refl


-- -- -- expTT : ∀ {Δ Γ} → (M : Δ ⁏ Γ ⊢ 𝔗)
-- -- --                 → M ∼ tt

-- -- test∼expTT : test∼ {∅} {∅ , TT}
-- --                    ᵛ0
-- --                    tt
-- -- test∼expTT = refl


-- -- -- exp□ : ∀ {Δ Γ} → (M : Δ ⁏ Γ ⊢ □ A)
-- -- --                → M ∼ ⌞ M ⌟ ⌜ ᵐᵛ0 ⌝

-- -- test∼exp□ : test∼ {∅} {∅ , □ "A"}
-- --                   ᵛ0
-- --                   (⌞ ᵛ0 ⌟ ⌜ ᵐᵛ0 ⌝)
-- -- test∼exp□ = refl


-- -- -- comm□$ : ∀ {Δ Γ A B} → (𝒬 : Δ ⁏ Γ ⊢ □ (A ⊃ B))
-- -- --                         (M : Δ , A ⊃ B ⁏ Γ ⊢ A ⊃ B) (N : Δ ⁏ Γ ⊢ A)
-- -- --                      → (⌞ 𝒬 ⌟ M) $ N ∼ ⌞ 𝒬 ⌟ (M $ (ᵐren (drop idᵣ) N))

-- -- test∼comm□$ : test∼ {∅} {∅ , □ ("A" ⊃ "B") , "A"}
-- --                     ((⌞ ᵛ1 ⌟ ᵐᵛ0) $ ᵛ0)
-- --                     (⌞ ᵛ1 ⌟ (ᵐᵛ0 $ ᵐren (drop idᵣ) ᵛ0))
-- -- test∼comm□$ = refl


-- -- -- comm□⌞⌟ : ∀ {Δ Γ A C} → (𝒬 : Δ ⁏ Γ ⊢ □ □ A)
-- -- --                          (M : Δ , □ A ⁏ Γ ⊢ □ A) (N : Δ , A ⁏ Γ ⊢ C)
-- -- --                       → ⌞ (⌞ 𝒬 ⌟ M) ⌟ N ∼ ⌞ 𝒬 ⌟ (⌞ M ⌟ (ᵐren (drop idᵣ) N))

-- -- test∼comm□⌞⌟ : test∼ {∅} {∅ , □ □ "A"}
-- --                      (⌞ ⌞ ᵛ0 ⌟ ᵐᵛ0 ⌟ ᵐᵛ0)
-- --                      (⌞ ᵛ0 ⌟ (⌞ ᵐᵛ0 ⌟ ᵐᵛ0))
-- -- test∼comm□⌞⌟ = refl


-- -- -- comm□π₁ : ∀ {Δ Γ A B} → (𝒬 : Δ ⁏ Γ ⊢ □ (A ∧ B))
-- -- --                          (M : Δ , A ∧ B ⁏ Γ ⊢ A ∧ B)
-- -- --                       → π₁ (⌞ 𝒬 ⌟ M) ∼ ⌞ 𝒬 ⌟ (π₁ M)

-- -- test∼comm□π₁ : test∼ {∅} {∅ , □ ("A" ∧ "B")}
-- --                      (π₁ (⌞ ᵛ0 ⌟ ᵐᵛ0))
-- --                      (⌞ ᵛ0 ⌟ (π₁ ᵐᵛ0))
-- -- test∼comm□π₁ = refl


-- -- -- comm□π₂ : ∀ {Δ Γ A B} → (𝒬 : Δ ⁏ Γ ⊢ □ (A ∧ B))
-- -- --                          (M : Δ , A ∧ B ⁏ Γ ⊢ A ∧ B)
-- -- --                       → π₂ (⌞ 𝒬 ⌟ M) ∼ ⌞ 𝒬 ⌟ (π₂ M)

-- -- test∼comm□π₂ : test∼ {∅} {∅ , □ ("A" ∧ "B")}
-- --                      (π₂ (⌞ ᵛ0 ⌟ ᵐᵛ0))
-- --                      (⌞ ᵛ0 ⌟ (π₂ ᵐᵛ0))
-- -- test∼comm□π₂ = refl


-- -- --------------------------------------------------------------------------------
-- -- --
-- -- -- Self-interpretation


-- -- -- weakBP : ∀ {Δ Γ A B} → (M : Δ ⁏ Γ ⊢ A)
-- -- --                      → TT $ ⌜ M ⌝ ∼ ⌜ M ⌝

-- -- test∼weakBP : test∼ {∅ , "A"} {∅}
-- --                     (ᵃˣT $ ⌜ ᵐᵛ0 ⌝)
-- --                     ᵐᵛ0
-- -- test∼weakBP = refl


-- -- -- Andrej : ∀ {Δ Γ A B} → (M : Δ ⁏ Γ ⊢ A ⊃ B) (N : Δ ⁏ Γ ⊢ A)
-- -- --                      → (𝔻 $ ⌜ M ⌝) $ ⌜ N ⌝ ∼ ⌜ M $ N ⌝

-- -- test∼Andrej : test∼ {∅ , "A" ⊃ "B" , "A"} {∅}
-- --                     ((ᵃˣD $ ⌜ ᵐᵛ1 ⌝) $ ⌜ ᵐᵛ0 ⌝)
-- --                     (⌜ ᵐᵛ1 $ ᵐᵛ0 ⌝)
-- -- test∼Andrej = refl


-- -- --------------------------------------------------------------------------------
