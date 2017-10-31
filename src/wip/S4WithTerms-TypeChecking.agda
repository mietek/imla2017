module S4WithTerms-TypeChecking where

open import S4WithTerms public


--------------------------------------------------------------------------------
--
-- Bidirectional syntax


-- Checkable and inferrable forms
-- NOTE: Almost the same as normal and neutral forms
mutual
  infix 3 _⊢_⇐_
  data _⊢_⇐_ : 𝒞 → Term → 𝒯 → Set
    where
      ƛ_∙_   : ∀ {A B M Δ Γ} → (x : RVar) (𝒟 : Δ ⁏ Γ , (x , A) ⊢ M ⇐ B)
                             → Δ ⁏ Γ ⊢ ƛ x ∙ M ⇐ A ⊃ B

      _,_    : ∀ {A B M N Δ Γ} → (𝒟 : Δ ⁏ Γ ⊢ M ⇐ A) (ℰ : Δ ⁏ Γ ⊢ N ⇐ B)
                               → Δ ⁏ Γ ⊢ M , N ⇐ A ∧ B

      tt     : ∀ {Δ Γ} → Δ ⁏ Γ ⊢ tt ⇐ 𝕋

      -- NOTE: We can already represent non-normal forms,
      -- so there's nothing special to do here
      ⌜_⌝    : ∀ {A M Δ Γ} → (𝒟 : Δ ⁏ ∅ ⊢ M ⇐ A)
                           → Δ ⁏ Γ ⊢ ⌜ M ⌝ ⇐ □ A

      ⌞_⌟_∙_ : ∀ {A C M N Δ Γ} → (𝒟 : Δ ⁏ Γ ⊢ M ⇒ □ A) (x : MVar) (ℰ : Δ , (x , A) ⁏ Γ ⊢ N ⇐ C)
                               → Δ ⁏ Γ ⊢ ⌞ M ⌟ x ∙ N ⇐ C

      -- NOTE: We embed inferrable forms at all types
      ⁱⁿ     : ∀ {A M Δ Γ} → (𝒟 : Δ ⁏ Γ ⊢ M ⇒ A)
                           → Δ ⁏ Γ ⊢ M ⇐ A

  infix 3 _⊢_⇒_
  data _⊢_⇒_ : 𝒞 → Term → 𝒯 → Set
    where
      ᵐᵛ_#_ : ∀ {A Δ Γ} → (x : MVar) (i : Δ ∋ (x , A))
                        → Δ ⁏ Γ ⊢ ᵐᵛ x ⇒ A

      ʳᵛ_#_ : ∀ {A Δ Γ} → (x : RVar) (i : Γ ∋ (x , A))
                        → Δ ⁏ Γ ⊢ ʳᵛ x ⇒ A

      _$_   : ∀ {A B M N Δ Γ} → (𝒟 : Δ ⁏ Γ ⊢ M ⇒ A ⊃ B) (ℰ : Δ ⁏ Γ ⊢ N ⇐ A)
                              → Δ ⁏ Γ ⊢ M $ N ⇒ B

      π₁    : ∀ {A B M Δ Γ} → (𝒟 : Δ ⁏ Γ ⊢ M ⇒ A ∧ B)
                            → Δ ⁏ Γ ⊢ π₁ M ⇒ A

      π₂    : ∀ {A B M Δ Γ} → (𝒟 : Δ ⁏ Γ ⊢ M ⇒ A ∧ B)
                            → Δ ⁏ Γ ⊢ π₂ M ⇒ B

      -- NOTE: We can represent non-normal forms with the annotation rule
      _⦂_   : ∀ {A M Δ Γ} → (𝒟 : Δ ⁏ Γ ⊢ M ⇐ A) (A′ : 𝒯) {{_ : A ≡ A′}}
                          → Δ ⁏ Γ ⊢ M ⦂ A ⇒ A


-- NOTE: We could have a separate type for terms without annotations
embₜₘ : Term → Term
embₜₘ (ᵐᵛ x)        = ᵐᵛ x
embₜₘ (ʳᵛ x)        = ʳᵛ x
embₜₘ (ƛ x ∙ M)     = ƛ x ∙ embₜₘ M
embₜₘ (M $ N)       = embₜₘ M $ embₜₘ N
embₜₘ (M , N)       = embₜₘ M , embₜₘ N
embₜₘ (π₁ M)        = π₁ (embₜₘ M) 
embₜₘ (π₂ M)        = π₂ (embₜₘ M)
embₜₘ tt            = tt
embₜₘ ⌜ M ⌝         = ⌜ embₜₘ M ⌝
embₜₘ (⌞ M ⌟ x ∙ N) = ⌞ embₜₘ M ⌟ x ∙ embₜₘ N
embₜₘ (M ⦂ A)       = embₜₘ M

mutual
  emb⇐ : ∀ {Δ Γ M A} → Δ ⁏ Γ ⊢ M ⇐ A → Δ ⁏ Γ ⊢ embₜₘ M ∷ A
  emb⇐ (ƛ x ∙ 𝒟)     = ƛ x ∙ emb⇐ 𝒟
  emb⇐ (𝒟 , ℰ)       = emb⇐ 𝒟 , emb⇐ ℰ
  emb⇐ tt            = tt
  emb⇐ (⌜ 𝒟 ⌝)       = ⌜ emb⇐ 𝒟 ⌝
  emb⇐ (⌞ 𝒟 ⌟ x ∙ ℰ) = ⌞ emb⇒ 𝒟 ⌟ x ∙ emb⇐ ℰ
  emb⇐ (ⁱⁿ 𝒟)        = emb⇒ 𝒟

  emb⇒ : ∀ {Δ Γ M A} → Δ ⁏ Γ ⊢ M ⇒ A → Δ ⁏ Γ ⊢ embₜₘ M ∷ A
  emb⇒ (ᵐᵛ x # i) = ᵐᵛ x # i
  emb⇒ (ʳᵛ x # i) = ʳᵛ x # i
  emb⇒ (𝒟 $ ℰ)    = emb⇒ 𝒟 $ emb⇐ ℰ
  emb⇒ (π₁ 𝒟)     = π₁ (emb⇒ 𝒟)
  emb⇒ (π₂ 𝒟)     = π₂ (emb⇒ 𝒟)
  emb⇒ (𝒟 ⦂ A)    = emb⇐ 𝒟
  

--------------------------------------------------------------------------------
--
-- Bidirectional type checking


mfind : (Δ : List (MVar × 𝒯)) (x : MVar) → String ⊎ Σ 𝒯 (λ A → Δ ∋ (x , A))
mfind ∅              x = inj₁ "mfind|∅"
mfind (Δ , (x′ , A)) x with x ≟ₘᵥ x′
…                     | yes refl = inj₂ (A , zero)
…                     | no x≢y   = for⊎ (mfind Δ x)
                                      (_⧺ " mfind|,")
                                      (mapΣ id suc)

rfind : (Γ : List (RVar × 𝒯)) (x : RVar) → String ⊎ Σ 𝒯 (λ A → Γ ∋ (x , A))
rfind ∅              x = inj₁ "rfind|∅"
rfind (Γ , (x′ , A)) x with x ≟ᵣᵥ x′
…                     | yes refl = inj₂ (A , zero)
…                     | no x≢y   = for⊎ (rfind Γ x)
                                      (_⧺ " rfind|,")
                                      (mapΣ id suc)


-- Type checking and type inference
mutual
  check : ∀ {Δ Γ} M A → String ⊎ Δ ⁏ Γ ⊢ M ⇐ A

  check M@(ᵐᵛ _)                  A       = switch M A

  check M@(ʳᵛ _)                  A       = switch M A

  check (ƛ _ ∙ _)                 (ᵗᵛ _)  = inj₁ "check|ƛ|ᵗᵛ"
  check {Γ = Γ} (ƛ x ∙ M)         (A ⊃ B) = for⊎ (check {Γ = Γ , (x , A)} M B)
                                              ("check|ƛ|⊃ " ⧺_)
                                              (ƛ x ∙_)
  check (ƛ _ ∙ _)                 (_ ∧ _) = inj₁ "check|ƛ|∧"
  check (ƛ _ ∙ _)                 𝕋       = inj₁ "check|ƛ|𝕋"
  check (ƛ _ ∙ _)                 (□ _)   = inj₁ "check|ƛ|□"

  check M@(_ $ _)                 A       = switch M A

  check (_ , _)                   (ᵗᵛ _)  = inj₁ "check|,|ᵗᵛ"
  check (_ , _)                   (_ ⊃ _) = inj₁ "check|,|⊃"
  check (M , N)                   (A ∧ B) = elim⊎ (check M A)
                                              (λ s → inj₁ ("check|,|∧|1 " ⧺ s))
                                              (λ 𝒟 → for⊎ (check N B)
                                                        ("check|,|∧|2 " ⧺_)
                                                        (𝒟 ,_))
  check (_ , _)                   𝕋       = inj₁ "check|,|𝕋"
  check (_ , _)                   (□ _)   = inj₁ "check|,|□"

  check M@(π₁ _)                  A       = switch M A

  check M@(π₂ _)                  A       = switch M A

  check tt                        (ᵗᵛ _)  = inj₁ "check|tt|ᵗᵛ"
  check tt                        (_ ⊃ _) = inj₁ "check|tt|⊃"
  check tt                        (_ ∧ _) = inj₁ "check|tt|∧"
  check tt                        𝕋       = inj₂ tt
  check tt                        (□ _)   = inj₁ "check|tt|□"

  check ⌜ _ ⌝                     (ᵗᵛ _)  = inj₁ "check|⌜⌝|ᵗᵛ"
  check ⌜ _ ⌝                     (_ ⊃ _) = inj₁ "check|⌜⌝|⊃"
  check ⌜ _ ⌝                     (_ ∧ _) = inj₁ "check|⌜⌝|∧"
  check ⌜ _ ⌝                     𝕋       = inj₁ "check|⌜⌝|𝕋"
  check ⌜ M ⌝                     (□ A)   = for⊎ (check {Γ = ∅} M A)
                                              ("check|⌜⌝|□ " ⧺_)
                                              ⌜_⌝

  check {Δ = Δ} {Γ} (⌞ M ⌟ x ∙ N) C       = elim⊎ (infer {Δ = Δ} {Γ} M)
                                              (λ s → inj₁ ("check|⌞⌟|1 " ⧺ s))
                                              (λ { (ᵗᵛ x  , 𝒟) → inj₁ "check|⌞⌟|ᵗᵛ"
                                                 ; (A ⊃ B , 𝒟) → inj₁ "check|⌞⌟|⊃"
                                                 ; (A ∧ B , 𝒟) → inj₁ "check|⌞⌟|∧"
                                                 ; (𝕋     , 𝒟) → inj₁ "check|⌞⌟|𝕋"
                                                 ; (□ A   , 𝒟) → for⊎ (check {Δ = Δ , (x , A)} N C)
                                                                    ("check|⌞⌟|2 " ⧺_)
                                                                    (⌞ 𝒟 ⌟ x ∙_)
                                                 })

  check M@(_ ⦂ _)                 A       = switch M A


  switch : ∀ {Δ Γ} M A → String ⊎ Δ ⁏ Γ ⊢ M ⇐ A
  switch M A = elim⊎ (infer M)
                 (λ s → inj₁ ("switch|1 " ⧺ s))
                 (λ { (A′ , 𝒟) → case A ≟ₜₚ A′ of
                                    (λ { (yes refl) → inj₂ (ⁱⁿ 𝒟)
                                       ; (no x≢y)   → inj₁ "switch|2"
                                       })
                    })


  infer : ∀ {Δ Γ} M → String ⊎ Σ 𝒯 (λ A → Δ ⁏ Γ ⊢ M ⇒ A)

  infer {Δ = Δ} (ᵐᵛ x) = for⊎ (mfind Δ x)
                           ("infer|ᵐᵛ " ⧺_)
                           (mapΣ id (ᵐᵛ x #_))

  infer {Γ = Γ} (ʳᵛ x) = for⊎ (rfind Γ x)
                           ("infer|ʳᵛ " ⧺_)
                           (mapΣ id (ʳᵛ x #_))

  infer (ƛ _ ∙ _)      = inj₁ "infer|ƛ"

  infer (M $ N)        = elim⊎ (infer M)
                           (λ s → inj₁ ("infer|$|1 " ⧺ s))
                           (λ { (ᵗᵛ _  , 𝒟) → inj₁ "infer|$|ᵗᵛ"
                              ; (A ⊃ B , 𝒟) → for⊎ (check N A)
                                                 ("infer|$|⊃ " ⧺_)
                                                 (λ ℰ → B , 𝒟 $ ℰ)
                              ; (_ ∧ _ , 𝒟) → inj₁ "infer|$|∧"
                              ; (𝕋     , 𝒟) → inj₁ "infer|$|𝕋"
                              ; (□ _   , 𝒟) → inj₁ "infer|$|□"
                              })

  infer (_ , _)        = inj₁ "infer|,"

  infer (π₁ M)         = elim⊎ (infer M)
                           (λ s → inj₁ ("infer|π₁|1 " ⧺ s))
                           (λ { (ᵗᵛ _  , 𝒟) → inj₁ "infer|π₁|ᵗᵛ"
                              ; (_ ⊃ _ , 𝒟) → inj₁ "infer|π₁|⊃"
                              ; (A ∧ B , 𝒟) → inj₂ (A , π₁ 𝒟)
                              ; (𝕋     , 𝒟) → inj₁ "infer|π₁|𝕋"
                              ; (□ _   , 𝒟) → inj₁ "infer|π₁|□"
                              })

  infer (π₂ M)         = elim⊎ (infer M)
                           (λ s → inj₁ ("infer|π₁|1 " ⧺ s))
                           (λ { (ᵗᵛ _  , 𝒟) → inj₁ "infer|π₁|ᵗᵛ"
                              ; (_ ⊃ _ , 𝒟) → inj₁ "infer|π₁|⊃"
                              ; (A ∧ B , 𝒟) → inj₂ (B , π₂ 𝒟)
                              ; (𝕋     , 𝒟) → inj₁ "infer|π₁|𝕋"
                              ; (□ _   , 𝒟) → inj₁ "infer|π₁|□"
                              })

  infer tt             = inj₁ "infer|tt"

  infer ⌜ _ ⌝          = inj₁ "infer|⌜⌝"

  infer (⌞ _ ⌟ _ ∙ _)  = inj₁ "infer|⌞⌟"

  infer (M ⦂ A)        = for⊎ (check M A)
                           ("infer|⦂ " ⧺_)
                           (λ 𝒟 → A , (𝒟 ⦂ A))


-- Normalisation on terms
nmₜₘ : ∀ {Δ Γ} → Term → String ⊎ Term
nmₜₘ {Δ} {Γ} M = elim⊎ (infer {Δ} {Γ} M)
                   (λ s         → inj₁ s)
                   (λ { (A , 𝒟) → case nm (emb⇒ 𝒟) of
                                     (λ { (M′ , 𝒟′) → inj₂ M′
                                        })
                      })


--------------------------------------------------------------------------------
--
-- Examples


ᵐᵛ0ᵢₙ : ∀ {A Δ Γ} → (x : MVar) → Δ , (x , A) ⁏ Γ ⊢ ᵐᵛ x ⇒ A
ᵐᵛ0ᵢₙ x = ᵐᵛ x # zero

ᵐᵛ1ᵢₙ : ∀ {A yB Δ Γ} → (x : MVar) → Δ , (x , A) , yB ⁏ Γ ⊢ ᵐᵛ x ⇒ A
ᵐᵛ1ᵢₙ x = ᵐᵛ x # suc zero

ᵐᵛ2ᵢₙ : ∀ {A yB zC Δ Γ} → (x : MVar) → Δ , (x , A) , yB , zC ⁏ Γ ⊢ ᵐᵛ x ⇒ A
ᵐᵛ2ᵢₙ x = ᵐᵛ x # suc (suc zero)


ʳᵛ0ᵢₙ : ∀ {A Δ Γ} → (x : RVar) → Δ ⁏ Γ , (x , A) ⊢ ʳᵛ x ⇒ A
ʳᵛ0ᵢₙ x = ʳᵛ x # zero

ʳᵛ1ᵢₙ : ∀ {A yB Δ Γ} → (x : RVar) → Δ ⁏ Γ , (x , A) , yB ⊢ ʳᵛ x ⇒ A
ʳᵛ1ᵢₙ x = ʳᵛ x # suc zero

ʳᵛ2ᵢₙ : ∀ {A yB zC Δ Γ} → (x : RVar) → Δ ⁏ Γ , (x , A) , yB , zC ⊢ ʳᵛ x ⇒ A
ʳᵛ2ᵢₙ x = ʳᵛ x # suc (suc zero)


--------------------------------------------------------------------------------
--
-- Type checking tests


test⇐ : ∀ {Δ Γ} M A → Δ ⁏ Γ ⊢ M ⇐ A → Set
test⇐ M A 𝒟 = check M A ≡ inj₂ 𝒟


test⇐axI : test⇐ {∅} {∅}
                   axIₜₘ
                   ("A" ⊃ "A")
                   (ƛ "x" ∙ ⁱⁿ (ʳᵛ0ᵢₙ "x"))
test⇐axI = refl


test⇐axK : test⇐ {∅} {∅}
                   axKₜₘ
                   ("A" ⊃ "B" ⊃ "A")
                   (ƛ "x" ∙ (ƛ "y" ∙ ⁱⁿ (ʳᵛ1ᵢₙ "x")))
test⇐axK = refl


test⇐axS : test⇐ {∅} {∅}
                   axSₜₘ
                   (("A" ⊃ "B" ⊃ "C") ⊃ ("A" ⊃ "B") ⊃ "A" ⊃ "C")
                   (ƛ "f" ∙ (ƛ "g" ∙ (ƛ "x" ∙
                     ⁱⁿ ((ʳᵛ2ᵢₙ "f" $ ⁱⁿ (ʳᵛ0ᵢₙ "x")) $ ⁱⁿ (ʳᵛ1ᵢₙ "g" $ ⁱⁿ (ʳᵛ0ᵢₙ "x"))))))
test⇐axS = refl


test⇐axD : test⇐ {∅} {∅}
                   axDₜₘ
                   (□ ("A" ⊃ "B") ⊃ □ "A" ⊃ □ "B")
                   (ƛ "'f" ∙ (ƛ "'x" ∙
                     (⌞ ʳᵛ1ᵢₙ "'f" ⌟ "f" ∙ (⌞ ʳᵛ0ᵢₙ "'x" ⌟ "x" ∙
                       ⌜ ⁱⁿ (ᵐᵛ1ᵢₙ "f" $ ⁱⁿ (ᵐᵛ0ᵢₙ "x")) ⌝))))
test⇐axD = refl


test⇐axT : test⇐ {∅} {∅}
                   axTₜₘ
                   (□ "A" ⊃ "A")
                   (ƛ "'x" ∙ (⌞ ʳᵛ0ᵢₙ "'x" ⌟ "x" ∙ ⁱⁿ (ᵐᵛ0ᵢₙ "x")))
test⇐axT = refl


test⇐ax4 : test⇐ {∅} {∅}
                   ax4ₜₘ
                   (□ "A" ⊃ □ □ "A")
                   (ƛ "'x" ∙ (⌞ ʳᵛ0ᵢₙ "'x" ⌟ "x" ∙ ⌜ ⌜ ⁱⁿ (ᵐᵛ0ᵢₙ "x") ⌝ ⌝))
test⇐ax4 = refl


--------------------------------------------------------------------------------
--
-- Type inference tests


test⇒ : ∀ {Δ Γ} M → (A : 𝒯) → Δ ⁏ Γ ⊢ M ⇒ A → Set
test⇒ M A 𝒟 = elim⊎ (infer M)
                 (λ s  → ⊥)
                 (λ A𝒟 → A , 𝒟 ≡ A𝒟)


test⇒axI : test⇒ {∅} {∅}
                   (axIₜₘ ⦂ ("A" ⊃ "A"))
                   ("A" ⊃ "A")
                   (ƛ "x" ∙ ⁱⁿ (ʳᵛ0ᵢₙ "x") ⦂ ("A" ⊃ "A"))
test⇒axI = refl


--------------------------------------------------------------------------------
--
-- Conversion tests


test∼ₜₘ : ∀ {Δ Γ} → Term → Term → Set
test∼ₜₘ {Δ} {Γ} M₁ M₂ = elim⊎ (nmₜₘ {Δ} {Γ} M₁)
                          (λ s   → ⊥)
                          (λ M₁′ → M₁′ ≡ M₂)


test∼red⊃ₜₘ : test∼ₜₘ {∅} {∅ , ("a" , "A")}
                      ((ƛ "x" ∙ ʳᵛ "x" ⦂ ("A" ⊃ "A")) $ ʳᵛ "a")
                      (ʳᵛ "a")
test∼red⊃ₜₘ = refl


test∼red∧₁ₜₘ : test∼ₜₘ {∅} {∅ , ("a" , "A") , ("b" , "B")}
                       (π₁ ((ʳᵛ "a" , ʳᵛ "b") ⦂ ("A" ∧ "B")))
                       (ʳᵛ "a")
test∼red∧₁ₜₘ = refl


test∼red∧₂ₜₘ : test∼ₜₘ {∅} {∅ , ("a" , "A") , ("b" , "B")}
                       (π₂ ((ʳᵛ "a" , ʳᵛ "b") ⦂ ("A" ∧ "B")))
                       (ʳᵛ "b")
test∼red∧₂ₜₘ = refl


test∼red□ₜₘ : test∼ₜₘ {∅ , ("a" , "A")} {∅}
                      (⌞ ⌜ ᵐᵛ "a" ⌝ ⦂ □ "A" ⌟ "x" ∙ ᵐᵛ "x" ⦂ "A")
                      (ᵐᵛ "a")
test∼red□ₜₘ = refl


-- TODO: Generate type annotations
test∼exp⊃ₜₘ : test∼ₜₘ {∅} {∅ , ("f" , "A" ⊃ "B")}
                      (ʳᵛ "f")
                      (ƛ "RFRESH" ∙ (ʳᵛ "f" $ ʳᵛ "RFRESH"))
test∼exp⊃ₜₘ = refl


-- TODO: Generate type annotations
test∼exp∧ₜₘ : test∼ₜₘ {∅} {∅ , ("p" , "A" ∧ "B")}
                      (ʳᵛ "p")
                      (π₁ (ʳᵛ "p") , π₂ (ʳᵛ "p"))
test∼exp∧ₜₘ = refl


-- TODO: Generate type annotations
test∼exp𝕋ₜₘ : test∼ₜₘ {∅} {∅ , ("t" , 𝕋)}
                      (ʳᵛ "t")
                      tt
test∼exp𝕋ₜₘ = refl


-- TODO: Generate type annotations
test∼exp□ₜₘ : test∼ₜₘ {∅} {∅ , ("'a" , □ "A")}
                      (ʳᵛ "'a")
                      (⌞ ʳᵛ "'a" ⌟ "MFRESH" ∙ ⌜ ᵐᵛ "MFRESH" ⌝)
test∼exp□ₜₘ = refl


test∼comm□$ₜₘ : test∼ₜₘ {∅} {∅ , ("'f" , □ ("A" ⊃ "B")) , ("a" , "A")}
                        ((⌞ ʳᵛ "'f" ⌟ "x" ∙ ᵐᵛ "x" ⦂ ("A" ⊃ "B")) $ ʳᵛ "a")
                        ((⌞ ʳᵛ "'f" ⌟ "MFRESH" ∙ (ᵐᵛ "MFRESH" $ ʳᵛ "a")))
test∼comm□$ₜₘ = refl


test∼comm□⌞⌟ₜₘ : test∼ₜₘ {∅} {∅ , ("''a" , □ □ "A")}
                         (⌞ ⌞ ʳᵛ "''a" ⌟ "x" ∙ ᵐᵛ "x" ⦂ □ "A" ⌟ "y" ∙ ᵐᵛ "y" ⦂ "A")
                         (⌞ ʳᵛ "''a" ⌟ "MFRESH" ∙ ⌞ ᵐᵛ "MFRESH" ⌟ "MFRESH" ∙ ᵐᵛ "MFRESH")
test∼comm□⌞⌟ₜₘ = refl


test∼comm□π₁ₜₘ : test∼ₜₘ {∅} {∅ , ("'x" , □ ("A" ∧ "B"))}
                         (π₁ (⌞ ʳᵛ "'x" ⌟ "x" ∙ ᵐᵛ "x" ⦂ ("A" ∧ "B")))
                         (⌞ ʳᵛ "'x" ⌟ "MFRESH" ∙ π₁ (ᵐᵛ "MFRESH"))
test∼comm□π₁ₜₘ = refl


test∼comm□π₂ₜₘ : test∼ₜₘ {∅} {∅ , ("'x" , □ ("A" ∧ "B"))}
                         (π₂ (⌞ ʳᵛ "'x" ⌟ "x" ∙ ᵐᵛ "x" ⦂ ("A" ∧ "B")))
                         (⌞ ʳᵛ "'x" ⌟ "MFRESH" ∙ π₂ (ᵐᵛ "MFRESH"))
test∼comm□π₂ₜₘ = refl


--------------------------------------------------------------------------------
--
-- Self-interpretation


test∼weakBPₜₘ : test∼ₜₘ {∅ , ("x" , "A")} {∅}
                        ((axTₜₘ ⦂ (□ "A" ⊃ "A")) $ ⌜ ᵐᵛ "x" ⌝)
                        (ᵐᵛ "x")
test∼weakBPₜₘ = refl


test∼Andrejₜₘ : test∼ₜₘ {∅ , ("f" , "A" ⊃ "B") , ("x" , "A")} {∅}
                        (((axDₜₘ ⦂ (□ ("A" ⊃ "B") ⊃ □ "A" ⊃ □ "B")) $ ⌜ ᵐᵛ "f" ⌝) $ ⌜ ᵐᵛ "x" ⌝)
                        (⌜ ᵐᵛ "f" $ ᵐᵛ "x" ⌝)
test∼Andrejₜₘ = refl


--------------------------------------------------------------------------------
