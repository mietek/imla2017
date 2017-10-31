module S4WithTerms-TypeChecking where

open import S4WithTerms public


--------------------------------------------------------------------------------
--
-- Bidirectional type checking


-- Bidirectional syntactic entailment
mutual
  infix 3 _⊢_⇐_
  data _⊢_⇐_ : 𝒞 → Term → 𝒯 → Set
    where
      ƛ_∙_   : ∀ {A B M Δ Γ} → (x : RVar) (𝒟 : Δ ⁏ Γ , (x , A) ⊢ M ⇐ B)
                             → Δ ⁏ Γ ⊢ ƛ x ∙ M ⇐ A ⊃ B

      _,_    : ∀ {A B M N Δ Γ} → (𝒟 : Δ ⁏ Γ ⊢ M ⇐ A) (ℰ : Δ ⁏ Γ ⊢ N ⇐ B)
                               → Δ ⁏ Γ ⊢ M , N ⇐ A ∧ B

      tt     : ∀ {Δ Γ} → Δ ⁏ Γ ⊢ tt ⇐ 𝕋

      ⌜_⌝    : ∀ {A M Δ Γ} → (𝒟 : Δ ⁏ ∅ ⊢ M ⇐ A)
                           → Δ ⁏ Γ ⊢ ⌜ M ⌝ ⇐ □ A

      ⌞_⌟_∙_ : ∀ {A C M N Δ Γ} → (𝒟 : Δ ⁏ Γ ⊢ M ⇒ □ A) (x : MVar) (ℰ : Δ , (x , A) ⁏ Γ ⊢ N ⇐ C)
                               → Δ ⁏ Γ ⊢ ⌞ M ⌟ x ∙ N ⇐ C

      ⁿᵗ     : ∀ {x M Δ Γ} → (𝒟 : Δ ⁏ Γ ⊢ M ⇒ ᵗᵛ x)
                           → Δ ⁏ Γ ⊢ M ⇐ ᵗᵛ x

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

      _⦂_   : ∀ {A M Δ Γ} → (𝒟 : Δ ⁏ Γ ⊢ M ⇐ A) (A′ : 𝒯) {{_ : A ≡ A′}}
                          → Δ ⁏ Γ ⊢ M ⦂ A ⇒ A


ᵐᵛ0ₙₜ : ∀ {A Δ Γ} → (x : MVar) → Δ , (x , A) ⁏ Γ ⊢ ᵐᵛ x ⇒ A
ᵐᵛ0ₙₜ x = ᵐᵛ x # zero

ᵐᵛ1ₙₜ : ∀ {A yB Δ Γ} → (x : MVar) → Δ , (x , A) , yB ⁏ Γ ⊢ ᵐᵛ x ⇒ A
ᵐᵛ1ₙₜ x = ᵐᵛ x # suc zero

ᵐᵛ2ₙₜ : ∀ {A yB zC Δ Γ} → (x : MVar) → Δ , (x , A) , yB , zC ⁏ Γ ⊢ ᵐᵛ x ⇒ A
ᵐᵛ2ₙₜ x = ᵐᵛ x # suc (suc zero)


ʳᵛ0ₙₜ : ∀ {A Δ Γ} → (x : RVar) → Δ ⁏ Γ , (x , A) ⊢ ʳᵛ x ⇒ A
ʳᵛ0ₙₜ x = ʳᵛ x # zero

ʳᵛ1ₙₜ : ∀ {A yB Δ Γ} → (x : RVar) → Δ ⁏ Γ , (x , A) , yB ⊢ ʳᵛ x ⇒ A
ʳᵛ1ₙₜ x = ʳᵛ x # suc zero

ʳᵛ2ₙₜ : ∀ {A yB zC Δ Γ} → (x : RVar) → Δ ⁏ Γ , (x , A) , yB , zC ⊢ ʳᵛ x ⇒ A
ʳᵛ2ₙₜ x = ʳᵛ x # suc (suc zero)


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


-- Type checking and type synthesis
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

  check {Δ = Δ} {Γ} (⌞ M ⌟ x ∙ N) C       = elim⊎ (synth {Δ = Δ} {Γ} M)
                                              (λ s → inj₁ ("check|⌞⌟|0 " ⧺ s))
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
  switch M (ᵗᵛ x)  = elim⊎ (synth M)
                       (λ s → inj₁ ("switch|ᵗᵛ|0 " ⧺ s) )
                       (λ { (ᵗᵛ y , 𝒟) → case x ≟ₜᵥ y of
                                            (λ { (yes refl) → inj₂ (ⁿᵗ 𝒟)
                                               ; (no x≢y)   → inj₁ "switch|ᵗᵛ|≢"
                                               })
                          ; (_ ⊃ _ , 𝒟) → inj₁ "switch|ᵗᵛ|⊃"
                          ; (_ ∧ _ , 𝒟) → inj₁ "switch|ᵗᵛ|∧"
                          ; (𝕋     , 𝒟) → inj₁ "switch|ᵗᵛ|𝕋"
                          ; (□ _   , 𝒟) → inj₁ "switch|ᵗᵛ|□"
                          })
  switch M (_ ⊃ _) = inj₁ "switch|⊃"
  switch M (_ ∧ _) = inj₁ "switch|∧"
  switch M 𝕋       = inj₁ "switch|𝕋"
  switch M (□ _)   = inj₁ "switch|□"


  synth : ∀ {Δ Γ} M → String ⊎ Σ 𝒯 (λ A → Δ ⁏ Γ ⊢ M ⇒ A)

  synth {Δ = Δ} (ᵐᵛ x) = for⊎ (mfind Δ x)
                           ("synth|ᵐᵛ " ⧺_)
                           (mapΣ id (ᵐᵛ x #_))

  synth {Γ = Γ} (ʳᵛ x) = for⊎ (rfind Γ x)
                           ("synth|ʳᵛ " ⧺_)
                           (mapΣ id (ʳᵛ x #_))

  synth (ƛ _ ∙ _)      = inj₁ "synth|ƛ"

  synth (M $ N)        = elim⊎ (synth M)
                           (λ s → inj₁ ("synth|$|0 " ⧺ s))
                           (λ { (ᵗᵛ _  , 𝒟) → inj₁ "synth|$|ᵗᵛ"
                              ; (A ⊃ B , 𝒟) → for⊎ (check N A)
                                                 ("synth|$|⊃ " ⧺_)
                                                 (λ ℰ → B , 𝒟 $ ℰ)
                              ; (_ ∧ _ , 𝒟) → inj₁ "synth|$|∧"
                              ; (𝕋     , 𝒟) → inj₁ "synth|$|𝕋"
                              ; (□ _   , 𝒟) → inj₁ "synth|$|□"
                              })

  synth (_ , _)        = inj₁ "synth|,"

  synth (π₁ M)         = elim⊎ (synth M)
                           (λ s → inj₁ ("synth|π₁|0 " ⧺ s))
                           (λ { (ᵗᵛ _  , 𝒟) → inj₁ "synth|π₁|ᵗᵛ"
                              ; (_ ⊃ _ , 𝒟) → inj₁ "synth|π₁|⊃"
                              ; (A ∧ B , 𝒟) → inj₂ (A , π₁ 𝒟)
                              ; (𝕋     , 𝒟) → inj₁ "synth|π₁|𝕋"
                              ; (□ _   , 𝒟) → inj₁ "synth|π₁|□"
                              })

  synth (π₂ M)         = elim⊎ (synth M)
                           (λ s → inj₁ ("synth|π₁|0 " ⧺ s))
                           (λ { (ᵗᵛ _  , 𝒟) → inj₁ "synth|π₁|ᵗᵛ"
                              ; (_ ⊃ _ , 𝒟) → inj₁ "synth|π₁|⊃"
                              ; (A ∧ B , 𝒟) → inj₂ (B , π₂ 𝒟)
                              ; (𝕋     , 𝒟) → inj₁ "synth|π₁|𝕋"
                              ; (□ _   , 𝒟) → inj₁ "synth|π₁|□"
                              })

  synth tt             = inj₁ "synth|tt"

  synth ⌜ _ ⌝          = inj₁ "synth|⌜⌝"

  synth (⌞ _ ⌟ _ ∙ _)  = inj₁ "synth|⌞⌟"

  synth (M ⦂ A)        = for⊎ (check M A)
                           ("synth|⦂ " ⧺_)
                           (λ 𝒟 → A , 𝒟 ⦂ A)


--------------------------------------------------------------------------------
--
-- Type checking tests


test⇐ : ∀ {Δ Γ} M A → (𝒟 : Δ ⁏ Γ ⊢ M ⇐ A) → Set
test⇐ M A 𝒟 = check M A ≡ inj₂ 𝒟


test⇐axI : test⇐ {∅} {∅}
                   (ƛ "x" ∙ ʳᵛ "x")
                   ("A" ⊃ "A")
                   (ƛ "x" ∙ ⁿᵗ (ʳᵛ0ₙₜ "x"))
test⇐axI = refl


test⇐axK : test⇐ {∅} {∅}
                   (ƛ "x" ∙ (ƛ "y" ∙ ʳᵛ "x"))
                   ("A" ⊃ "B" ⊃ "A")
                   (ƛ "x" ∙ (ƛ "y" ∙ ⁿᵗ (ʳᵛ1ₙₜ "x")))
test⇐axK = refl


test⇐axS : test⇐ {∅} {∅}
                   (ƛ "f" ∙ (ƛ "g" ∙ (ƛ "x" ∙
                     ((ʳᵛ "f" $ ʳᵛ "x") $ (ʳᵛ "g" $ ʳᵛ "x")))))
                   (("A" ⊃ "B" ⊃ "C") ⊃ ("A" ⊃ "B") ⊃ "A" ⊃ "C")
                   (ƛ "f" ∙ (ƛ "g" ∙ (ƛ "x" ∙
                     ⁿᵗ ((ʳᵛ2ₙₜ "f" $ ⁿᵗ (ʳᵛ0ₙₜ "x")) $ ⁿᵗ (ʳᵛ1ₙₜ "g" $ ⁿᵗ (ʳᵛ0ₙₜ "x"))))))
test⇐axS = refl


test⇐axD : test⇐ {∅} {∅}
                   (ƛ "'f" ∙ (ƛ "'x" ∙
                     (⌞ ʳᵛ "'f" ⌟ "f" ∙ (⌞ ʳᵛ "'x" ⌟ "x" ∙
                       ⌜ ᵐᵛ "f" $ ᵐᵛ "x" ⌝))))
                   (□ ("A" ⊃ "B") ⊃ □ "A" ⊃ □ "B")
                   (ƛ "'f" ∙ (ƛ "'x" ∙
                     (⌞ ʳᵛ1ₙₜ "'f" ⌟ "f" ∙ (⌞ ʳᵛ0ₙₜ "'x" ⌟ "x" ∙
                       ⌜ ⁿᵗ (ᵐᵛ1ₙₜ "f" $ ⁿᵗ (ᵐᵛ0ₙₜ "x")) ⌝))))
test⇐axD = refl


test⇐axT : test⇐ {∅} {∅}
                   (ƛ "'x" ∙ (⌞ ʳᵛ "'x" ⌟ "x" ∙ ᵐᵛ "x"))
                   (□ "A" ⊃ "A")
                   (ƛ "'x" ∙ (⌞ ʳᵛ0ₙₜ "'x" ⌟ "x" ∙ ⁿᵗ (ᵐᵛ0ₙₜ "x")))
test⇐axT = refl


test⇐ax4 : test⇐ {∅} {∅}
                   (ƛ "'x" ∙ (⌞ ʳᵛ "'x" ⌟ "x" ∙ ⌜ ⌜ ᵐᵛ "x" ⌝ ⌝))
                   (□ "A" ⊃ □ □ "A")
                   (ƛ "'x" ∙ (⌞ ʳᵛ0ₙₜ "'x" ⌟ "x" ∙ ⌜ ⌜ ⁿᵗ (ᵐᵛ0ₙₜ "x") ⌝ ⌝))
test⇐ax4 = refl


--------------------------------------------------------------------------------
