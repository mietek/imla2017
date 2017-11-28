module TNT5 where


--------------------------------------------------------------------------------
--
-- Naturals


module Naturals where
  open import Prelude


  _≟_ : (n m : Nat) → Dec (n ≡ m)
  zero  ≟ zero  = yes refl
  zero  ≟ suc m = no (λ ())
  suc n ≟ zero  = no (λ ())
  suc n ≟ suc m with n ≟ m
  ...           | yes refl = yes refl
  ...           | no n≢m   = no (n≢m ∘ injsuc)
   
   
  -- _≥_
   
  data _≥_ : Nat → Nat → Set
    where
      done : ∀ {n} → n ≥ zero
   
      keep : ∀ {n m} → n ≥ m
                     → suc n ≥ suc m
   
  drop≥ : ∀ {n m} → n ≥ m
                  → suc n ≥ m
  drop≥ done       = done
  drop≥ (keep n≥m) = keep (drop≥ n≥m)
   
  pred≥ : ∀ {n m} → suc n ≥ suc m
                  → n ≥ m
  pred≥ (keep n≥m) = n≥m
   
  refl≥ : ∀ {n} → n ≥ n
  refl≥ {zero}  = done
  refl≥ {suc n} = keep refl≥
   
  trans≥ : ∀ {n m k} → n ≥ m → m ≥ k
                     → n ≥ k
  trans≥ n≥m        done       = done
  trans≥ (keep n≥m) (keep m≥k) = keep (trans≥ n≥m m≥k)

  wk≥ : ∀ {n} → suc n ≥ n
  wk≥ = drop≥ refl≥
 
  _≱_ : Nat → Nat → Set
  n ≱ m = ¬ (n ≥ m)
   
  n≱sn : ∀ {n} → n ≱ suc n
  n≱sn (keep n≥sn) = n≥sn ↯ n≱sn
   
  _≥?_ : ∀ n m  → Dec (n ≥ m)
  zero  ≥? zero  = yes done
  zero  ≥? suc m = no (λ ())
  suc n ≥? zero  = yes done
  suc n ≥? suc m with n ≥? m
  ...            | yes n≥m = yes (keep n≥m)
  ...            | no n≱m  = no (n≱m ∘ pred≥)
   
   
  -- _>_
   
  _>_ : Nat → Nat → Set
  n > m = n ≥ suc m
   
  trans> : ∀ {n m k} → n > m → m > k
                     → n > k
  trans> n>m m>k = trans≥ n>m (drop≥ m>k)
   
  >→≥ : ∀ {n m} → n > m
                 → n ≥ m
  >→≥ (keep n≥m) = trans≥ wk≥ n≥m
   
  >→≢ : ∀ {n m} → n > m
                 → n ≢ m
  >→≢ n>m refl = n≱sn n>m
   
  _>?_ : ∀ n m  → Dec (n > m)
  n >? m = n ≥? suc m
   
   
  -- _<_
   
  _<_ : Nat → Nat → Set
  n < m = m > n
   
  ≱→< : ∀ {n m} → n ≱ m
                 → n < m
  ≱→< {n}     {zero}  n≱z   = done ↯ n≱z
  ≱→< {zero}  {suc m} z≱sm  = keep done
  ≱→< {suc n} {suc m} sn≱sm = keep (≱→< (sn≱sm ∘ keep))
   
   
  -- _≤_
   
  _≤_ : Nat → Nat → Set
  n ≤ m = m ≥ n
   
  ≱→≤ : ∀ {n m} → n ≱ m
                 → n ≤ m
  ≱→≤ = >→≥ ∘ ≱→<


--------------------------------------------------------------------------------
--
-- Numeric expressions


module NumericExpressions where
  open import Prelude
    hiding (_∋_ ; _⊇_)
  open Naturals


  -- Numeric variables
   
  NVar : Set
  NVar = Nat

  𝑎 : NVar
  𝑎 = 0

  𝑏 : NVar
  𝑏 = 1

  𝑐 : NVar
  𝑐 = 2

  𝑑 : NVar
  𝑑 = 3

  𝑒 : NVar
  𝑒 = 4

   
  -- Numeric contexts, freshness, and greatness
   
  mutual
    data NCtx : Set
      where
        ∅ : NCtx
   
        _,_ : ∀ ξ x → {{f : fresh x ξ}}
                    → NCtx
   
    fresh : NVar → NCtx → Set
    fresh x ∅       = ⊤
    fresh x (ξ , y) = x ≢ y × fresh x ξ
   
  great : NVar → NCtx → Set
  great x ∅       = ⊤
  great x (ξ , y) = x > y × great x ξ
   
  transgreat : ∀ {ξ x y} → x > y → {{g : great y ξ}}
                         → great x ξ
  transgreat {∅}     x>y {{tt}}      = tt
  transgreat {ξ , z} x>y {{y>z , g}} = trans> x>y y>z , transgreat x>y {{g}}
   
  gengreat : (ξ : NCtx) → Σ NVar (λ y → great y ξ)
  gengreat ∅       = zero , tt
  gengreat (ξ , x) with gengreat ξ
  ...              | y  , g with y >? x
  ...                       | yes y>x = y , (y>x , g)
  ...                       | no y≯x  = suc x , (refl≥ , transgreat (≱→< y≯x) {{g}})
   
  great→fresh : ∀ {x ξ} → {{g : great x ξ}}
                         → fresh x ξ
  great→fresh {x} {∅}     {{tt}}      = tt
  great→fresh {x} {ξ , y} {{x>y , g}} = >→≢ x>y , great→fresh {{g}}
   
  genfresh : (ξ : NCtx) → Σ NVar (λ y → fresh y ξ)
  genfresh ξ with gengreat ξ
  ...        | y , g = y , great→fresh {{g}}
   
   
  -- _∋_
   
  infix 4 _∋_
  data _∋_ : NCtx → NVar → Set
    where
      instance
        zero : ∀ {ξ x} → {{f : fresh x ξ}}
                       → ξ , x ∋ x
   
        suc : ∀ {ξ x y} → {{f : fresh y ξ}} → ξ ∋ x
                        → ξ , y ∋ x
   
  _∌_ : NCtx → NVar → Set
  ξ ∌ x = ¬ (ξ ∋ x)
   
  fresh→∌ : ∀ {x ξ} → {{f : fresh x ξ}}
                     → ξ ∌ x
  fresh→∌ {x} {{x≢x , f}} zero    = refl ↯ x≢x
  fresh→∌ {x} {{x≢y , f}} (suc i) = i ↯ fresh→∌ {{f}}
   
  uniq∋ : ∀ {ξ x} → (i₁ i₂ : ξ ∋ x)
                  → i₁ ≡ i₂
  uniq∋ zero     zero     = refl
  uniq∋ zero     (suc i₂) = i₂ ↯ fresh→∌
  uniq∋ (suc i₁) zero     = i₁ ↯ fresh→∌
  uniq∋ (suc i₁) (suc i₂) = suc & uniq∋ i₁ i₂
   
   
  -- _⊇_
   
  infix 4 _⊇_
  data _⊇_ : NCtx → NCtx → Set
    where
      done : ∀ {ξ} → ξ ⊇ ∅
   
      step : ∀ {ξ ξ′ x} → {{f : fresh x ξ}} → ξ′ ⊇ ξ → ξ′ ∋ x
                        → ξ′ ⊇ ξ , x
   
  ren∋ : ∀ {ξ ξ′ x} → ξ′ ⊇ ξ → ξ ∋ x
                    → ξ′ ∋ x
  ren∋ done       ()
  ren∋ (step η j) zero    = j
  ren∋ (step η j) (suc i) = ren∋ η i
   
  ext⊇ : ∀ {ξ ξ′} → (∀ {x} → ξ ∋ x → ξ′ ∋ x)
                  → ξ′ ⊇ ξ
  ext⊇ {∅}     f = done
  ext⊇ {ξ , x} f = step (ext⊇ (f ∘ suc)) (f zero)
   
  refl⊇ : ∀ {ξ} → ξ ⊇ ξ
  refl⊇ = ext⊇ id
   
  trans⊇ : ∀ {ξ ξ′ ξ″} → ξ″ ⊇ ξ′ → ξ′ ⊇ ξ
                       → ξ″ ⊇ ξ
  trans⊇ η₁ η₂ = ext⊇ (ren∋ η₁ ∘ ren∋ η₂)
   
  drop⊇ : ∀ {x ξ ζ} → ξ ⊇ ζ → {{f : fresh x ξ}}
                    → ξ , x ⊇ ζ
  drop⊇ η = trans⊇ (ext⊇ suc) η
   
  keep⊇ : ∀ {x ξ ζ} → ξ ⊇ ζ → {{f₁ : fresh x ξ}} {{f₂ : fresh x ζ}}
                    → ξ , x ⊇ ζ , x
  keep⊇ η = step (drop⊇ η) zero

  wk⊇ : ∀ {x ξ} → {{f : fresh x ξ}}
                → ξ , x ⊇ ξ
  wk⊇ = drop⊇ refl⊇
   
  uniq⊇ : ∀ {ξ ξ′} → (η₁ η₂ : ξ′ ⊇ ξ)
                   → η₁ ≡ η₂
  uniq⊇ done         done         = refl
  uniq⊇ (step η₁ i₁) (step η₂ i₂) = step & uniq⊇ η₁ η₂ ⊗ uniq∋ i₁ i₂
   
   
  -- Numeric expressions
   
  data NExp : NCtx → Set
    where
      nlit : ∀ {ξ} → Nat
                   → NExp ξ
   
      nvar : ∀ {ξ} → (x : NVar) {{i : ξ ∋ x}}
                   → NExp ξ
   
      nsuc : ∀ {ξ} → NExp ξ
                   → NExp ξ
   
      _+_ : ∀ {ξ} → NExp ξ → NExp ξ
                  → NExp ξ
   
      _*_ : ∀ {ξ} → NExp ξ → NExp ξ
                  → NExp ξ
   
   
  -- Numeric substitutions
   
  data NSub : NCtx → NCtx → Set
    where
      ∅ : ∀ {ξ} → NSub ξ ∅
   
      _,_/_ : ∀ {ξ ζ} → NSub ξ ζ → NExp ξ → (x : NVar) {{f : fresh x ζ}}
                      → NSub ξ (ζ , x)
   
  ⊇→NSub : ∀ {ξ ξ′} → ξ′ ⊇ ξ
                      → NSub ξ′ ξ
  ⊇→NSub done               = ∅
  ⊇→NSub (step {x = x} η i) = ⊇→NSub η , nvar x {{i}} / x
   
  sub∋ : ∀ {ζ ξ x} → NSub ξ ζ → ζ ∋ x
                    → NExp ξ
  sub∋ {∅}     ∅            ()
  sub∋ {ζ , x} (σ , M / .x) zero    = M
  sub∋ {ζ , x} (σ , N / y)  (suc i) = sub∋ σ i
   
  subNE : ∀ {ξ ζ} → NSub ξ ζ → NExp ζ
                  → NExp ξ
  subNE σ (nlit n)       = nlit n
  subNE σ (nvar x {{i}}) = sub∋ σ i
  subNE σ (nsuc M)       = nsuc (subNE σ M)
  subNE σ (M + N)        = subNE σ M + subNE σ N
  subNE σ (M * N)        = subNE σ M * subNE σ N
   
  renNE : ∀ {ξ ξ′} → ξ′ ⊇ ξ → NExp ξ
                   → NExp ξ′
  renNE η M = subNE (⊇→NSub η) M
   
  renNS : ∀ {ζ ξ ξ′} → ξ′ ⊇ ξ → NSub ξ ζ
                     → NSub ξ′ ζ
  renNS {∅}     η ∅           = ∅
  renNS {ζ , x} η (σ , M / y) = renNS η σ , renNE η M / y
   
  dropNS : ∀ {x ξ ζ} → NSub ξ ζ → {{f : fresh x ξ}}
                     → NSub (ξ , x) ζ
  dropNS σ = renNS wk⊇ σ
   
  forkNS : ∀ {x y ξ ζ} → NSub ξ ζ → {{f₁ : fresh x ξ}} {{f₂ : fresh y ζ}}
                       → NSub (ξ , x) (ζ , y)
  forkNS {x} {y} σ = dropNS σ , nvar x / y
   
  keepNS : ∀ {x ξ ζ} → NSub ξ ζ → {{f₁ : fresh x ξ}} {{f₂ : fresh x ζ}}
                     → NSub (ξ , x) (ζ , x)
  keepNS σ = forkNS σ
   
  reflNS : ∀ {ξ} → NSub ξ ξ
  reflNS {∅}     = ∅
  reflNS {ξ , x} = keepNS reflNS
   
  transNS : ∀ {ξ ζ θ} → NSub ξ ζ → NSub ζ θ
                      → NSub ξ θ
  transNS σ₁ ∅            = ∅
  transNS σ₁ (σ₂ , N / y) = transNS σ₁ σ₂ , subNE σ₁ N / y

  wkNS : ∀ {x ξ} → {{f : fresh x ξ}}
                 → NSub (ξ , x) ξ
  wkNS = dropNS reflNS


--------------------------------------------------------------------------------
--
-- Expressions


module Expressions where
  open import Prelude
  open NumericExpressions
    hiding (_∋_ ; _⊇_)
  module N = NumericExpressions


  -- Types

  infixr 13 _⊃_
  data Type : NCtx → Set
    where
      _==_ : ∀ {ξ} → NExp ξ → NExp ξ
                   → Type ξ
   
      ~_   : ∀ {ξ} → Type ξ
                   → Type ξ
   
      _∧_  : ∀ {ξ} → Type ξ → Type ξ
                   → Type ξ
   
      _⊃_  : ∀ {ξ} → Type ξ → Type ξ
                   → Type ξ
   
      ∇_∶_ : ∀ {ξ} → (x : NVar) {{f : fresh x ξ}} → Type (ξ , x)
                   → Type ξ
   
  _∨_ : ∀ {ξ} → Type ξ → Type ξ → Type ξ
  A ∨ B = ~ A ⊃ B
   
  ∃_∶_ : ∀ {ξ} → (x : NVar) {{f : fresh x ξ}} → Type (ξ , x)
               → Type ξ
  ∃ x ∶ A = ~ (∇ x ∶ ~ A)
   
  _⫗_ : ∀ {ξ} → Type ξ → Type ξ → Type ξ
  A ⫗ B = (A ⊃ B) ∧ (B ⊃ A)
   
  nsubT : ∀ {ξ ζ} → NSub ξ ζ → Type ζ
                  → Type ξ
  nsubT {ξ} σ (M == N)  = subNE σ M == subNE σ N
  nsubT {ξ} σ (~ A)     = ~ (nsubT σ A)
  nsubT {ξ} σ (A ∧ B)   = nsubT σ A ∧ nsubT σ B
  nsubT {ξ} σ (A ⊃ B)   = nsubT σ A ⊃ nsubT σ B
  nsubT {ξ} σ (∇ x ∶ A) with genfresh ξ
  ...                   | y , f = ∇ y ∶ nsubT (forkNS σ {{f}}) A
   
  nrenT : ∀ {ξ ξ′} → ξ′ N.⊇ ξ → Type ξ
                   → Type ξ′
  nrenT η A = nsubT (⊇→NSub η) A
   
   
  -- Contexts
   
  Ctx : NCtx → Set
  Ctx ξ = List (Type ξ)

  nrenC : ∀ {ξ ξ′} → ξ′ N.⊇ ξ → Ctx ξ
                   → Ctx ξ′
  nrenC η Γ = map (nrenT η) Γ


  -- Expressions

  data Exp : ∀ ξ → Ctx ξ → Type ξ → Set
    where
      var : ∀ {ξ A Γ} → Γ ∋ A
                      → Exp ξ Γ A
   
      lam : ∀ {ξ A B Γ} → Exp ξ (Γ , A) B
                        → Exp ξ Γ (A ⊃ B)
   
      app : ∀ {ξ A B Γ} → Exp ξ Γ (A ⊃ B) → Exp ξ Γ A
                        → Exp ξ Γ B
   
      pair : ∀ {ξ A B Γ} → Exp ξ Γ A → Exp ξ Γ B
                         → Exp ξ Γ (A ∧ B)
   
      fst : ∀ {ξ A B Γ} → Exp ξ Γ (A ∧ B)
                        → Exp ξ Γ A
   
      snd : ∀ {ξ A B Γ} → Exp ξ Γ (A ∧ B)
                        → Exp ξ Γ B
   
      dni : ∀ {ξ A Γ} → Exp ξ Γ A
                      → Exp ξ Γ (~ ~ A)
   
      dne : ∀ {ξ A Γ} → Exp ξ Γ (~ ~ A)
                      → Exp ξ Γ A
   
      contra : ∀ {ξ A B Γ} → Exp ξ Γ (A ⊃ B)
                           → Exp ξ Γ (~ B ⊃ ~ A)
   
      spec[_≔_] : ∀ x {ξ Γ} → {{f : fresh x ξ}} {A : Type (ξ , x)}
                            → (M : NExp ξ) → Exp ξ Γ (∇ x ∶ A)
                            → Exp ξ Γ (nsubT (reflNS , M / x) A)

      gen[_] : ∀ x {ξ A Γ} → {{f : fresh x ξ}}
                           → Exp ξ Γ A
                           → Exp (ξ , x) (nrenC N.wk⊇ Γ) (nrenT N.wk⊇ A)
   
      sym : ∀ {ξ M N Γ} → Exp ξ Γ (M == N)
                        → Exp ξ Γ (N == M)
   
      trans : ∀ {ξ M N O Γ} → Exp ξ Γ (M == N) → Exp ξ Γ (N == O)
                            → Exp ξ Γ (M == O)
   
      nsuci : ∀ {ξ M N Γ} → Exp ξ Γ (M == N)
                          → Exp ξ Γ (nsuc M == nsuc N)
   
      nsuce : ∀ {ξ M N Γ} → Exp ξ Γ (nsuc M == nsuc N)
                          → Exp ξ Γ (M == N)
   
      induct[_] : ∀ x {ξ Γ} → {{f : fresh x ξ}} {A : Type (ξ , x)}
                            → Exp ξ Γ (nsubT (reflNS , nlit 0 / x) A)
                            → Exp ξ Γ (∇ x ∶ (A ⊃ nsubT (wkNS , nsuc (nvar x) / x) A))
                            → Exp ξ Γ (∇ x ∶ A)
      
      ax1 : ∀ {Γ} → Exp ∅ Γ (∇ 𝑎 ∶ ~ (nsuc (nvar 𝑎) == nlit 0))
   
      ax2 : ∀ {Γ} → Exp ∅ Γ (∇ 𝑎 ∶ ((nvar 𝑎 + nlit 0) == nvar 𝑎))
   
      -- ax3 : ∀ {Γ} → Exp ∅ Γ (∇ 𝑎 ∶ ∇ 𝑏 ∶ ((nvar 𝑎 + nvar 𝑏) == nsuc (nvar 𝑎 + nvar 𝑏)))
   
      ax4 : ∀ {Γ} → Exp ∅ Γ (∇ 𝑎 ∶ ((nvar 𝑎 * nlit 0) == nlit 0))
   
      -- ax5 : ∀ {Γ} → Exp ∅ Γ (∇ 𝑎 ∶ ∇ 𝑏 ∶ ((nvar 𝑎 * nsuc (nvar 𝑏)) == ((nvar 𝑎 * nvar 𝑏) + nvar 𝑎)))
