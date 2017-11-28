module TNT5 where


--------------------------------------------------------------------------------
--
-- Naturals


module Naturals where
  open import Prelude


  -- _≡_

  _≡?_ : (n m : Nat) → Dec (n ≡ m)
  zero  ≡? zero  = yes refl
  zero  ≡? suc m = no (λ ())
  suc n ≡? zero  = no (λ ())
  suc n ≡? suc m with n ≡? m
  ...            | yes refl = yes refl
  ...            | no n≢m   = no (n≢m ∘ injsuc)

  _≢?_ : (n m : Nat) → Dec (n ≢ m)
  zero  ≢? zero  = no (λ z≢z → refl ↯ z≢z)
  zero  ≢? suc m = yes (λ ())
  suc n ≢? zero  = yes (λ ())
  suc n ≢? suc m with n ≢? m
  ...            | yes n≢m = yes (λ sn≡sm → injsuc sn≡sm ↯ n≢m)
  ...            | no ¬n≢m = no (λ sn≢sm → (λ n≡m → (suc & n≡m) ↯ sn≢sm) ↯ ¬n≢m)


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
-- Booleans


module Booleans where
  open import Prelude
  open Naturals

   
  _and_ : Bool → Bool → Bool
  true  and x = x
  false and x = false
   
  ⌊_⌋ : ∀ {ℓ} {X : Set ℓ} → Dec X
                          → Bool
  ⌊ yes _ ⌋ = true
  ⌊ no  _ ⌋ = false


  -- ⌈_̂⌉

  data ⌈_⌉ : Bool → Set
    where
      instance
        yes : ⌈ true ⌉

  ⌈fst⌉ : ∀ {p q} → ⌈ p and q ⌉
                  → ⌈ p ⌉
  ⌈fst⌉ {true}  {q} t = yes
  ⌈fst⌉ {false} {q} t = t
  
  ⌈snd⌉ : ∀ {p q} → ⌈ p and q ⌉
                  → ⌈ q ⌉
  ⌈snd⌉ {true}  {q}     t = t
  ⌈snd⌉ {false} {true}  t = yes
  ⌈snd⌉ {false} {false} t = t

  ⌈pair⌉ : ∀ {p q} → ⌈ p ⌉ → ⌈ q ⌉
                   → ⌈ p and q ⌉
  ⌈pair⌉ yes yes = yes


  -- _⌊≢?⌋_

  _⌊≢?⌋_ : Nat → Nat → Bool
  n ⌊≢?⌋ m = ⌊ n ≢? m ⌋

  wrap≢ : ∀ {n m} → n ≢ m
                  → ⌈ n ⌊≢?⌋ m ⌉
  wrap≢ {n} {m} n≢m with n ≢? m
  ...               | yes n≢m! = yes
  ...               | no ¬n≢m  = n≢m ↯ ¬n≢m

  unwrap≢ : ∀ {n m} → ⌈ n ⌊≢?⌋ m ⌉
                    → n ≢ m
  unwrap≢ {n} {m} t  with n ≢? m
  ...                | yes n≢m = n≢m
  unwrap≢ {n} {m} () | no ¬n≢m


  -- _⌊>?⌋_

  _⌊>?⌋_ : Nat → Nat → Bool
  n ⌊>?⌋ m = ⌊ n >? m ⌋

  wrap> : ∀ {n m} → n > m
                  → ⌈ n ⌊>?⌋ m ⌉
  wrap> {n} {m} n>m with n >? m
  ...               | yes n>m! = yes
  ...               | no n≯m   = n>m ↯ n≯m

  unwrap> : ∀ {n m} → ⌈ n ⌊>?⌋ m ⌉
                    → n > m
  unwrap> {n} {m} t  with n >? m
  ...                | yes n>m = n>m
  unwrap> {n} {m} () | no n≯m


--------------------------------------------------------------------------------
--
-- Numeric expressions


module NumericExpressions where
  open import Prelude
    hiding (_∋_ ; _⊇_)
    -- renaming (_⩼_ to _>?_)
  open Booleans
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
   
        _,_ : ∀ ξ x → {{f : ⌈ fresh x ξ ⌉}}
                    → NCtx
   
    fresh : NVar → NCtx → Bool
    fresh x ∅       = true
    fresh x (ξ , y) = (x ⌊≢?⌋ y) and fresh x ξ
  
  great : NVar → NCtx → Bool
  great x ∅       = true
  great x (ξ , y) = (x ⌊>?⌋ y) and great x ξ

  Fresh : NVar → NCtx → Set
  Fresh x ξ = ⌈ fresh x ξ ⌉

  Great : NVar → NCtx → Set
  Great x ξ = ⌈ great x ξ ⌉
   
  transGreat : ∀ {ξ x y} → x > y → {{g : Great y ξ}}
                         → Great x ξ
  transGreat {∅}     {x} {y} x>y {{yes}} = yes
  transGreat {ξ , z} {x} {y} x>y {{g}}   with y >? z
  ...                                    | yes y>z = ⌈pair⌉ (wrap> (trans> x>y y>z))
                                                            (transGreat {ξ} x>y {{g}})
  transGreat {ξ , z} {x} {y} x>y {{()}}  | no y≯z
   
  genGreat : (ξ : NCtx) → Σ NVar (λ y → Great y ξ)
  genGreat ∅       = zero , yes
  genGreat (ξ , x) with genGreat ξ
  ...              | y  , g with y >? x
  ...                       | yes y>x = y , ⌈pair⌉ (wrap> y>x) g
  ...                       | no y≯x  = suc x , ⌈pair⌉ (wrap> (refl≥ {suc x}))
                                                       (transGreat {ξ} (≱→< y≯x) {{g}})
   
  Great→Fresh : ∀ {ξ x} → {{g : Great x ξ}}
                         → Fresh x ξ
  Great→Fresh {∅}     {x} {{yes}} = yes
  Great→Fresh {ξ , y} {x} {{g}}   = ⌈pair⌉ (wrap≢ (>→≢ (unwrap> {x} (⌈fst⌉ g))))
                                            (Great→Fresh {ξ} {{⌈snd⌉ {x ⌊>?⌋ y} g}})
   
  genFresh : (ξ : NCtx) → Σ NVar (λ y → Fresh y ξ)
  genFresh ξ with genGreat ξ
  ...        | y , g = y , Great→Fresh {ξ} {{g}}
   
   
  -- _∋_
   
  infix 4 _∋_
  data _∋_ : NCtx → NVar → Set
    where
      instance
        zero : ∀ {ξ x} → {{f : Fresh x ξ}}
                       → ξ , x ∋ x
   
        suc : ∀ {ξ x y} → {{f : Fresh y ξ}} → ξ ∋ x
                        → ξ , y ∋ x
   
  _∌_ : NCtx → NVar → Set
  ξ ∌ x = ¬ (ξ ∋ x)
   
  Fresh→∌ : ∀ {x ξ} → {{f : Fresh x ξ}}
                     → ξ ∌ x
  Fresh→∌ {x} {ξ , y} {{f}} zero    = refl ↯ unwrap≢ {x} (⌈fst⌉ f)
  Fresh→∌ {x} {ξ , y} {{f}} (suc i) = i ↯ Fresh→∌ {{⌈snd⌉ {x ⌊≢?⌋ y} f}}
   
  uniq∋ : ∀ {ξ x} → (i₁ i₂ : ξ ∋ x)
                  → i₁ ≡ i₂
  uniq∋ zero     zero     = refl
  uniq∋ zero     (suc i₂) = i₂ ↯ Fresh→∌
  uniq∋ (suc i₁) zero     = i₁ ↯ Fresh→∌
  uniq∋ (suc i₁) (suc i₂) = suc & uniq∋ i₁ i₂
   
   
  -- _⊇_
   
  infix 4 _⊇_
  data _⊇_ : NCtx → NCtx → Set
    where
      done : ∀ {ξ} → ξ ⊇ ∅
   
      step : ∀ {ξ ξ′ x} → {{f : Fresh x ξ}} → ξ′ ⊇ ξ → ξ′ ∋ x
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
   
  drop⊇ : ∀ {x ξ ζ} → ξ ⊇ ζ → {{f : Fresh x ξ}}
                    → ξ , x ⊇ ζ
  drop⊇ η = trans⊇ (ext⊇ suc) η
   
  keep⊇ : ∀ {x ξ ζ} → ξ ⊇ ζ → {{f₁ : Fresh x ξ}} {{f₂ : Fresh x ζ}}
                    → ξ , x ⊇ ζ , x
  keep⊇ η = step (drop⊇ η) zero

  wk⊇ : ∀ {x ξ} → {{f : Fresh x ξ}}
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
   
      _,_/_ : ∀ {ξ ζ} → NSub ξ ζ → NExp ξ → (x : NVar) {{f : Fresh x ζ}}
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
   
  dropNS : ∀ {x ξ ζ} → NSub ξ ζ → {{f : Fresh x ξ}}
                     → NSub (ξ , x) ζ
  dropNS σ = renNS wk⊇ σ
   
  forkNS : ∀ {x y ξ ζ} → NSub ξ ζ → {{f₁ : Fresh x ξ}} {{f₂ : Fresh y ζ}}
                       → NSub (ξ , x) (ζ , y)
  forkNS {x} {y} σ = dropNS σ , nvar x / y
   
  keepNS : ∀ {x ξ ζ} → NSub ξ ζ → {{f₁ : Fresh x ξ}} {{f₂ : Fresh x ζ}}
                     → NSub (ξ , x) (ζ , x)
  keepNS σ = forkNS σ
   
  reflNS : ∀ {ξ} → NSub ξ ξ
  reflNS {∅}     = ∅
  reflNS {ξ , x} = keepNS reflNS
   
  transNS : ∀ {ξ ζ θ} → NSub ξ ζ → NSub ζ θ
                      → NSub ξ θ
  transNS σ₁ ∅            = ∅
  transNS σ₁ (σ₂ , N / y) = transNS σ₁ σ₂ , subNE σ₁ N / y

  wkNS : ∀ {x ξ} → {{f : Fresh x ξ}}
                 → NSub (ξ , x) ξ
  wkNS = dropNS reflNS


--------------------------------------------------------------------------------
--
-- Expressions


module Expressions where
  open import Prelude
  open Booleans
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
   
      ∇_∶_ : ∀ {ξ} → (x : NVar) {{f : Fresh x ξ}} → Type (ξ , x)
                   → Type ξ
   
  _∨_ : ∀ {ξ} → Type ξ → Type ξ → Type ξ
  A ∨ B = ~ A ⊃ B
   
  ∃_∶_ : ∀ {ξ} → (x : NVar) {{f : Fresh x ξ}} → Type (ξ , x)
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
  nsubT {ξ} σ (∇ x ∶ A) with genFresh ξ
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
   
      spec[_≔_] : ∀ x {ξ Γ} → {{f : Fresh x ξ}} {A : Type (ξ , x)}
                            → (M : NExp ξ) → Exp ξ Γ (∇ x ∶ A)
                            → Exp ξ Γ (nsubT (reflNS , M / x) A)

      gen[_] : ∀ x {ξ A Γ} → {{f : Fresh x ξ}}
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
   
      induct[_] : ∀ x {ξ Γ} → {{f : Fresh x ξ}} {A : Type (ξ , x)}
                            → Exp ξ Γ (nsubT (reflNS , nlit 0 / x) A)
                            → Exp ξ Γ (∇ x ∶ (A ⊃ nsubT (wkNS , nsuc (nvar x) / x) A))
                            → Exp ξ Γ (∇ x ∶ A)
      
      ax1 : ∀ {Γ} → Exp ∅ Γ (∇ 𝑎 ∶ ~ (nsuc (nvar 𝑎) == nlit 0))
   
      ax2 : ∀ {Γ} → Exp ∅ Γ (∇ 𝑎 ∶ ((nvar 𝑎 + nlit 0) == nvar 𝑎))
   
      ax3 : ∀ {Γ} → Exp ∅ Γ (∇ 𝑎 ∶ ∇ 𝑏 ∶ ((nvar 𝑎 + nvar 𝑏) == nsuc (nvar 𝑎 + nvar 𝑏)))
   
      ax4 : ∀ {Γ} → Exp ∅ Γ (∇ 𝑎 ∶ ((nvar 𝑎 * nlit 0) == nlit 0))
   
      ax5 : ∀ {Γ} → Exp ∅ Γ (∇ 𝑎 ∶ ∇ 𝑏 ∶ ((nvar 𝑎 * nsuc (nvar 𝑏)) == ((nvar 𝑎 * nvar 𝑏) + nvar 𝑎)))
