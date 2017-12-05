{-# OPTIONS --rewriting #-}

module TNT6 where


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

  ≥+≢→> : ∀ {n m} → n ≥ m → n ≢ m
                   → n > m
  ≥+≢→> {zero}  {zero}  done       z≢z   = refl ↯ z≢z
  ≥+≢→> {zero}  {suc m} ()         z≢sm
  ≥+≢→> {suc n} {zero}  done       sn≢z  = keep done
  ≥+≢→> {suc n} {suc m} (keep n≥m) sn≢sm = keep (≥+≢→> n≥m (sn≢sm ∘ (suc &_)))

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


  -- ⌈__̂⌉

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
-- Lists


module Lists where
  open import Prelude
    renaming (renᵢ to ren∋ ; idᵣ to refl⊇)
  open Naturals


  pred∋ : ∀ {ℓ} → {X : Set ℓ} {Γ : List X} {A B : X}
                → A ≢ B → Γ , B ∋ A
                → Γ ∋ A
  pred∋ A≢A zero    = refl ↯ A≢A
  pred∋ A≢B (suc i) = i

  _∋?_ : ∀ ξ x → Dec (ξ ∋ x)
  ∅       ∋? x = no (λ ())
  (ξ , y) ∋? x with x ≡? y
  ...          | yes refl = yes zero
  ...          | no x≢y   = mapDec suc (pred∋ x≢y) (ξ ∋? x)


  wk⊇ : ∀ {ℓ} → {X : Set ℓ} {Γ : List X} {A : X}
              → Γ , A ⊇ Γ
  wk⊇ = drop refl⊇


--------------------------------------------------------------------------------
--
-- Numeric expressions


module NumericExpressions where
  open import Prelude
    renaming (renᵢ to ren∋ ; idᵣ to refl⊇)
  open Booleans
  open Lists
  open Naturals


  -- Numeric variables

  NVar : Set
  NVar = Nat

  -- TODO: Improve this
  String→NVar : String → NVar
  String→NVar "a" = 0
  String→NVar "b" = 1
  String→NVar "c" = 2
  String→NVar "d" = 3
  String→NVar "e" = 4
  String→NVar _   = 5

  NVar→String : NVar → String
  NVar→String 0 = "a"
  NVar→String 1 = "b"
  NVar→String 2 = "c"
  NVar→String 3 = "d"
  NVar→String 4 = "e"
  NVar→String _ = "f"

  instance
    nvarIsString : IsString NVar
    nvarIsString =
      record
        { Constraint = λ s → ⊤
        ; fromString = λ s → String→NVar s
        }


  -- Numeric contexts

  NCtx : Set
  NCtx = List NVar


  -- Freshness and greatness

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

  mkGreat : (ξ : NCtx) → NVar
  mkGreat ∅       = zero
  mkGreat (ξ , x) with mkGreat ξ
  ...             | y with y ⌊>?⌋ x
  ...                 | true  = y
  ...                 | false = suc x

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

  genGreatFresh : (ξ : NCtx) → Σ NVar (λ y →
                                  Σ (Great y ξ) (λ g →
                                    Σ (Fresh y ξ) (λ f →
                                      genGreat ξ ≡ (y , g) × Great→Fresh {ξ} {{g}} ≡ f)))
  genGreatFresh ξ with genGreat ξ
  ...                  | y , g = y , (g , (Great→Fresh {ξ} {{g}} , (refl , refl)))


  -- Numeric expressions

  infixl 50 _+_
  infixl 55 _*_
  data NExp : NCtx → Set
    where
      nlit : ∀ {ξ} → Nat
                   → NExp ξ

      nvar : ∀ x {ξ} → {{i : ξ ∋ x}}
                     → NExp ξ

      nsuc : ∀ {ξ} → NExp ξ
                   → NExp ξ

      _+_ : ∀ {ξ} → NExp ξ → NExp ξ
                  → NExp ξ

      _*_ : ∀ {ξ} → NExp ξ → NExp ξ
                  → NExp ξ

  {-# DISPLAY nlit n = n #-}
  {-# DISPLAY nvar x = NVar→String x #-}

  instance
    nexpIsNumber : ∀ {ξ} → Number (NExp ξ)
    nexpIsNumber =
      record
        { Constraint = λ n → ⊤
        ; fromNat    = λ n → nlit n
        }

  instance
    nexpIsString : ∀ {ξ} → IsString (NExp ξ)
    nexpIsString {ξ} =
      record
        { Constraint = λ s → Σ ⌈ ⌊ ξ ∋? String→NVar s ⌋ ⌉
                                (λ e → ξ ∋ String→NVar s)
        ; fromString = λ { s {{e , i}} → nvar (String→NVar s) {{i}} }
        }


  -- Numeric substitutions

  record NExp/NVar (ξ : NCtx) : Set
    where
      constructor _/_
      field
        M : NExp ξ
        x : NVar

  NSub : NCtx → List NVar → Set
  NSub ξ ζ = All (λ x → NExp/NVar ξ) ζ

  sub∋ : ∀ {ζ ξ x} → NSub ξ ζ → ζ ∋ x
                   → NExp ξ
  sub∋ {∅}     ∅           ()
  sub∋ {ζ , x} (σ , M / y) zero    = M
  sub∋ {ζ , x} (σ , M / y) (suc i) = sub∋ σ i

  subNE : ∀ {ξ ζ} → NSub ξ ζ → NExp ζ
                  → NExp ξ
  subNE σ (nlit n)       = nlit n
  subNE σ (nvar x {{i}}) = sub∋ σ i
  subNE σ (nsuc M)       = nsuc (subNE σ M)
  subNE σ (M + N)        = subNE σ M + subNE σ N
  subNE σ (M * N)        = subNE σ M * subNE σ N

  renNE : ∀ {ξ ξ′} → ξ′ ⊇ ξ → NExp ξ
                   → NExp ξ′
  renNE η (nlit n)       = nlit n
  renNE η (nvar x {{i}}) = nvar x {{ren∋ η i}}
  renNE η (nsuc M)       = nsuc (renNE η M)
  renNE η (M + N)        = renNE η M + renNE η N
  renNE η (M * N)        = renNE η M * renNE η N

  renNS : ∀ {ζ ξ ξ′} → ξ′ ⊇ ξ → NSub ξ ζ
                     → NSub ξ′ ζ
  renNS η σ = mapAll (λ { (M / x) → renNE η M / x }) σ

  dropNS : ∀ {x ξ ζ} → NSub ξ ζ
                     → NSub (ξ , x) ζ
  dropNS σ = renNS wk⊇ σ

  forkNS : ∀ {x y ξ ζ} → NSub ξ ζ
                       → NSub (ξ , x) (ζ , y)
  forkNS {x} {y} σ = dropNS σ , nvar x / y

  keepNS : ∀ {x ξ ζ} → NSub ξ ζ
                     → NSub (ξ , x) (ζ , x)
  keepNS σ = forkNS σ

  reflNS : ∀ {ξ} → NSub ξ ξ
  reflNS {∅}     = ∅
  reflNS {ξ , x} = keepNS reflNS

  transNS : ∀ {ξ ζ θ} → NSub ξ ζ → NSub ζ θ
                      → NSub ξ θ
  transNS σ₁ ∅            = ∅
  transNS σ₁ (σ₂ , M / x) = transNS σ₁ σ₂ , subNE σ₁ M / x

  wkNS : ∀ {x ξ} → NSub (ξ , x) ξ
  wkNS = dropNS reflNS

  ⊇→NSub : ∀ {ξ ξ′} → ξ′ ⊇ ξ
                     → NSub ξ′ ξ
  ⊇→NSub done     = ∅
  ⊇→NSub (drop η) = dropNS (⊇→NSub η)
  ⊇→NSub (keep η) = keepNS (⊇→NSub η)


--------------------------------------------------------------------------------
--
-- Expressions


module Expressions where
  open import Prelude
    hiding (tt)
    renaming (renᵢ to ren∋ ; idᵣ to refl⊇)
  open Booleans
  open Lists
  open NumericExpressions


  -- Types

  infix  45 ~_
  infixl 40 _∧_ _∨_
  infixr 35 _⊃_
  infix  30 _⫗_
  infix  25 _==_
  infixr 20 ∇_∶_ ∃_∶_
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

      ∇_∶_ : ∀ x {ξ} → Type (ξ , x)
                     → Type ξ

  _∨_ : ∀ {ξ} → Type ξ → Type ξ → Type ξ
  A ∨ B = ~ A ⊃ B

  ∃_∶_ : ∀ x {ξ} → Type (ξ , x)
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
  nsubT {ξ} σ (∇ x ∶ A) with mkGreat ξ
  ...                   | y = ∇ y ∶ nsubT (forkNS σ) A

  nrenT : ∀ {ξ ξ′} → ξ′ ⊇ ξ → Type ξ
                   → Type ξ′
  nrenT η A = nsubT (⊇→NSub η) A


  -- Contexts

  Ctx : NCtx → Set
  Ctx ξ = List (Type ξ)

  nsubC : ∀ {ξ ζ} → NSub ξ ζ → Ctx ζ
                  → Ctx ξ
  nsubC σ Γ = map (nsubT σ) Γ

  nrenC : ∀ {ξ ξ′} → ξ′ ⊇ ξ → Ctx ξ
                   → Ctx ξ′
  nrenC `η Γ = nsubC (⊇→NSub `η) Γ

  nsub∋ : ∀ {ξ ζ Γ A} → (`σ : NSub ξ ζ) → Γ ∋ A
                      → nsubC `σ Γ ∋ nsubT `σ A
  nsub∋ `σ zero    = zero
  nsub∋ `σ (suc i) = suc (nsub∋ `σ i)

  nren∋ : ∀ {ξ ξ′ Γ A} → (`η : ξ′ ⊇ ξ) → Γ ∋ A
                       → nrenC `η Γ ∋ nrenT `η A
  nren∋ `η i = nsub∋ (⊇→NSub `η) i

  nsub⊇ : ∀ {ξ ζ Γ Γ′} → (σ : NSub ξ ζ) → Γ′ ⊇ Γ
                       → nsubC σ Γ′ ⊇ nsubC σ Γ
  nsub⊇ σ done     = done
  nsub⊇ σ (drop η) = drop (nsub⊇ σ η)
  nsub⊇ σ (keep η) = keep (nsub⊇ σ η)

  nren⊇ : ∀ {ξ ξ′ Γ Γ′} → (`η : ξ′ ⊇ ξ) → Γ′ ⊇ Γ
                        → nrenC `η Γ′ ⊇ nrenC `η Γ
  nren⊇ `η η = nsub⊇ (⊇→NSub `η) η


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

      spec[_/_] : ∀ {ξ Γ} → (S : NExp ξ) (x : NVar) {A : Type (ξ , x)}
                          → Exp ξ Γ (∇ x ∶ A)
                          → Exp ξ Γ (nsubT (reflNS , S / x) A)

      gen[_] : ∀ x {ξ A Γ} → Exp (ξ , x) (nrenC wk⊇ Γ) A
                           → Exp ξ Γ (∇ x ∶ A)

      sym : ∀ {ξ M N Γ} → Exp ξ Γ (M == N)
                        → Exp ξ Γ (N == M)

      trans : ∀ {ξ M N O Γ} → Exp ξ Γ (M == N) → Exp ξ Γ (N == O)
                            → Exp ξ Γ (M == O)

      nsuci : ∀ {ξ M N Γ} → Exp ξ Γ (M == N)
                          → Exp ξ Γ (nsuc M == nsuc N)

      nsuce : ∀ {ξ M N Γ} → Exp ξ Γ (nsuc M == nsuc N)
                          → Exp ξ Γ (M == N)

      induct[_] : ∀ x {ξ A Γ} → Exp ξ Γ (nsubT (reflNS , 0 / x) A)
                              → Exp ξ Γ (∇ x ∶ (A ⊃ nsubT (wkNS , nsuc (nvar x) / x) A))
                              → Exp ξ Γ (∇ x ∶ A)

      ax1 : ∀ {ξ Γ} → Exp ξ Γ (∇ "a" ∶ ~ (nsuc "a" == 0))

      ax2 : ∀ {ξ Γ} → Exp ξ Γ (∇ "a" ∶ "a" + 0 == "a")

      ax3 : ∀ {ξ Γ} → Exp ξ Γ (∇ "a" ∶ ∇ "b" ∶ "a" + "b" == nsuc ("a" + "b"))

      ax4 : ∀ {ξ Γ} → Exp ξ Γ (∇ "a" ∶ "a" * 0 == 0)

      ax5 : ∀ {ξ Γ} → Exp ξ Γ (∇ "a" ∶ ∇ "b" ∶ "a" * nsuc "b" == "a" * "b" + "a")


  -- TODO: Names in Exp too!

  v0 : ∀ {ξ A Γ} → Exp ξ (Γ , A) A
  v0 = var 0

  v1 : ∀ {ξ A B Γ} → Exp ξ (Γ , A , B) A
  v1 = var 1

  v2 : ∀ {ξ A B C Γ} → Exp ξ (Γ , A , B , C) A
  v2 = var 2

  v3 : ∀ {ξ A B C D Γ} → Exp ξ (Γ , A , B , C , D) A
  v3 = var 3

  v4 : ∀ {ξ A B C D E Γ} → Exp ξ (Γ , A , B , C , D , E) A
  v4 = var 4

  v5 : ∀ {ξ A B C D E F Γ} → Exp ξ (Γ , A , B , C , D , E , F) A
  v5 = var 5


--  nsub : ∀ {ξ ζ Γ A} → (`σ : NSub ξ ζ) → Exp ζ Γ A
--                     → Exp ξ (nsubC `σ Γ) (nsubT `σ A)
--  nsub `σ (var i)           = var (nsub∋ `σ i)
--  nsub `σ (lam M)           = lam (nsub `σ M)
--  nsub `σ (app M N)         = app (nsub `σ M) (nsub `σ N)
--  nsub `σ (pair M N)        = pair (nsub `σ M) (nsub `σ N)
--  nsub `σ (fst M)           = fst (nsub `σ M)
--  nsub `σ (snd M)           = snd (nsub `σ M)
--  nsub `σ (dni M)           = dni (nsub `σ M)
--  nsub `σ (dne M)           = dne (nsub `σ M)
--  nsub `σ (contra M)        = contra (nsub `σ M)
--  nsub `σ (spec[ S / x ] M) = {!!}
--  nsub `σ (gen[ x ] M)      = {!!}
--  nsub `σ (sym M)           = sym (nsub `σ M)
--  nsub `σ (trans M N)       = trans (nsub `σ M) (nsub `σ N)
--  nsub `σ (nsuci M)         = nsuci (nsub `σ M)
--  nsub `σ (nsuce M)         = nsuce (nsub `σ M)
--  nsub `σ (induct[ x ] M N) = {!!}
--  nsub `σ ax1               = {!ax1!}
--  nsub `σ ax2               = {!ax2!}
--  nsub `σ ax3               = {!ax3!}
--  nsub `σ ax4               = {!ax4!}
--  nsub `σ ax5               = {!ax5!}

--   nren : ∀ {ξ′ ξ A Γ} → (`η : ξ′ N.⊇ ξ) → Exp ξ Γ A
--                       → Exp ξ′ (nrenC `η Γ) (nrenT `η A)
--   nren `η M = nsub (⊇→NSub `η) M


  ren : ∀ {ξ A Γ Γ′} → Γ′ ⊇ Γ → Exp ξ Γ A
                     → Exp ξ Γ′ A
  ren η (var i)           = var (ren∋ η i)
  ren η (lam M)           = lam (ren (keep η) M)
  ren η (app M N)         = app (ren η M) (ren η N)
  ren η (pair M N)        = pair (ren η M) (ren η N)
  ren η (fst M)           = fst (ren η M)
  ren η (snd M)           = snd (ren η M)
  ren η (dni M)           = dni (ren η M)
  ren η (dne M)           = dne (ren η M)
  ren η (contra M)        = contra (ren η M)
  ren η (spec[ S / x ] M) = spec[ S / x ] (ren η M)
  ren η (gen[ x ] M)      = gen[ x ] (ren (nren⊇ wk⊇ η) M)
  ren η (sym M)           = sym (ren η M)
  ren η (trans M N)       = trans (ren η M) (ren η N)
  ren η (nsuci M)         = nsuci (ren η M)
  ren η (nsuce M)         = nsuce (ren η M)
  ren η (induct[ x ] M N) = induct[ x ] (ren η M) (ren η N)
  ren η ax1               = ax1
  ren η ax2               = ax2
  ren η ax3               = ax3
  ren η ax4               = ax4
  ren η ax5               = ax5

  wk : ∀ {ξ A B Γ} → Exp ξ Γ A
                   → Exp ξ (Γ , B) A
  wk M = ren (drop refl⊇) M


  -- Substitutions

  Sub : ∀ ξ → Ctx ξ → Ctx ξ → Set
  Sub ξ Γ Ξ = All (Exp ξ Γ) Ξ

  ⊇→Sub : ∀ {ξ Γ Γ′} → Γ′ ⊇ Γ
                      → Sub ξ Γ′ Γ
  ⊇→Sub done     = ∅
  ⊇→Sub (drop η) = mapAll wk (⊇→Sub η)
  ⊇→Sub (keep η) = mapAll wk (⊇→Sub η) , var zero


  lem : ∀ {ξ A Γ} → Exp ξ Γ (A ∨ ~ A)
  lem = lam v0

  define : ∀ {ξ A C Γ} → Exp ξ Γ A → Exp ξ (Γ , A) C
                       → Exp ξ Γ C
  define M N = app (lam N) M

  ntra : ∀ {ξ A B Γ} → Exp ξ Γ (~ B ⊃ ~ A)
                     → Exp ξ Γ (A ⊃ B)
  ntra M = lam (dne (app (wk (contra M)) (dni v0)))

  deny : ∀ {ξ A C Γ} → Exp ξ Γ A → Exp ξ Γ (~ A)
                     → Exp ξ Γ C
  deny M N = app (ntra (lam (wk N))) M


  TT : ∀ {ξ} → Type ξ
  TT = 0 == 0

  refl== : ∀ {ξ Γ} → Exp ξ Γ (∇ "a" ∶ "a" == "a")
  refl== = gen[ "a" ] (trans
             (sym (spec[ "a" / "a" ] ax2))
             (spec[ "a" / "a" ] ax2))

  tt : ∀ {ξ Γ} → Exp ξ Γ TT
  tt = spec[ 0 / "a" ] refl==


  FF : ∀ {ξ} → Type ξ
  FF = ~ TT

  fen : ∀ {ξ A Γ} → Exp ξ (Γ , A) FF
                  → Exp ξ Γ (~ A)
  fen M = app (contra (lam M)) (dni tt)

  fe : ∀ {ξ A Γ} → Exp ξ (Γ , ~ A) FF
                 → Exp ξ Γ A
  fe M = dne (fen M)

  efq : ∀ {ξ C Γ} → Exp ξ Γ FF
                  → Exp ξ Γ C
  efq M = fe (wk M)


  dni⊃₁ : ∀ {ξ A B Γ} → Exp ξ Γ (A ⊃ B)
                      → Exp ξ Γ (~ ~ A ⊃ B)
  dni⊃₁ M = lam (app (wk M) (dne v0))

  dne⊃₂ : ∀ {ξ A B Γ} → Exp ξ Γ (A ⊃ ~ ~ B)
                      → Exp ξ Γ (A ⊃ B)
  dne⊃₂ M = lam (dne (app (wk M) v0))

  swap∨ : ∀ {ξ A B Γ} → Exp ξ Γ (A ∨ B)
                      → Exp ξ Γ (B ∨ A)
  swap∨ M = dne⊃₂ (contra M)

  right : ∀ {ξ A B Γ} → Exp ξ Γ B
                      → Exp ξ Γ (A ∨ B)
  right M = lam (wk M)

  left : ∀ {ξ A B Γ} → Exp ξ Γ A
                     → Exp ξ Γ (A ∨ B)
  left M = swap∨ (right M)

  sndK*36 : ∀ {ξ A B C Γ} → Exp ξ Γ ((A ∨ B) ∧ (A ∨ C))
                          → Exp ξ Γ (A ∨ (B ∧ C))
  sndK*36 M = lam (pair
                (app (fst (wk M)) v0)
                (app (snd (wk M)) v0))

  ∨→~∧ : ∀ {ξ A B Γ} → Exp ξ Γ (~ A ∨ ~ B)
                      → Exp ξ Γ (~ (A ∧ B))
  ∨→~∧ M = fen (deny
              (snd v0)
              (app
                (wk M)
                (dni (fst v0))))

  woop : ∀ {ξ A C Γ} → Exp ξ (Γ , A) C → Exp ξ (Γ , ~ A) C
                     → Exp ξ Γ C
  woop M N = app
               (swap∨ (sndK*36 (pair
                 (swap∨ (dni⊃₁ (lam M)))
                 (swap∨ (dni⊃₁ (lam N))))))
               (fen (deny
                 (fst v0)
                 (snd v0)))
