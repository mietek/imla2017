{-# OPTIONS --rewriting #-}

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

--  transFreshGreat : ∀ {ξ x y} → x ≢ y → x > y → {{f : Fresh y ξ}} {{g : Great y ξ}}
--                              → Fresh x ξ × Great x ξ
--  transFreshGreat {∅}     {x} {y} x≢y x>y {{yes}} {{yes}} = yes , yes
--  transFreshGreat {ξ , z} {x} {y} x≢y x>y {{f}}   {{g}}   with y ≢? x | y >? x
--  ...                                                     | yes y≢x | yes y>x = {!⌈pair⌉ (trans≢ wrap≢ y≢x)!}
--  ...                                                     | yes y≢x | no y≯y  = {!!}
--  ...                                                     | no ¬y≢x | yes y>y = {!!}
--  ...                                                     | no ¬y≢x | no y≯y  = {!!}
--
--
--  genFreshGreat : (ξ : NCtx) → Σ NVar (λ y → Fresh y ξ × Great y ξ)
--  genFreshGreat ∅       = zero , (yes , yes)
--  genFreshGreat (ξ , x) with genFreshGreat ξ
--  ...                   | y  , (f , g) with y ≢? x | y ≥? x
--  ...                                  | yes y≢x | yes y≥x = y , ( ⌈pair⌉ (wrap≢ y≢x) f
--                                                                 , ⌈pair⌉ (wrap> (≥+≢→> y≥x y≢x)) g
--                                                                 )
--  ...                                  | yes y≢x | no y≱x  = {!!}
--  ...                                  | no ¬y≢x | yes y≥x = {!!}
--  ...                                  | no ¬y≢x | no y≱x  = {!!}

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

--  genFresh : (ξ : NCtx) → Σ NVar (λ y → Fresh y ξ)
--  genFresh ξ with genGreat ξ
--  ...        | y , g = y , Great→Fresh {ξ} {{g}}

--  genGreatFresh : (ξ : NCtx) → Σ NVar (λ y → Σ (Great y ξ) (λ g → Fresh y ξ × genGreat ξ ≡ (y , g)))
--  genGreatFresh ξ with genGreat ξ
--  ...             | y , g = y , (g , (Great→Fresh {ξ} {{g}} , refl))

  genGreatFresh : (ξ : NCtx) → Σ NVar (λ y →
                                Σ (Great y ξ) (λ g →
                                Σ (Fresh y ξ) (λ f →
                                genGreat ξ ≡ (y , g) × Great→Fresh {ξ} {{g}} ≡ f)))
  genGreatFresh ξ with genGreat ξ
  ...                  | y , g = y , (g , (Great→Fresh {ξ} {{g}} , (refl , refl)))


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

  ∌→Fresh : ∀ {x ξ} → ξ ∌ x
                     → Fresh x ξ
  ∌→Fresh {x} {∅}     ∅∌x  = yes
  ∌→Fresh {x} {ξ , y} ξy∌x with x ≡? y
  ...                       | yes refl = zero ↯ ξy∌x
  ...                       | no x≢y   = ⌈pair⌉ (wrap≢ x≢y)
                                                (∌→Fresh (λ ξ∋x → suc ξ∋x ↯ ξy∌x))

  uniq∋ : ∀ {ξ x} → (i₁ i₂ : ξ ∋ x)
                  → i₁ ≡ i₂
  uniq∋ zero     zero     = refl
  uniq∋ zero     (suc i₂) = i₂ ↯ Fresh→∌
  uniq∋ (suc i₁) zero     = i₁ ↯ Fresh→∌
  uniq∋ (suc i₁) (suc i₂) = suc & uniq∋ i₁ i₂

  pred∋ : ∀ {ξ x y} → x ≢ y → {{f : Fresh y ξ}}
                    → ξ , y ∋ x
                    → ξ ∋ x
  pred∋ x≢x zero    = refl ↯ x≢x
  pred∋ x≢y (suc i) = i

  _∋?_ : ∀ ξ x → Dec (ξ ∋ x)
  ∅       ∋? x = no (λ ())
  (ξ , y) ∋? x with x ≡? y
  ...          | yes refl = yes zero
  ...          | no x≢y   = mapDec suc (pred∋ x≢y) (ξ ∋? x)


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


  -- TODO

  mutual
    _∪_ : NCtx → NCtx → NCtx
    ξ ∪ ∅       = ξ
    ξ ∪ (ζ , x) with ξ ∋? x
    ...         | yes ξ∋x = ξ ∪ ζ
    ...         | no ξ∌x  = (ξ ∪ ζ , x) {{unionFresh {ζ} {{∌→Fresh ξ∌x}}}}

    unionFresh : ∀ {ζ ξ x} → {{f₁ : Fresh x ξ}} {{f₂ : Fresh x ζ}}
                           → Fresh x (ξ ∪ ζ)
    unionFresh {∅}              {ξ} {x} {{f₁}} {{f₂}} = f₁
    unionFresh {(ζ , y) {{f₀}}} {ξ} {x} {{f₁}} {{f₂}} with x ≡? y | ξ ∋? y
    ...        | yes refl | yes ξ∋y = ξ∋y ↯ Fresh→∌ {{f₁}}
    ...        | yes refl | no ξ∌y  = refl ↯ unwrap≢ (⌈fst⌉ {y ⌊≢?⌋ y} f₂)
    ...        | no x≢y   | yes ξ∋y = unionFresh {ζ} {{f₁}} {{⌈snd⌉ {x ⌊≢?⌋ y} f₂}}
    ...        | no x≢y   | no ξ∌y  = ⌈pair⌉ (wrap≢ x≢y)
                                             (unionFresh {ζ} {{f₁}} {{⌈snd⌉ {x ⌊≢?⌋ y} f₂}})

  ∪→⊇ : ∀ ξ ζ → ξ ∪ ζ ⊇ ξ
  ∪→⊇ ξ ∅       = refl⊇
  ∪→⊇ ξ (ζ , x) with ξ ∋? x
  ...            | yes ξ∋x = ∪→⊇ ξ ζ
  ...            | no ξ∌x  = drop⊇ (∪→⊇ ξ ζ)


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


  -- TODO

  mutual
    _-_ : NCtx → NCtx → NCtx
    ∅       - ζ = ∅
    (ξ , x) - ζ with ζ ∋? x
    ...         | yes ζ∋x = ξ - ζ
    ...         | no ζ∌x  = (ξ - ζ , x) {{diffFresh {ξ} {{∌→Fresh ζ∌x}}}}

    diffFresh : ∀ {ξ ζ x} → {{f₂ : Fresh x ζ}} {{f₁ : Fresh x ξ}}
                          → Fresh x (ξ - ζ)
    diffFresh {∅}     {ζ} {x} {{f₂}} {{f₁}} = yes
    diffFresh {ξ , y} {ζ} {x} {{f₂}} {{f₁}} with ζ ∋? y
    ...       | yes ζ∋y = diffFresh {ξ} {{f₂}} {{⌈snd⌉ {x ⌊≢?⌋ y} f₁}}
    ...       | no ζ∌y  = ⌈pair⌉ (⌈fst⌉ {x ⌊≢?⌋ y} f₁)
                                 (diffFresh {ξ} {{f₂}} {{⌈snd⌉ {x ⌊≢?⌋ y} f₁}})

  diff⊇ : ∀ ξ ζ → ξ ⊇ ξ - ζ
  diff⊇ ∅       ζ = done
  diff⊇ (ξ , x) ζ with ζ ∋? x
  ...             | yes ζ∋x = drop⊇ (diff⊇ ξ ζ)
  ...             | no ζ∌x  = keep⊇ (diff⊇ ξ ζ)

  -→NSub : ∀ ξ ζ → NSub ξ (ξ - ζ)
  -→NSub ξ ζ = ⊇→NSub (diff⊇ ξ ζ)


--------------------------------------------------------------------------------
--
-- Expressions


module Expressions where
  open import Prelude
    hiding (tt)
    renaming (renᵢ to ren∋ ; idᵣ to refl⊇)
  open Booleans
  open NumericExpressions
    hiding (_∋_ ; ren∋ ; _⊇_ ; refl⊇)
  module N = NumericExpressions


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

      ∇_∶_ : ∀ x {ξ} → {{f : Fresh x ξ}} → Type (ξ , x)
                     → Type ξ

  _∨_ : ∀ {ξ} → Type ξ → Type ξ → Type ξ
  A ∨ B = ~ A ⊃ B

  ∃_∶_ : ∀ x {ξ} → {{f : Fresh x ξ}} → Type (ξ , x)
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
  nsubT {ξ} σ (∇ x ∶ A) with genGreatFresh ξ
  ...                   | y , (g , (f , (refl , refl))) = ∇ y ∶ nsubT (forkNS σ {{f}}) A

  nrenT : ∀ {ξ ξ′} → ξ′ N.⊇ ξ → Type ξ
                   → Type ξ′
  nrenT η A = nsubT (⊇→NSub η) A


  -- Contexts

  Ctx : NCtx → Set
  Ctx ξ = List (Type ξ)

  nsubC : ∀ {ξ ζ} → NSub ξ ζ → Ctx ζ
                  → Ctx ξ
  nsubC σ Γ = map (nsubT σ) Γ

  nrenC : ∀ {ξ ξ′} → ξ′ N.⊇ ξ → Ctx ξ
                   → Ctx ξ′
  nrenC `η Γ = nsubC (⊇→NSub `η) Γ

  nsub∋ : ∀ {ξ ζ Γ A} → (`σ : NSub ξ ζ) → Γ ∋ A
                      → nsubC `σ Γ ∋ nsubT `σ A
  nsub∋ `σ zero    = zero
  nsub∋ `σ (suc i) = suc (nsub∋ `σ i)

  nren∋ : ∀ {ξ ξ′ Γ A} → (`η : ξ′ N.⊇ ξ) → Γ ∋ A
                       → nrenC `η Γ ∋ nrenT `η A
  nren∋ `η i = nsub∋ (⊇→NSub `η) i

  nsub⊇ : ∀ {ξ ζ Γ Γ′} → (σ : NSub ξ ζ) → Γ′ ⊇ Γ
                       → nsubC σ Γ′ ⊇ nsubC σ Γ
  nsub⊇ σ done     = done
  nsub⊇ σ (drop η) = drop (nsub⊇ σ η)
  nsub⊇ σ (keep η) = keep (nsub⊇ σ η)

  nren⊇ : ∀ {ξ ξ′ Γ Γ′} → (`η : ξ′ N.⊇ ξ) → Γ′ ⊇ Γ
                        → nrenC `η Γ′ ⊇ nrenC `η Γ
  nren⊇ `η η = nsub⊇ (⊇→NSub `η) η


{-
  -- TODO: n-ary spec/gen

  fresh⋆ : NCtx → NCtx → Bool
  fresh⋆ ∅       ξ = true
  fresh⋆ (ζ , x) ξ = fresh x ξ and fresh⋆ ζ ξ

  Fresh⋆ : NCtx → NCtx → Set
  Fresh⋆ ζ ξ = ⌈ fresh⋆ ζ ξ ⌉

  mutual
    _++_ : ∀ ξ ζ → {{f⋆ : Fresh⋆ ζ ξ}}
                 → NCtx
    (ξ ++ ∅)             {{f⋆}} = ξ
    (ξ ++ (ζ , x) {{f}}) {{f⋆}}
      = ((ξ ++ ζ) {{⌈snd⌉ {fresh x ξ} {fresh⋆ ζ ξ} f⋆}} , x)
          {{Fresh++Fresh {ξ} {ζ} {{⌈fst⌉ f⋆}} {{f}} {{⌈snd⌉ {fresh x ξ} f⋆}}}}

    Fresh++Fresh : ∀ {ξ ζ x} → {{f₁ : Fresh x ξ}} {{f₂ : Fresh x ζ}} {{f⋆ : Fresh⋆ ζ ξ}}
                             → Fresh x (ξ ++ ζ)
    Fresh++Fresh {ξ} {∅}              {x} {{f₁}} {{f₂}} {{f⋆}} = f₁
    Fresh++Fresh {ξ} {(ζ , y) {{f₀}}} {x} {{f₁}} {{f₂}} {{f⋆}}
      = ⌈pair⌉ (⌈fst⌉ {x ⌊≢?⌋ y} f₂)
               (Fresh++Fresh {ξ} {ζ} {{f₁}} {{⌈snd⌉ {x ⌊≢?⌋ y} f₂}} {{⌈snd⌉ {fresh y ξ} f⋆}})


  wk⋆⊇ : ∀ ζ {ξ} → {{f⋆ : Fresh⋆ ζ ξ}}
                 → (ξ ++ ζ) N.⊇ ξ
  wk⋆⊇ ∅       = refl⊇
  wk⋆⊇ (ζ , x) = drop⊇ (wk⋆⊇ ζ)


  ∇⋆_∶_ : ∀ ζ {ξ} → {{f⋆ : Fresh⋆ ζ ξ}} → Type (ξ ++ ζ)
                  → Type ξ
  ∇⋆ ∅     ∶ A = A
  ∇⋆ ζ , x ∶ A = ∇⋆ ζ ∶ ∇ x ∶ A

  -- TODO: Figure this out
  -- spec⋆[_] : ∀ {ζ ξ Γ} → {{f⋆ : Fresh⋆ ζ ξ}} (σ : NSub ξ (ξ ++ ζ)) {A : Type (ξ ++ ζ)}
  --                      → Exp ξ Γ (∇⋆ ζ ∶ A)
  --                      → Exp ξ Γ (nsubT σ A)
  -- spec⋆[_] {∅}     ∅            N = {!!}
  -- spec⋆[_] {∅}     (σ , M / x)  N = {!!}
  -- spec⋆[_] {ζ , x} (σ , M / .x) N = {!!}

  -- TODO: Figure this out
  -- gen⋆[_] : ∀ ζ {ξ A Γ} → {{f⋆ : Fresh⋆ ζ ξ}}
  --                       → Exp ξ Γ A
  --                       → Exp ξ Γ (∇⋆ ζ ∶ nrenT (wk⋆⊇ ζ) A)
  -- gen⋆[ ∅ ]     M = {!M!}
  -- gen⋆[ ζ , x ] M = {!gen⋆[ ζ ] {{?}} (gen[ x ] {{?}} M)!}
-}


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

      spec[_⁏_/_] : ∀ {ξ ζ} → (`σ : NSub ξ ζ) (S : NExp ξ) (x : NVar)
                            → {{f : Fresh x ζ}} {A : Type (ζ , x)} {Γ : Ctx ζ}
                            → {A₌ : Type ξ} {{_ : A₌ ≡ nsubT (`σ , S / x) A}}
                            → {Γ₌ : Ctx ξ} {{_ : Γ₌ ≡ nsubC `σ Γ}}
                            → Exp ζ Γ (∇ x ∶ A)
                            → Exp ξ Γ₌ A₌

--      spec[_/_] : ∀ {ξ ζ Γ} → (S : NExp (ξ ∪ ζ)) (x : NVar) {{f : Fresh x ξ}} {A : Type (ξ , x)}
--                            → {A₌ : Type (ξ ∪ ζ)} {{_ : A₌ ≡ nsubT (⊇→NSub (∪→⊇ ξ ζ) , S / x) A}}
--                            → {Γ₌ : Ctx (ξ ∪ ζ)} {{_ : Γ₌ ≡ nrenC (∪→⊇ ξ ζ) Γ}}
--                            → Exp ξ Γ (∇ x ∶ A)
--                            → Exp (ξ ∪ ζ) Γ₌ A₌

      gen[_] : ∀ x {ξ Γ} → {{f : Fresh x ξ}} {A : Type (ξ , x)}
                         → {Γ₌ : Ctx (ξ , x)} {{_ : Γ₌ ≡ nrenC wk⊇ Γ}}
                         → Exp (ξ , x) Γ₌ A
                         → Exp ξ Γ (∇ x ∶ A)

      sym : ∀ {ξ M N Γ} → Exp ξ Γ (M == N)
                        → Exp ξ Γ (N == M)

      trans : ∀ {ξ M N O Γ} → Exp ξ Γ (M == N) → Exp ξ Γ (N == O)
                            → Exp ξ Γ (M == O)

      nsuci : ∀ {ξ M N Γ} → Exp ξ Γ (M == N)
                          → Exp ξ Γ (nsuc M == nsuc N)

      nsuce : ∀ {ξ M N Γ} → Exp ξ Γ (nsuc M == nsuc N)
                          → Exp ξ Γ (M == N)

      induct[_] : ∀ x {ξ Γ} → {{f : Fresh x ξ}} {A : Type (ξ , x)}
                            → {A₀ : Type ξ} {{_ : A₀ ≡ nsubT (reflNS , 0 / x) A}}
                            → {Aₙ : Type (ξ , x)} {{_ : Aₙ ≡ nsubT (wkNS , nsuc (nvar x) / x) A}}
                            → Exp ξ Γ A₀ → Exp ξ Γ (∇ x ∶ (A ⊃ Aₙ))
                            → Exp ξ Γ (∇ x ∶ A)


--       -- ax1[_] : ∀ x {ξ Γ} → {{f : Fresh x ξ}}
--       --                    → Exp ξ Γ (∇ x ∶ ~ (nsuc (nvar x) == 0))
--       --
--       -- ax2[_] : ∀ x {ξ Γ} → {{f : Fresh x ξ}}
--       --                    → Exp ξ Γ (∇ x ∶ nvar x + 0 == nvar x)
--       --
--       -- ax3[_,_] : ∀ x y {ξ Γ} → {{f₁ : Fresh x ξ}} {{f₂ : Fresh y (ξ , x)}}
--       --                        → Exp ξ Γ (∇ x ∶ ∇ y ∶ nvar x + nvar y == nsuc (nvar x + nvar y))
--       --
--       -- ax4[_] : ∀ x {ξ Γ} → {{f : Fresh x ξ}}
--       --                    → Exp ξ Γ (∇ x ∶ nvar x * 0 == 0)
--       --
--       -- ax5[_,_] : ∀ x y {ξ Γ} → {{f₁ : Fresh x ξ}} {{f₂ : Fresh y (ξ , x)}}
--       --                        → Exp ξ Γ (∇ x ∶ ∇ y ∶ nvar x * nsuc (nvar y) == nvar x * nvar y + nvar x)

-- --      ax1 : ∀ {Γ} → Exp ∅ Γ (∇ "a" ∶ ~ (nsuc "a" == 0))
-- --
-- --      ax2 : ∀ {Γ} → Exp ∅ Γ (∇ "a" ∶ "a" + 0 == "a")
-- --
-- --      ax3 : ∀ {Γ} → Exp ∅ Γ (∇ "a" ∶ ∇ "b" ∶ "a" + "b" == nsuc ("a" + "b"))
-- --
-- --      ax4 : ∀ {Γ} → Exp ∅ Γ (∇ "a" ∶ "a" * 0 == 0)
-- --
-- --      ax5 : ∀ {Γ} → Exp ∅ Γ (∇ "a" ∶ ∇ "b" ∶ "a" * nsuc "b" == "a" * "b" + "a")


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




  postulate
    lemgen : ∀ {x y ξ ζ} Γ → (`σ : NSub ξ ζ)
                           → {{_ : Fresh y ξ}} {{_ : Fresh x ζ}} {A : Type (ξ , y)}
                           → Exp (ξ , y) (nsubC (dropNS `σ , nvar y / x)
                                            (nrenC (wk⊇ {x}) Γ)) A
                           → Exp (ξ , y) (nrenC (wk⊇ {y})
                                            (nsubC `σ Γ)) A

  postulate
    leminduct₀ : ∀ {x y ξ ζ Γ} → {{_ : Fresh y ξ}} {{_ : Fresh x ζ}} {A : Type (ζ , x)} {`σ : NSub ξ ζ}
                               → Exp ξ Γ (nsubT `σ
                                            (nsubT (reflNS , 0 / x) A))
                               → Exp ξ Γ (nsubT (reflNS , 0 / y)
                                            (nsubT (dropNS `σ , nvar y / x) A))

  postulate
    leminductₙ : ∀ {x y ξ ζ Γ} → {{_ : Fresh y ξ}} {{_ : Fresh x ζ}} {A : Type (ζ , x)} {`σ : NSub ξ ζ}
                               → Exp ξ Γ (∇ y ∶ nsubT (forkNS `σ) A ⊃
                                                   nsubT (forkNS {y} {x} `σ)
                                                     (nsubT (wkNS , nsuc (nvar x) / x) A))
                               → Exp ξ Γ (∇ y ∶ nsubT (dropNS `σ , nvar y / x) A ⊃
                                                   nsubT (wkNS , nsuc (nvar y) / y)
                                                     (nsubT (dropNS `σ , nvar y / x) A))

  postulate
    lemspec : ∀ {θ ξ ζ} Γ → (‶σ : NSub θ ξ) (`σ : NSub ξ ζ) (S : NExp ξ) (x : NVar)
                          → {{_ : Fresh x ζ}} {A : Type (ζ , x)}
                          → Exp θ (nsubC (transNS ‶σ `σ) Γ)
                                   (nsubT (transNS ‶σ `σ , subNE ‶σ S / x) A)
                          → Exp θ (nsubC ‶σ (nsubC `σ Γ))
                                   (nsubT ‶σ (nsubT (`σ , S / x) A))

  postulate
    lemspec′ : ∀ {θ ξ ζ} Γ′ → (‶σ : NSub θ ξ) (`σ : NSub ξ ζ) (S : NExp ξ) (x : NVar)
                            → {{_ : Fresh x ζ}} {A : Type (ζ , x)}
                            → Exp θ (nsubC ‶σ Γ′) (nsubT (transNS ‶σ `σ , subNE ‶σ S / x) A)
                            → Exp θ (nsubC ‶σ Γ′) (nsubT ‶σ (nsubT (`σ , S / x) A))


  nsub : ∀ {ξ ζ A Γ} → (`σ : NSub ξ ζ) → Exp ζ Γ A
                     → Exp ξ (nsubC `σ Γ) (nsubT `σ A)
  nsub `σ (var i)     = var (nsub∋ `σ i)
  nsub `σ (lam M)     = lam (nsub `σ M)
  nsub `σ (app M N)   = app (nsub `σ M) (nsub `σ N)
  nsub `σ (pair M N)  = pair (nsub `σ M) (nsub `σ N)
  nsub `σ (fst M)     = fst (nsub `σ M)
  nsub `σ (snd M)     = snd (nsub `σ M)
  nsub `σ (dni M)     = dni (nsub `σ M)
  nsub `σ (dne M)     = dne (nsub `σ M)
  nsub `σ (contra M)  = contra (nsub `σ M)


--      spec[_⁏_/_] : ∀ {ξ ζ} → (`σ : NSub ξ ζ) (S : NExp ξ) (x : NVar)
--                            → {{f : Fresh x ζ}} {A : Type (ζ , x)} {Γ : Ctx ζ}
--                            → {A₌ : Type ξ} {{_ : A₌ ≡ nsubT (`σ , S / x) A}}
--                            → {Γ₌ : Ctx ξ} {{_ : Γ₌ ≡ nsubC `σ Γ}}
--                            → Exp ζ Γ (∇ x ∶ A)
--                            → Exp ξ Γ₌ A₌

  nsub {θ} {.ξ} {.A₌} {.Γ₌} ‶σ
    (spec[_⁏_/_] {ξ} {ζ} `σ S x {{f}} {A} {Γ} {A₌} {{refl}} {Γ₌} {{refl}} M)
      = let S′  = subNE ‶σ S in
        let A₌′ = nsubT (transNS ‶σ `σ , S′ / x) A in
        let Γ₌′ = nsubC (transNS ‶σ `σ) Γ in
          lemspec Γ ‶σ `σ S x
            (spec[_⁏_/_] {θ} {ζ} (transNS ‶σ `σ) S′ x {{f}} {A} {Γ} {A₌′} {{refl}} {Γ₌′} {{refl}} M)


--      gen[_] : ∀ x {ξ Γ} → {{f : Fresh x ξ}} {A : Type (ξ , x)}
--                         → {Γ₌ : Ctx (ξ , x)} {{_ : Γ₌ ≡ nrenC wk⊇ Γ}}
--                         → Exp (ξ , x) Γ₌ A
--                         → Exp ξ Γ (∇ x ∶ A)

  nsub {θ} {.ξ} {.(∇ x ∶ A)} {.Γ} `σ
    (gen[ x ] {ξ} {Γ} {{f}} {A} {Γ₌} {{refl}} M)
      with genGreatFresh θ
  ... | y , (g′ , (f′ , (refl , refl)))
      = let A′ = nsubT (dropNS `σ , nvar y / x) A in
        let Γ′ = nrenC wk⊇ (nsubC `σ Γ) in
          gen[ y ] {θ} {{f′}} {A′} {Γ′} {{refl}}
            (lemgen Γ `σ {{f′}} (nsub (dropNS `σ , nvar y / x) M))


  nsub `σ (sym M)     = sym (nsub `σ M)
  nsub `σ (trans M N) = trans (nsub `σ M) (nsub `σ N)
  nsub `σ (nsuci M)   = nsuci (nsub `σ M)
  nsub `σ (nsuce M)   = nsuce (nsub `σ M)


--      induct[_] : ∀ x {ξ Γ} → {{f : Fresh x ξ}} {A : Type (ξ , x)}
--                            → {A₀ : Type ξ} {{_ : A₀ ≡ nsubT (reflNS , 0 / x) A}}
--                            → {Aₙ : Type (ξ , x)} {{_ : Aₙ ≡ nsubT (wkNS , nsuc (nvar x) / x) A}}
--                            → Exp ξ Γ A₀ → Exp ξ Γ (∇ x ∶ (A ⊃ Aₙ))
--                            → Exp ξ Γ (∇ x ∶ A)

  nsub {θ} {.ξ} {.(∇ x ∶ A)} {.Γ} `σ
    (induct[ x ] {ξ} {Γ} {{f}} {A} {A₀} {{refl}} {Aₙ} {{refl}} M N)
      with genGreatFresh θ
  ... | y , (g′ , (f′ , (refl , refl)))
      = let A′  = nsubT (dropNS `σ {{f′}} , nvar y / x) A in
        let A₀′ = nsubT (reflNS , 0 / y) A′ in
        let Aₙ′ = nsubT (wkNS , nsuc (nvar y) / y) A′ in
          induct[ y ] {θ} {{f′}} {A′} {A₀′} {{refl}} {Aₙ′} {{refl}}
            (leminduct₀ (nsub `σ M))
            (leminductₙ (nsub `σ N))




  nren : ∀ {ξ′ ξ A Γ} → (`η : ξ′ N.⊇ ξ) → Exp ξ Γ A
                      → Exp ξ′ (nrenC `η Γ) (nrenT `η A)
  nren `η M = nsub (⊇→NSub `η) M


--  nsub⊇ : ∀ {ξ ζ Γ Γ′} → (σ : NSub ξ ζ) → Γ′ ⊇ Γ
--                       → nsubC σ Γ′ ⊇ nsubC σ Γ

--   oops∋ : ∀ {ξ ζ x} → (`σ : NSub ξ ζ) (Mₛ : NExp ξ)
--                     → Σ (ζ N.∋ x) (λ i → sub∋ `σ i ≡ Mₛ)
--   oops∋ `σ iₛ = {!!}
--
--   oopsNE : ∀ {ξ ζ} → (`σ : NSub ξ ζ) (Mₛ : NExp ξ)
--                    → Σ (NExp ζ) (λ M → subNE `σ M ≡ Mₛ)
--   oopsNE `σ (nlit n)       = nlit n , refl
--   oopsNE `σ (nvar x {{i}}) = {!!}
--   oopsNE `σ (nsuc Mₛ)      with oopsNE `σ Mₛ
--   ...                      | M , refl = nsuc M , refl
--   oopsNE `σ (Mₛ + Nₛ)      with oopsNE `σ Mₛ | oopsNE `σ Nₛ
--   ...                      | M , refl | N , refl = M + N , refl
--   oopsNE `σ (Mₛ * Nₛ)      with oopsNE `σ Mₛ | oopsNE `σ Nₛ
--   ...                      | M , refl | N , refl = M * N , refl
--
--   oopsT : ∀ {ξ ζ} → (`σ : NSub ξ ζ) (Aₛ : Type ξ)
--                   → Σ (Type ζ) (λ A → nsubT `σ A ≡ Aₛ)
--   oopsT `σ (Mₛ == Nₛ) with oopsNE `σ Mₛ | oopsNE `σ Nₛ
--   ...                 | M , refl | N , refl = M == N , refl
--   oopsT `σ (~ Aₛ)     with oopsT `σ Aₛ
--   ...                 | A , refl = ~ A , refl
--   oopsT `σ (Aₛ ∧ Bₛ)  with oopsT `σ Aₛ | oopsT `σ Bₛ
--   ...                 | A , refl | B , refl = A ∧ B , refl
--   oopsT `σ (Aₛ ⊃ Bₛ)  with oopsT `σ Aₛ | oopsT `σ Bₛ
--   ...                 | A , refl | B , refl = A ⊃ B , refl
--   oopsT {ξ} {ζ} `σ (∇_∶_ x {{f}} Aₛ) with genGreatFresh ζ
--   ...                 | y , (g′ , (f′ , (refl , refl))) with oopsT {!dropNS (`σ , nvar y / x) !} Aₛ
--   ...                                                 | A , p = {!!}
-- --   with oopsT (`σ , ? / x) Aₛ
-- --   ...                 | A , refl = ?
--
-- --  nsubT {ξ} σ (∇ x ∶ A) with genGreatFresh ξ
-- --  ...                   | y , (g , (f , (refl , refl))) = ∇ y ∶ nsubT (forkNS σ {{f}}) A
--
--
--   oopsC : ∀ {ξ ζ Γ Γ′ₛ} → (`σ : NSub ξ ζ) → Γ′ₛ ⊇ nsubC `σ Γ
--                         → Σ (Ctx ζ) (λ Γ′ → Γ′ ⊇ Γ × nsubC `σ Γ′ ≡ Γ′ₛ)
--   oopsC {ξ} {ζ} {∅}     {∅}                   `σ done      = ∅ , (done , refl)
--   oopsC {ξ} {ζ} {∅}     {Γ′ₛ , Bₛ}            `σ (drop ηₛ) with oopsC {Γ = ∅} `σ ηₛ | oopsT `σ Bₛ
--   ...                                                      | Γ′ , (η , refl) | B , refl = (Γ′ , B) , (drop η , refl)
--   oopsC {ξ} {ζ} {Γ , A} {∅}                   `σ ()
--   oopsC {ξ} {ζ} {Γ , A} {Γ′ₛ , Bₛ}            `σ (drop ηₛ) with oopsC {Γ = Γ , A} `σ ηₛ | oopsT `σ Bₛ
--   ...                                                      | Γ′ , (η , refl) | B , refl = (Γ′ , B) , (drop η , refl)
--   oopsC {ξ} {ζ} {Γ , A} {Γ′ₛ , .(nsubT `σ A)} `σ (keep ηₛ) with oopsC {Γ = Γ} `σ ηₛ
--   ...                                                      | Γ′ , (η , refl) = (Γ′ , A) , (keep η , refl)


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


--      spec[_⁏_/_] : ∀ {ξ ζ} → (`σ : NSub ξ ζ) (S : NExp ξ) (x : NVar)
--                            → {{f : Fresh x ζ}} {A : Type (ζ , x)} {Γ : Ctx ζ}
--                            → {A₌ : Type ξ} {{_ : A₌ ≡ nsubT (`σ , S / x) A}}
--                            → {Γ₌ : Ctx ξ} {{_ : Γ₌ ≡ nsubC `σ Γ}}
--                            → Exp ζ Γ (∇ x ∶ A)
--                            → Exp ξ Γ₌ A₌

  ren {.ξ} {.A₌} {.Γ₌} {Γ′} η
    (spec[_⁏_/_] {ξ} {ζ} `σ S x {{f}} {A} {Γ} {A₌} {{refl}} {Γ₌} {{refl}} M)
      = {!!}
        -- let Γ₀ , η₀ = oops `σ η in
        --   spec[_⁏_/_] {ξ} {ζ} `σ S x {{f}} {A} {Γ₀} {A₌} {{refl}} {nsubC `σ Γ₀} {{refl}}
        --     (ren η₀ M)


  ren {.ξ} {.(∇ x ∶ A)} {.Γ} {Γ′} η
    (gen[ x ] {ξ} {Γ} {{f}} {A} {Γ₌} {{refl}} M)
      = gen[ x ] {ξ} {{f}} {A} {nrenC wk⊇ Γ′} {{refl}}
          (ren (nren⊇ wk⊇ η) M)

  ren η (sym M)           = sym (ren η M)
  ren η (trans M N)       = trans (ren η M) (ren η N)
  ren η (nsuci M)         = nsuci (ren η M)
  ren η (nsuce M)         = nsuce (ren η M)

  ren {.ξ} {.(∇ x ∶ A)} {.Γ} {Γ′} η
    (induct[ x ] {ξ} {Γ} {{f}} {A} {A₀} {{refl}} {Aₙ} {{refl}} M N)
      = induct[ x ] {ξ} {{f}} {A} {A₀} {{refl}} {Aₙ} {{refl}}
          (ren η M)
          (ren η N)


  gren : ∀ {ξ ζ A Γ Γ′} → (`σ : NSub ξ ζ) → Γ′ ⊇ Γ → Exp ζ Γ A
                        → Exp ξ (nsubC `σ Γ′) (nsubT `σ A)
  gren `σ η (var i)           = var (nsub∋ `σ (ren∋ η i))
  gren `σ η (lam M)           = lam (gren `σ (keep η) M)
  gren `σ η (app M N)         = app (gren `σ η M) (gren `σ η N)
  gren `σ η (pair M N)        = pair (gren `σ η M) (gren `σ η N)
  gren `σ η (fst M)           = fst (gren `σ η M)
  gren `σ η (snd M)           = snd (gren `σ η M)
  gren `σ η (dni M)           = dni (gren `σ η M)
  gren `σ η (dne M)           = dne (gren `σ η M)
  gren `σ η (contra M)        = contra (gren `σ η M)


--      spec[_⁏_/_] : ∀ {ξ ζ} → (`σ : NSub ξ ζ) (S : NExp ξ) (x : NVar)
--                            → {{f : Fresh x ζ}} {A : Type (ζ , x)} {Γ : Ctx ζ}
--                            → {A₌ : Type ξ} {{_ : A₌ ≡ nsubT (`σ , S / x) A}}
--                            → {Γ₌ : Ctx ξ} {{_ : Γ₌ ≡ nsubC `σ Γ}}
--                            → Exp ζ Γ (∇ x ∶ A)
--                            → Exp ξ Γ₌ A₌

-- from Exp ζ Γ (∇ x ∶ A)
-- to   Exp ξ Γ₌ A₌
-- ?!

--  gren : ∀ {ξ ζ A Γ Γ′} → (`σ : NSub ξ ζ) → Γ′ ⊇ Γ → Exp ζ Γ A
--                        → Exp ξ (nsubC `σ Γ′) (nsubT `σ A)

  gren {θ} {.ξ} {.A₌} {.Γ₌} {Γ′} ‶σ η
    (spec[_⁏_/_] {ξ} {ζ} `σ S x {{f}} {A} {Γ} {A₌} {{refl}} {Γ₌} {{refl}} M)
      = {!!}


--      gen[_] : ∀ x {ξ Γ} → {{f : Fresh x ξ}} {A : Type (ξ , x)}
--                         → {Γ₌ : Ctx (ξ , x)} {{_ : Γ₌ ≡ nrenC wk⊇ Γ}}
--                         → Exp (ξ , x) Γ₌ A
--                         → Exp ξ Γ (∇ x ∶ A)

  gren {θ} {.ξ} {.(∇ x ∶ A)} {.Γ} {Γ′} `σ η
    (gen[ x ] {ξ} {Γ} {{_}} {A} {Γ₌} {{refl}} M)
      with genGreatFresh θ
  ... | y , (g′ , (f′ , (refl , refl)))
      = let A′ = nsubT (dropNS `σ , nvar y / x) A in
        let Γ″ = nrenC wk⊇ (nsubC `σ Γ′) in
          gen[ y ] {θ} {{f′}} {A′} {Γ″} {{refl}}
            (lemgen Γ′ `σ {{f′}} (gren (dropNS `σ , nvar y / x) (nren⊇ wk⊇ η) M))


  gren `σ η (sym M)           = sym (gren `σ η M)
  gren `σ η (trans M N)       = trans (gren `σ η M) (gren `σ η N)
  gren `σ η (nsuci M)         = nsuci (gren `σ η M)
  gren `σ η (nsuce M)         = nsuce (gren `σ η M)


--      induct[_] : ∀ x {ξ Γ} → {{f : Fresh x ξ}} {A : Type (ξ , x)}
--                            → {A₀ : Type ξ} {{_ : A₀ ≡ nsubT (reflNS , 0 / x) A}}
--                            → {Aₙ : Type (ξ , x)} {{_ : Aₙ ≡ nsubT (wkNS , nsuc (nvar x) / x) A}}
--                            → Exp ξ Γ A₀ → Exp ξ Γ (∇ x ∶ (A ⊃ Aₙ))
--                            → Exp ξ Γ (∇ x ∶ A)

  gren {θ} {.ξ} {.(∇ x ∶ A)} {.Γ} {Γ′} `σ η
    (induct[ x ] {ξ} {Γ} {{f}} {A} {A₀} {{refl}} {Aₙ} {{refl}} M N)
      with genGreatFresh θ
  ... | y , (g′ , (f′ , (refl , refl)))
      = let A′  = nsubT (dropNS `σ {{f′}} , nvar y / x) A in
        let A₀′ = nsubT (reflNS , 0 / y) A′ in
        let Aₙ′ = nsubT (wkNS , nsuc (nvar y) / y) A′ in
          induct[ y ] {θ} {{f′}} {A′} {A₀′} {{refl}} {Aₙ′} {{refl}}
            (leminduct₀ (gren `σ η M))
            (leminductₙ (gren `σ η N))


--  postulate
--    idnsubT : ∀ {ξ} {A : Type ξ} → nsubT reflNS A ≡ A
--
--  postulate
--    idnsubC : ∀ {ξ} {Γ : Ctx ξ} → nsubC reflNS Γ ≡ Γ
--
--  ren : ∀ {ξ A Γ Γ′} → Γ′ ⊇ Γ → Exp ξ Γ A
--                     → Exp ξ Γ′ A
--  ren {ξ} {A} {Γ} {Γ′} η M
--    = coe ((λ Γ° A° → Exp ξ Γ° A°) & idnsubC ⊗ idnsubT)
--          (gren reflNS η M)




































-- --   ren : ∀ {ξ A Γ Γ′} → Γ′ ⊇ Γ → Exp ξ Γ A
-- --                      → Exp ξ Γ′ A
-- --   ren η (var i)           = var (ren∋ η i)
-- --   ren η (lam M)           = lam (ren (keep η) M)
-- --   ren η (app M N)         = app (ren η M) (ren η N)
-- --   ren η (pair M N)        = pair (ren η M) (ren η N)
-- --   ren η (fst M)           = fst (ren η M)
-- --   ren η (snd M)           = snd (ren η M)
-- --   ren η (dni M)           = dni (ren η M)
-- --   ren η (dne M)           = dne (ren η M)
-- --   ren η (contra M)        = contra (ren η M)
-- --   -- ren {ξ} {._} {._} {Γ′} η (spec[_⁏_/_] {.ξ} {ζ} `σ S x {{f}}
-- --   --                             {A‼} {Γ‼} {._} {._} {{refl}} {{refl}} M)
-- --   --                         = spec[_⁏_/_] {ξ} {ζ} {!!} S x {{f}}
-- --   --                             {A‼} {{!!}} {nsubT ({!!} , S / x) A‼} {Γ′} {{refl}} {{refl}} {!M!}
-- --   --                           -- spec[ `σ ⁏ S / x ] {{_}} {{!!}} {{!!}}
-- --   --                           --   {{!!}} {{!!}} {{{!refl!}}} {{{!refl!}}}
-- --   --                           --     M
-- -- --  ren {.(ξ ∪ ζ)} {A} {Γ} {Γ′} η
-- -- --    (spec[_/_] {ξ} {ζ} S x {{f}} {Aᴹ} {Γᴹ} {.A} {{refl}} {.Γ} {{refl}} M)
-- -- --                          = spec[_/_] {ξ} {ζ} S x {{f}} {Aᴹ} {Γᴹ} {A} {{refl}} {nrenC (∪→⊇ ξ ζ) {!Γᴹ!}} {{refl}} M
-- --   ren η (gen[ x ] {{_}} {{refl}} M)
-- --                           = gen[ x ] (ren (nren⊇ wk⊇ η) M)
-- --   ren η (sym M)           = sym (ren η M)
-- --   ren η (trans M N)       = trans (ren η M) (ren η N)
-- --   ren η (nsuci M)         = nsuci (ren η M)
-- --   ren η (nsuce M)         = nsuce (ren η M)
-- --   ren η (induct[ x ] M N) = induct[ x ] (ren η M) (ren η N)

--   wk : ∀ {ξ A B Γ} → Exp ξ Γ A
--                    → Exp ξ (Γ , B) A
--   wk M = ren (drop refl⊇) M


--   -- Substitutions

--   Sub : ∀ ξ → Ctx ξ → Ctx ξ → Set
--   Sub ξ Γ Ξ = All (Exp ξ Γ) Ξ

--   ⊇→Sub : ∀ {ξ Γ Γ′} → Γ′ ⊇ Γ
--                       → Sub ξ Γ′ Γ
--   ⊇→Sub done     = ∅
--   ⊇→Sub (drop η) = mapAll wk (⊇→Sub η)
--   ⊇→Sub (keep η) = mapAll wk (⊇→Sub η) , var zero



--   -- -- lem : ∀ {ξ A Γ} → Exp ξ Γ (A ∨ ~ A)
--   -- -- lem = lam v0

--   -- -- define : ∀ {ξ A C Γ} → Exp ξ Γ A → Exp ξ (Γ , A) C
--   -- --                      → Exp ξ Γ C
--   -- -- define M N = app (lam N) M

--   -- -- ntra : ∀ {ξ A B Γ} → Exp ξ Γ (~ B ⊃ ~ A)
--   -- --                    → Exp ξ Γ (A ⊃ B)
--   -- -- ntra M = lam (dne (app (wk (contra M)) (dni v0)))

--   -- -- deny : ∀ {ξ A C Γ} → Exp ξ Γ A → Exp ξ Γ (~ A)
--   -- --                    → Exp ξ Γ C
--   -- -- deny M N = app (ntra (lam (wk N))) M


--   -- -- -- TT : ∀ {ξ} → Type ξ
--   -- -- -- TT {ξ} with genFresh ξ
--   -- -- -- ...    | x , f = let instance _ = f in
--   -- -- --                    ∇ x ∶ ~ (nsuc (nvar x) == 0)
--   -- -- --
--   -- -- -- tt : ∀ {ξ Γ} → Exp ξ Γ TT
--   -- -- -- tt {ξ} {Γ} with genGreat ξ | genFresh ξ
--   -- -- -- ...        | x , g | _ , f = let instance _ = f in
--   -- -- --                                 ax1[ x ] {ξ} {Γ}
--   -- -- --
--   -- -- -- FF : ∀ {ξ} → Type ξ
--   -- -- -- FF = ~ TT
--   -- -- --
--   -- -- -- fen : ∀ {ξ A Γ} → Exp ξ (Γ , A) FF
--   -- -- --                 → Exp ξ Γ (~ A)
--   -- -- -- fen M = app (contra (lam M)) (dni tt)
--   -- -- --
--   -- -- -- fe : ∀ {ξ A Γ} → Exp ξ (Γ , ~ A) FF
--   -- -- --                → Exp ξ Γ A
--   -- -- -- fe M = dne (fen M)
--   -- -- --
--   -- -- -- efq : ∀ {ξ C Γ} → Exp ξ Γ FF
--   -- -- --                 → Exp ξ Γ C
--   -- -- -- efq M = fe (wk M)


--   -- -- TT : ∀ {ξ} → Type ξ
--   -- -- TT = 0 == 0

--   -- -- refl== : ∀ {Γ} → Exp ∅ Γ (∇ "a" ∶ "a" == "a")
--   -- -- refl== = gen[ "a" ] (trans
--   -- --            (sym {!!}) -- (sym (spec[_] {∅ , "a"} {∅} {{yes}} (∅ , "a" / "a") {!ax2!}))
--   -- --            {!ax2!})
--   -- -- -- refl== = gen[ "a" ] (trans
--   -- -- --            (sym (spec[ {!nvar 0!} / "a" ] ax2))
--   -- -- --            (spec[ {!!} / "a" ] ax2))




--   -- -- -- dni⊃₁ : ∀ {ξ A B Γ} → Exp ξ Γ (A ⊃ B)
--   -- -- --                     → Exp ξ Γ (~ ~ A ⊃ B)
--   -- -- -- dni⊃₁ M = lam (app (wk M) (dne v0))

--   -- -- -- dne⊃₂ : ∀ {ξ A B Γ} → Exp ξ Γ (A ⊃ ~ ~ B)
--   -- -- --                     → Exp ξ Γ (A ⊃ B)
--   -- -- -- dne⊃₂ M = lam (dne (app (wk M) v0))

--   -- -- -- swap∨ : ∀ {ξ A B Γ} → Exp ξ Γ (A ∨ B)
--   -- -- --                     → Exp ξ Γ (B ∨ A)
--   -- -- -- swap∨ M = dne⊃₂ (contra M)

--   -- -- -- right : ∀ {ξ A B Γ} → Exp ξ Γ B
--   -- -- --                     → Exp ξ Γ (A ∨ B)
--   -- -- -- right M = lam (wk M)

--   -- -- -- left : ∀ {ξ A B Γ} → Exp ξ Γ A
--   -- -- --                    → Exp ξ Γ (A ∨ B)
--   -- -- -- left M = swap∨ (right M)

--   -- -- -- sndK*36 : ∀ {ξ A B C Γ} → Exp ξ Γ ((A ∨ B) ∧ (A ∨ C))
--   -- -- --                         → Exp ξ Γ (A ∨ (B ∧ C))
--   -- -- -- sndK*36 M = lam (pair
--   -- -- --               (app (fst (wk M)) v0)
--   -- -- --               (app (snd (wk M)) v0))

--   -- -- -- -- ∨→~∧ : ∀ {ξ A B Γ} → Exp ξ Γ (~ A ∨ ~ B)
--   -- -- -- --                     → Exp ξ Γ (~ (A ∧ B))
--   -- -- -- -- ∨→~∧ M = fen (deny
--   -- -- -- --             (snd v0)
--   -- -- -- --             (app
--   -- -- -- --               (wk M)
--   -- -- -- --               (dni (fst v0))))
--   -- -- -- --
--   -- -- -- -- woop : ∀ {ξ A C Γ} → Exp ξ (Γ , A) C → Exp ξ (Γ , ~ A) C
--   -- -- -- --                    → Exp ξ Γ C
--   -- -- -- -- woop M N = app
--   -- -- -- --              (swap∨ (sndK*36 (pair
--   -- -- -- --                (swap∨ (dni⊃₁ (lam M)))
--   -- -- -- --                (swap∨ (dni⊃₁ (lam N))))))
--   -- -- -- --              (fen (deny
--   -- -- -- --                (fst v0)
--   -- -- -- --                (snd v0)))
