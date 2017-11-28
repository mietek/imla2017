module TNT5 where

open import Prelude public


--------------------------------------------------------------------------------
--
-- Naturals


_≟_ : (n m : Nat) → Dec (n ≡ m)
zero  ≟ zero  = yes refl
zero  ≟ suc m = no (λ ())
suc n ≟ zero  = no (λ ())
suc n ≟ suc m with n ≟ m
...           | yes refl = yes refl
...           | no n≢m   = no (n≢m ∘ injsuc)


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

_≥?_ : ∀ n m  → Dec (n ≥ m)
zero  ≥? zero  = yes done
zero  ≥? suc m = no (λ ())
suc n ≥? zero  = yes done
suc n ≥? suc m with n ≥? m
...            | yes n≥m = yes (keep n≥m)
...            | no n≱m  = no (n≱m ∘ pred≥)


_≱_ : Nat → Nat → Set
n ≱ m = ¬ (n ≥ m)

n≱sn : ∀ {n} → n ≱ suc n
n≱sn (keep n≥sn) = n≥sn ↯ n≱sn


_>_ : Nat → Nat → Set
n > m = n ≥ suc m

trans> : ∀ {n m k} → n > m → m > k
                   → n > k
trans> n>m m>k = trans≥ n>m (drop≥ m>k)

>→≥ : ∀ {n m} → n > m
               → n ≥ m
>→≥ (keep n≥m) = trans≥ (drop≥ refl≥) n≥m

>→≢ : ∀ {n m} → n > m
               → n ≢ m
>→≢ n>m refl = n≱sn n>m

_>?_ : ∀ n m  → Dec (n > m)
n >? m = n ≥? suc m


_<_ : Nat → Nat → Set
n < m = m > n

≱→< : ∀ {n m} → n ≱ m
               → n < m
≱→< {n}     {zero}  n≱z   = done ↯ n≱z
≱→< {zero}  {suc m} z≱sm  = keep done
≱→< {suc n} {suc m} sn≱sm = keep (≱→< (sn≱sm ∘ keep))


_≤_ : Nat → Nat → Set
n ≤ m = m ≥ n

≱→≤ : ∀ {n m} → n ≱ m
               → n ≤ m
≱→≤ = >→≥ ∘ ≱→<


--------------------------------------------------------------------------------
--
-- Syntax


NVar : Set
NVar = Nat

mutual
  data NCtx : Set
    where
      ∅ : NCtx

      _,_ : ∀ ξ x → {{φ : fresh x ξ}}
                  → NCtx

  fresh : NVar → NCtx → Set
  fresh x ∅       = ⊤
  fresh x (ξ , y) = x ≢ y × fresh x ξ

big : NVar → NCtx → Set
big x ∅       = ⊤
big x (ξ , y) = x > y × big x ξ

big→fresh : ∀ {x ξ} → {{β : big x ξ}}
                     → fresh x ξ
big→fresh {x} {∅}     {{tt}}      = tt
big→fresh {x} {ξ , y} {{x>y , β}} = >→≢ x>y , big→fresh {{β}}

infix 4 _N∋_
data _N∋_ : NCtx → NVar → Set
  where
    instance
      zero : ∀ {ξ x} → {{φ : fresh x ξ}}
                     → ξ , x N∋ x

      suc : ∀ {ξ x y} → {{φ : fresh y ξ}} → ξ N∋ x
                      → ξ , y N∋ x

_N∌_ : NCtx → NVar → Set
ξ N∌ x = ¬ (ξ N∋ x)

fresh→N∌ : ∀ {x ξ} → {{φ : fresh x ξ}}
                    → ξ N∌ x
fresh→N∌ {x} {{x≢x , φ}} zero    = refl ↯ x≢x
fresh→N∌ {x} {{x≢y , φ}} (suc i) = i ↯ fresh→N∌ {{φ}}

infix 4 _N⊇_
data _N⊇_ : NCtx → NCtx → Set
  where
    done : ∀ {ξ} → ξ N⊇ ∅

    step : ∀ {ξ ξ′ x} → {{φ : fresh x ξ}} → ξ′ N⊇ ξ → ξ′ N∋ x
                      → ξ′ N⊇ ξ , x

extN⊇ : ∀ {ξ ξ′} → (∀ {x} → ξ N∋ x → ξ′ N∋ x)
                 → ξ′ N⊇ ξ
extN⊇ {∅}     f = done
extN⊇ {ξ , x} f = step (extN⊇ (f ∘ suc)) (f zero)

renN∋ : ∀ {ξ ξ′ x} → ξ′ N⊇ ξ → ξ N∋ x
                   → ξ′ N∋ x
renN∋ done       ()
renN∋ (step η j) zero    = j
renN∋ (step η j) (suc i) = renN∋ η i

reflN⊇ : ∀ {ξ} → ξ N⊇ ξ
reflN⊇ = extN⊇ id

transN⊇ : ∀ {ξ ξ′ ξ″} → ξ″ N⊇ ξ′ → ξ′ N⊇ ξ → ξ″ N⊇ ξ
transN⊇ η₁ η₂ = extN⊇ (λ i → renN∋ η₁ (renN∋ η₂ i))

dropN⊇ : ∀ {x ξ ζ} → ξ N⊇ ζ → {{φ : fresh x ξ}}
                   → ξ , x N⊇ ζ
dropN⊇ η = transN⊇ (extN⊇ suc) η

keepN⊇ : ∀ {x ξ ζ} → ξ N⊇ ζ → {{φ₁ : fresh x ξ}} {{φ₂ : fresh x ζ}}
                   → ξ , x N⊇ ζ , x
keepN⊇ η = step (dropN⊇ η) zero

uniqN∋ : ∀ {ξ x} → (i₁ i₂ : ξ N∋ x) → i₁ ≡ i₂
uniqN∋ zero     zero     = refl
uniqN∋ zero     (suc i₂) = i₂ ↯ fresh→N∌
uniqN∋ (suc i₁) zero     = i₁ ↯ fresh→N∌
uniqN∋ (suc i₁) (suc i₂) = suc & uniqN∋ i₁ i₂

uniqN⊇ : ∀ {ξ ξ′} → (η₁ η₂ : ξ′ N⊇ ξ) → η₁ ≡ η₂
uniqN⊇ done         done         = refl
uniqN⊇ (step η₁ i₁) (step η₂ i₂) = step & uniqN⊇ η₁ η₂ ⊗ uniqN∋ i₁ i₂

data NExp : NCtx → Set
  where
    nat : ∀ {ξ} → Nat
                → NExp ξ

    nvar : ∀ {ξ} → (x : NVar) {{i : ξ N∋ x}}
                 → NExp ξ

    suc : ∀ {ξ} → NExp ξ
                → NExp ξ

    _+_ : ∀ {ξ} → NExp ξ → NExp ξ
                → NExp ξ

    _*_ : ∀ {ξ} → NExp ξ → NExp ξ
                → NExp ξ

renNE : ∀ {ξ ξ′} → ξ′ N⊇ ξ → NExp ξ
                 → NExp ξ′
renNE η (nat n)        = nat n
renNE η (nvar x {{i}}) = nvar x {{renN∋ η i}}
renNE η (suc M)        = suc (renNE η M)
renNE η (M + N)        = renNE η M + renNE η N
renNE η (M * N)        = renNE η M * renNE η N

data NSub : NCtx → NCtx → Set
  where
    ∅ : ∀ {ξ} → NSub ξ ∅

    _,_ : ∀ {ξ ζ x} → NSub ξ ζ → NExp ξ → {{φ : fresh x ζ}}
                    → NSub ξ (ζ , x)

renNS : ∀ {ζ ξ ξ′} → ξ′ N⊇ ξ → NSub ξ ζ
                   → NSub ξ′ ζ
renNS {∅}     η ∅       = ∅
renNS {ζ , x} η (σ , M) = renNS η σ , renNE η M

dropNS : ∀ {x ξ ζ} → NSub ξ ζ → {{φ : fresh x ξ}}
                   → NSub (ξ , x) ζ
dropNS σ = renNS (dropN⊇ reflN⊇) σ

forkNS : ∀ {x y ξ ζ} → NSub ξ ζ → {{φ₁ : fresh x ξ}} {{φ₂ : fresh y ζ}}
                     → NSub (ξ , x) (ζ , y)
forkNS {x} σ = dropNS σ , nvar x

keepNS : ∀ {x ξ ζ} → NSub ξ ζ → {{φ₁ : fresh x ξ}} {{φ₂ : fresh x ζ}}
                   → NSub (ξ , x) (ζ , x)
keepNS σ = forkNS σ

reflNS : ∀ {ξ} → NSub ξ ξ
reflNS {∅}     = ∅
reflNS {ξ , x} = keepNS reflNS

subN∋ : ∀ {ζ ξ x} → NSub ξ ζ → ζ N∋ x
                  → NExp ξ
subN∋ {∅}     ∅      ()
subN∋ {ζ , x} (σ , M) zero    = M
subN∋ {ζ , x} (σ , N) (suc i) = subN∋ σ i

subNE : ∀ {ξ ζ} → NSub ξ ζ → NExp ζ
                → NExp ξ
subNE σ (nat n)        = nat n
subNE σ (nvar x {{i}}) = subN∋ σ i
subNE σ (suc M)        = suc (subNE σ M)
subNE σ (M + N)        = subNE σ M + subNE σ N
subNE σ (M * N)        = subNE σ M * subNE σ N

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

    ∇_∶_ : ∀ {ξ} → (x : NVar) {{φ : fresh x ξ}} → Type (ξ , x)
                 → Type ξ

_∨_ : ∀ {ξ} → Type ξ → Type ξ → Type ξ
A ∨ B = (~ A) ⊃ B

∃_∶_ : ∀ {ξ} → (x : NVar) {{φ : fresh x ξ}} → Type (ξ , x)
             → Type ξ
∃ x ∶ A = ~ (∇ x ∶ ~ A)

_⫗_ : ∀ {ξ} → Type ξ → Type ξ → Type ξ
A ⫗ B = (A ⊃ B) ∧ (B ⊃ A)

transbig : ∀ {ξ x y} → y > x → {{β : big x ξ}}
                     → big y ξ
transbig {∅}     y>x {{tt}}      = tt
transbig {ξ , z} y>x {{x>z , β}} = trans> y>x x>z , transbig y>x {{β}}

genbig : (ξ : NCtx) → Σ NVar (λ y → big y ξ)
genbig ∅       = zero , tt
genbig (ξ , x) with genbig ξ
genbig (ξ , x) | y  , β with y >? x
genbig (ξ , x) | y  , β | yes y>x = y , (y>x , β)
genbig (ξ , x) | y  , β | no y≯x  = suc x , (refl≥ , transbig (≱→< y≯x) {{β}})

genfresh : (ξ : NCtx) → Σ NVar (λ y → fresh y ξ)
genfresh ξ with genbig ξ
genfresh ξ | y , β = y , big→fresh {{β}}

backfresh : ∀ {x ξ ξ′} → ξ′ N⊇ ξ → {{φ : fresh x ξ′}}
                       → fresh x ξ
backfresh      done               = tt
backfresh {x} (step {x = y}  η i) with x ≟ y
backfresh {x} (step {x = .x} η i) | yes refl = i ↯ fresh→N∌
backfresh {x} (step {x = y}  η i) | no x≢y   = x≢y , backfresh η 

subT : ∀ {ξ ζ} → NSub ξ ζ → Type ζ
               → Type ξ
subT     σ (M == N)  = subNE σ M == subNE σ N
subT     σ (~ A)     = ~ (subT σ A)
subT     σ (A ∧ B)   = subT σ A ∧ subT σ B
subT     σ (A ⊃ B)   = subT σ A ⊃ subT σ B
subT {ξ} σ (∇ x ∶ A) with genfresh ξ
subT {ξ} σ (∇ x ∶ A) | x′ , φ′ = ∇ x′ ∶ subT (forkNS σ {{φ′}}) A

N⊇→NSub : ∀ {ξ ξ′} → ξ′ N⊇ ξ
                    → NSub ξ′ ξ
N⊇→NSub done               = ∅
N⊇→NSub (step {x = x} η i) = N⊇→NSub η , nvar x {{i}}

renT : ∀ {ξ ξ′} → ξ′ N⊇ ξ → Type ξ
                → Type ξ′
renT η A = subT (N⊇→NSub η) A
