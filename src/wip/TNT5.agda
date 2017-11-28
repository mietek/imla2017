module TNT5 where

open import Prelude public
  hiding (_∋_ ; _⊇_)


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
>→≥ (keep n≥m) = trans≥ (drop≥ refl≥) n≥m

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


NVar : Set
NVar = Nat


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

uniq⊇ : ∀ {ξ ξ′} → (η₁ η₂ : ξ′ ⊇ ξ)
                 → η₁ ≡ η₂
uniq⊇ done         done         = refl
uniq⊇ (step η₁ i₁) (step η₂ i₂) = step & uniq⊇ η₁ η₂ ⊗ uniq∋ i₁ i₂


-- Numeric expressions

data NExp : NCtx → Set
  where
    nat : ∀ {ξ} → Nat
                → NExp ξ

    nvar : ∀ {ξ} → (x : NVar) {{i : ξ ∋ x}}
                 → NExp ξ

    suc : ∀ {ξ} → NExp ξ
                → NExp ξ

    _+_ : ∀ {ξ} → NExp ξ → NExp ξ
                → NExp ξ

    _*_ : ∀ {ξ} → NExp ξ → NExp ξ
                → NExp ξ


-- Numeric substitutions

data NSub : NCtx → NCtx → Set
  where
    ∅ : ∀ {ξ} → NSub ξ ∅

    _,_ : ∀ {ξ ζ x} → NSub ξ ζ → NExp ξ → {{f : fresh x ζ}}
                    → NSub ξ (ζ , x)

⊇→NSub : ∀ {ξ ξ′} → ξ′ ⊇ ξ
                    → NSub ξ′ ξ
⊇→NSub done               = ∅
⊇→NSub (step {x = x} η i) = ⊇→NSub η , nvar x {{i}}

sub∋ : ∀ {ζ ξ x} → NSub ξ ζ → ζ ∋ x
                  → NExp ξ
sub∋ {∅}     ∅      ()
sub∋ {ζ , x} (σ , M) zero    = M
sub∋ {ζ , x} (σ , N) (suc i) = sub∋ σ i

subNE : ∀ {ξ ζ} → NSub ξ ζ → NExp ζ
                → NExp ξ
subNE σ (nat n)        = nat n
subNE σ (nvar x {{i}}) = sub∋ σ i
subNE σ (suc M)        = suc (subNE σ M)
subNE σ (M + N)        = subNE σ M + subNE σ N
subNE σ (M * N)        = subNE σ M * subNE σ N

renNE : ∀ {ξ ξ′} → ξ′ ⊇ ξ → NExp ξ
                 → NExp ξ′
renNE η M = subNE (⊇→NSub η) M

renNS : ∀ {ζ ξ ξ′} → ξ′ ⊇ ξ → NSub ξ ζ
                   → NSub ξ′ ζ
renNS {∅}     η ∅       = ∅
renNS {ζ , x} η (σ , M) = renNS η σ , renNE η M

dropNS : ∀ {x ξ ζ} → NSub ξ ζ → {{f : fresh x ξ}}
                   → NSub (ξ , x) ζ
dropNS σ = renNS (drop⊇ refl⊇) σ

forkNS : ∀ {x y ξ ζ} → NSub ξ ζ → {{f₁ : fresh x ξ}} {{f₂ : fresh y ζ}}
                     → NSub (ξ , x) (ζ , y)
forkNS {x} σ = dropNS σ , nvar x

keepNS : ∀ {x ξ ζ} → NSub ξ ζ → {{f₁ : fresh x ξ}} {{f₂ : fresh x ζ}}
                   → NSub (ξ , x) (ζ , x)
keepNS σ = forkNS σ

reflNS : ∀ {ξ} → NSub ξ ξ
reflNS {∅}     = ∅
reflNS {ξ , x} = keepNS reflNS

transNS : ∀ {ξ ζ θ} → NSub ξ ζ → NSub ζ θ
                    → NSub ξ θ
transNS σ₁ ∅        = ∅
transNS σ₁ (σ₂ , N) = transNS σ₁ σ₂ , subNE σ₁ N


--------------------------------------------------------------------------------
--
-- Types


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
A ∨ B = (~ A) ⊃ B

∃_∶_ : ∀ {ξ} → (x : NVar) {{f : fresh x ξ}} → Type (ξ , x)
             → Type ξ
∃ x ∶ A = ~ (∇ x ∶ ~ A)

_⫗_ : ∀ {ξ} → Type ξ → Type ξ → Type ξ
A ⫗ B = (A ⊃ B) ∧ (B ⊃ A)

subT : ∀ {ξ ζ} → NSub ξ ζ → Type ζ
               → Type ξ
subT {ξ} σ (M == N)  = subNE σ M == subNE σ N
subT {ξ} σ (~ A)     = ~ (subT σ A)
subT {ξ} σ (A ∧ B)   = subT σ A ∧ subT σ B
subT {ξ} σ (A ⊃ B)   = subT σ A ⊃ subT σ B
subT {ξ} σ (∇ x ∶ A) with genfresh ξ
...                  | y , f = ∇ y ∶ subT (forkNS σ {{f}}) A

renT : ∀ {ξ ξ′} → ξ′ ⊇ ξ → Type ξ
                → Type ξ′
renT η A = subT (⊇→NSub η) A
