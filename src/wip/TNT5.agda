module TNT5 where

open import Prelude public


not : Bool → Bool
not true  = false
not false = true

_and_ : Bool → Bool → Bool
true  and x = x
false and x = false

⌊_⌋ : ∀ {ℓ} {X : Set ℓ} → Dec X → Bool
⌊ yes _ ⌋ = true
⌊ no  _ ⌋ = false

NVar : Set
NVar = Nat

_N≟_ : (x₁ x₂ : NVar) → Dec (x₁ ≡ x₂)
zero   N≟ zero   = yes refl
zero   N≟ suc x₂ = no (λ ())
suc x₁ N≟ zero   = no (λ ())
suc x₁ N≟ suc x₂ with x₁ N≟ x₂
...              | yes refl = yes refl
...              | no x₁≢x₂ = no (x₁≢x₂ ∘ injsuc)

data _N≥_ : NVar → NVar → Set
  where
    done : ∀ {x} → x N≥ zero

    step : ∀ {x y} → x N≥ y
                   → suc x N≥ suc y

predN≥ : ∀ {x y} → suc x N≥ suc y
                 → x N≥ y
predN≥ (step p) = p

_N≥?_ : (x y : NVar) → Dec (x N≥ y)
zero  N≥? zero  = yes done
zero  N≥? suc y = no (λ ())
suc x N≥? zero  = yes done
suc x N≥? suc y with x N≥? y
...             | yes x≥y = yes (step x≥y)
...             | no x≱y  = no (x≱y ∘ predN≥)

_N>_ : NVar → NVar → Set
x N> y = x N≥ suc y

_N>?_ : (x y : NVar) → Dec (x N> y)
x N>? y = x N≥? suc y

reflN≥ : ∀ {x} → x N≥ x
reflN≥ {zero}  = done
reflN≥ {suc x} = step reflN≥

transN≥ : ∀ {x y z} → x N≥ y → y N≥ z
                    → x N≥ z
transN≥ p        done     = done
transN≥ (step p) (step q) = step (transN≥ p q)

stepN≥ : ∀ {x y} → x N≥ y
                 → suc x N≥ y
stepN≥ done     = done
stepN≥ (step p) = step (stepN≥ p)

N>→N≥ : ∀ {x y} → x N> y
                 → x N≥ y
N>→N≥ (step p) = transN≥ (stepN≥ reflN≥) p

_N≱_ : NVar → NVar → Set
x N≱ y = ¬ (x N≥ y)

_N≯_ : NVar → NVar → Set
x N≯ y = ¬ (x N> y)

_N≤_ : NVar → NVar → Set
x N≤ y = y N≥ x

_N<_ : NVar → NVar → Set
x N< y = y N> x

N≱→N< : ∀ {x y} → x N≱ y
                 → x N< y
N≱→N< {x}     {zero}  p = done ↯ p
N≱→N< {zero}  {suc y} p = step done
N≱→N< {suc x} {suc y} p = step (N≱→N< (p ∘ step))

N≱→N≤ : ∀ {x y} → x N≱ y
                 → x N≤ y
N≱→N≤ = N>→N≥ ∘ N≱→N<

N≥+≢→N> : ∀ {x y} → x N≥ y → x ≢ y
                   → x N> y
N≥+≢→N> {zero}  {y}     done     q = refl ↯ q
N≥+≢→N> {suc x} {zero}  done     q = step done
N≥+≢→N> {suc x} {suc y} (step p) q = step (N≥+≢→N> p (q ∘ (suc &_)))

sxN≥x : ∀ {x} → suc x N≥ x
sxN≥x {zero}  = done
sxN≥x {suc x} = step sxN≥x

xN≱sx : ∀ {x} → x N≱ suc x
xN≱sx (step p) = xN≱sx p

N>→≢ : ∀ {x y} → x N> y
                → x ≢ y
N>→≢ x>y refl = xN≱sx x>y

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
big x (ξ , y) = x N> y × big x ξ

big→fresh : ∀ {x ξ} → {{β : big x ξ}}
                     → fresh x ξ
big→fresh {x} {∅}     {{tt}}      = tt
big→fresh {x} {ξ , y} {{x>y , β}} = N>→≢ x>y , big→fresh {{β}}

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

keepNS : ∀ {x y ξ ζ} → NSub ξ ζ → {{φ₁ : fresh x ξ}} {{φ₂ : fresh y ζ}}
                     → NSub (ξ , x) (ζ , y)
keepNS {x} σ = dropNS σ , nvar x

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

biglem₁ : ∀ {ξ x y} → y N> x → {{β : big x ξ}}
                    → big y ξ
biglem₁ = {!!}

biglem₂ : ∀ {ξ x y} → y N> x → {{β : big y ξ}} {{φ : fresh x ξ}}
                    → big y (ξ , x)
biglem₂ = {!!}

genbig : (ξ : NCtx) → Σ NVar (λ y → big y ξ)
genbig ∅       = zero , tt
genbig (ξ , x) with genbig ξ
genbig (ξ , x) | y  , β with y N>? x
genbig (ξ , x) | y  , β | yes y>x = y , biglem₂ y>x {{β}}
genbig (ξ , x) | y  , β | no y≯x  = suc x , (reflN≥ , biglem₁ (N≱→N< y≯x) {{β}})

genfresh : (ξ : NCtx) → Σ NVar (λ y → fresh y ξ)
genfresh ξ with genbig ξ
genfresh ξ | y , β = y , big→fresh {{β}}

-- -- -- renT : ∀ {ξ ξ′} → ξ′ N⊇ ξ → Type ξ
-- -- --                 → Type ξ′
-- -- -- renT η (M == N)  = renNE η M == renNE η N
-- -- -- renT η (~ A)     = ~ (renT η A)
-- -- -- renT η (A ∧ B)   = renT η A ∧ renT η B
-- -- -- renT η (A ⊃ B)   = renT η A ⊃ renT η B
-- -- -- renT η (∇_∶_ x {{φ}} A) = let x′ , φ′ = refreshN⊇ x η in
-- -- --                           ∇_∶_ x′ {{φ′}} (renT {!keepN⊇ η {{φ′}} !} A)

-- -- -- subT : ∀ {ξ ζ} → NSub ξ ζ → Type ζ
-- -- --                → Type ξ
-- -- -- subT σ (M == N)  = subNE σ M == subNE σ N
-- -- -- subT σ (~ A)     = ~ (subT σ A)
-- -- -- subT σ (A ∧ B)   = subT σ A ∧ subT σ B
-- -- -- subT σ (A ⊃ B)   = subT σ A ⊃ subT σ B
-- -- -- subT σ (∇ x ∶ A) = let y = {!!} in
-- -- --                    ∇_∶_ y {{{!!}}} (subT (keepNS σ {{{!!}}}) A)
