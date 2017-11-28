module TNT4 where

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

data NVar : Set
  where
    a  : NVar
    b  : NVar
    c  : NVar
    d  : NVar
    e  : NVar
    _′ : NVar → NVar

inj≡′ : ∀ {x₁ x₂} → x₁ ′ ≡ x₂ ′ → x₁ ≡ x₂
inj≡′ refl = refl

infix 5 _N≟_
_N≟_ : (x₁ x₂ : NVar) → Dec (x₁ ≡ x₂)
a    N≟ a    = yes refl
a    N≟ b    = no (λ ())
a    N≟ c    = no (λ ())
a    N≟ d    = no (λ ())
a    N≟ e    = no (λ ())
a    N≟ x₂ ′ = no (λ ())
b    N≟ a    = no (λ ())
b    N≟ b    = yes refl
b    N≟ c    = no (λ ())
b    N≟ d    = no (λ ())
b    N≟ e    = no (λ ())
b    N≟ x₂ ′ = no (λ ())
c    N≟ a    = no (λ ())
c    N≟ b    = no (λ ())
c    N≟ c    = yes refl
c    N≟ d    = no (λ ())
c    N≟ e    = no (λ ())
c    N≟ x₂ ′ = no (λ ())
d    N≟ a    = no (λ ())
d    N≟ b    = no (λ ())
d    N≟ c    = no (λ ())
d    N≟ d    = yes refl
d    N≟ e    = no (λ ())
d    N≟ x₂ ′ = no (λ ())
e    N≟ a    = no (λ ())
e    N≟ b    = no (λ ())
e    N≟ c    = no (λ ())
e    N≟ d    = no (λ ())
e    N≟ e    = yes refl
e    N≟ x₂ ′ = no (λ ())
x₁ ′ N≟ a    = no (λ ())
x₁ ′ N≟ b    = no (λ ())
x₁ ′ N≟ c    = no (λ ())
x₁ ′ N≟ d    = no (λ ())
x₁ ′ N≟ e    = no (λ ())
x₁ ′ N≟ x₂ ′ with x₁ N≟ x₂
...          | yes refl = yes refl
...          | no x₁≢x₂ = no (x₁≢x₂ ∘ inj≡′)

infix 4 _N>_
data _N>_ : NVar → NVar → Set
  where
    bN>a   : b N> a
    cN>a   : c N> a
    dN>a   : d N> a
    eN>a   : e N> a
    x′N>a  : ∀ {x} → x ′ N> a
    cN>b   : c N> b
    dN>b   : d N> b
    eN>b   : e N> b
    x′N>b  : ∀ {x} → x ′ N> b
    dN>c   : d N> c
    eN>c   : e N> c
    x′N>c  : ∀ {x} → x ′ N> c
    eN>d   : e N> d
    x′N>d  : ∀ {x} → x ′ N> d
    x′N>e  : ∀ {x} → x ′ N> e
    x′N>y′ : ∀ {x y} → x N> y → x ′ N> y ′

injN>′ : ∀ {x₁ x₂} → x₁ ′ N> x₂ ′ → x₁ N> x₂
injN>′ (x′N>y′ p) = p

infix 5 _N⩼_
_N⩼_ : (x₁ x₂ : NVar) → Dec (x₁ N> x₂)
a    N⩼ a    = no (λ ())
a    N⩼ b    = no (λ ())
a    N⩼ c    = no (λ ())
a    N⩼ d    = no (λ ())
a    N⩼ e    = no (λ ())
a    N⩼ x₂ ′ = no (λ ())
b    N⩼ a    = yes bN>a
b    N⩼ b    = no (λ ())
b    N⩼ c    = no (λ ())
b    N⩼ d    = no (λ ())
b    N⩼ e    = no (λ ())
b    N⩼ x₂ ′ = no (λ ())
c    N⩼ a    = yes cN>a
c    N⩼ b    = yes cN>b
c    N⩼ c    = no (λ ())
c    N⩼ d    = no (λ ())
c    N⩼ e    = no (λ ())
c    N⩼ x₂ ′ = no (λ ())
d    N⩼ a    = yes dN>a
d    N⩼ b    = yes dN>b
d    N⩼ c    = yes dN>c
d    N⩼ d    = no (λ ())
d    N⩼ e    = no (λ ())
d    N⩼ x₂ ′ = no (λ ())
e    N⩼ a    = yes eN>a
e    N⩼ b    = yes eN>b
e    N⩼ c    = yes eN>c
e    N⩼ d    = yes eN>d
e    N⩼ e    = no (λ ())
e    N⩼ x₂ ′ = no (λ ())
x₁ ′ N⩼ a    = yes x′N>a
x₁ ′ N⩼ b    = yes x′N>b
x₁ ′ N⩼ c    = yes x′N>c
x₁ ′ N⩼ d    = yes x′N>d
x₁ ′ N⩼ e    = yes x′N>e
x₁ ′ N⩼ x₂ ′ with x₁ N⩼ x₂
...          | yes x₁N>x₂ = yes (x′N>y′ x₁N>x₂)
...          | no x₁N≯x₂  = no (x₁N≯x₂ ∘ injN>′)

N>→≢ : ∀ {x₁ x₂} → x₁ N> x₂
                  → x₁ ≢ x₂
N>→≢ bN>a       = λ ()
N>→≢ cN>a       = λ ()
N>→≢ dN>a       = λ ()
N>→≢ eN>a       = λ ()
N>→≢ x′N>a      = λ ()
N>→≢ cN>b       = λ ()
N>→≢ dN>b       = λ ()
N>→≢ eN>b       = λ ()
N>→≢ x′N>b      = λ ()
N>→≢ dN>c       = λ ()
N>→≢ eN>c       = λ ()
N>→≢ x′N>c      = λ ()
N>→≢ eN>d       = λ ()
N>→≢ x′N>d      = λ ()
N>→≢ x′N>e      = λ ()
N>→≢ (x′N>y′ p) = N>→≢ p ∘ inj≡′

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
big→fresh {x} {∅}     {{tt}}       = tt
big→fresh {x} {ξ , y} {{xN>y , β}} = N>→≢ xN>y , big→fresh {{β}}

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

next : (x : NVar) → Σ NVar (λ z → z N> x)
next a     = b , bN>a
next b     = c , cN>b
next c     = d , dN>c
next d     = e , eN>d
next e     = {!!}
next (x ′) = {!!}

genbig : (ξ : NCtx) → Σ NVar (λ y → big y ξ)
genbig ∅       = a , tt
genbig (ξ , x) with genbig ξ
genbig (ξ , x) | y  , φ with x N⩼ y
genbig (ξ , x) | y , φ | yes xN>y = {!!}
genbig (ξ , x) | y , φ | no x₁ = {!!}

xN≯x : ∀ {x} → ¬ (x N> x)
xN≯x (x′N>y′ p) = p ↯ xN≯x

genbig′ : NVar → (ξ : NCtx) → Σ NVar (λ y → big y ξ)
genbig′ y₀ ∅       = y₀ , tt
genbig′ y₀ (ξ , x) with genbig′ y₀ ξ
genbig′ y₀ (ξ , x) | y  , φ with x N≟ y | x N⩼ y
genbig′ y₀ (ξ , x) | .x , φ | yes refl | yes xN>x = xN>x ↯ xN≯x
genbig′ y₀ (ξ , x) | .x , φ | yes refl | no xN≯x  = {!!}
genbig′ y₀ (ξ , x) | y  , φ | no x≢y   | yes xN>y = {!!}
genbig′ y₀ (ξ , x) | y  , φ | no x≢y   | no xN≯y  = y , ({!!} , {!!})

genfresh : (ξ : NCtx) → Σ NVar (λ y → fresh y ξ)
genfresh ∅       = a , tt
genfresh (ξ , x) with genfresh ξ
genfresh (ξ , x) | y  , φ with y N≟ x
genfresh (ξ , x) | .x , φ | yes refl = {!!}
genfresh (ξ , x) | y  , φ | no y≢x   = y , (y≢x , φ)

-- -- refresh : NVar → (ξ : NCtx) → Σ NVar (λ x′ → True (fresh x′ ξ))
-- -- refresh x ∅       = x , yes
-- -- refresh x (ξ , y) with refresh x ξ
-- -- refresh x (ξ , y) | x′ , φ with x′ N≟ y
-- -- refresh x (ξ , y) | .y , φ | yes refl = y ′ , {!!}
-- -- refresh x (ξ , y) | x′ , φ | no x′≢y  = {!!}

-- -- refreshN⊇ : ∀ x {ξ ξ′} → ξ′ N⊇ ξ → {{φ : True (fresh x ξ)}}
-- --                        → Σ NVar (λ x′ → True (fresh x′ ξ′))
-- -- refreshN⊇ x done {{φ}} = {!!}
-- -- refreshN⊇ x (step η x₂) {{φ}} = {!!}

-- -- refreshNS : ∀ x {ξ ζ} → NSub ξ ζ → {{φ : True (fresh x ζ)}}
-- --                       → Σ NVar (λ x′ → True (fresh x′ ξ))
-- -- refreshNS x {∅}               σ {{φ}} = x , yes
-- -- refreshNS x {ξ , y}           σ {{φ}} with x N≟ y
-- -- refreshNS x {(ξ , .x) {{φ′}}} σ {{φ}} | yes refl = {!!}
-- -- refreshNS x {ξ , y}           σ {{φ}} | no x≢y   = {!!}

-- -- renT : ∀ {ξ ξ′} → ξ′ N⊇ ξ → Type ξ
-- --                 → Type ξ′
-- -- renT η (M == N)  = renNE η M == renNE η N
-- -- renT η (~ A)     = ~ (renT η A)
-- -- renT η (A ∧ B)   = renT η A ∧ renT η B
-- -- renT η (A ⊃ B)   = renT η A ⊃ renT η B
-- -- renT η (∇_∶_ x {{φ}} A) = let x′ , φ′ = refreshN⊇ x η in
-- --                           ∇_∶_ x′ {{φ′}} (renT {!keepN⊇ η {{φ′}} !} A)

-- -- subT : ∀ {ξ ζ} → NSub ξ ζ → Type ζ
-- --                → Type ξ
-- -- subT σ (M == N)  = subNE σ M == subNE σ N
-- -- subT σ (~ A)     = ~ (subT σ A)
-- -- subT σ (A ∧ B)   = subT σ A ∧ subT σ B
-- -- subT σ (A ⊃ B)   = subT σ A ⊃ subT σ B
-- -- subT σ (∇ x ∶ A) = let y = {!!} in
-- --                    ∇_∶_ y {{{!!}}} (subT (keepNS σ {{{!!}}}) A)
