module TNT3 where

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

injN′ : ∀ {x₁ x₂} → x₁ ′ ≡ x₂ ′ → x₁ ≡ x₂
injN′ refl = refl

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
...          | no x₁≢x₂ = no (x₁≢x₂ ∘ injN′)

infix 5 _N>_
_N>_ : NVar → NVar → Bool
a    N> a    = false
a    N> b    = false
a    N> c    = false
a    N> d    = false
a    N> e    = false
a    N> x₂ ′ = false
b    N> a    = true
b    N> b    = false
b    N> c    = false
b    N> d    = false
b    N> e    = false
b    N> x₂ ′ = false
c    N> a    = true
c    N> b    = true
c    N> c    = false
c    N> d    = false
c    N> e    = false
c    N> x₂ ′ = false
d    N> a    = true
d    N> b    = true
d    N> c    = true
d    N> d    = false
d    N> e    = false
d    N> x₂ ′ = false
e    N> a    = true
e    N> b    = true
e    N> c    = true
e    N> d    = true
e    N> e    = false
e    N> x₂ ′ = false
x₁ ′ N> a    = true
x₁ ′ N> b    = true
x₁ ′ N> c    = true
x₁ ′ N> d    = true
x₁ ′ N> e    = true
x₁ ′ N> x₂ ′ = x₁ N> x₂


mutual
  data NCtx : Set
    where
      ∅ : NCtx

      _,_ : ∀ ξ x → {{φ : True (fresh x ξ)}}
                  → NCtx

  fresh : NVar → NCtx → Bool
  fresh x ∅       = true
  fresh x (ξ , y) = not ⌊ x N≟ y ⌋ and fresh x ξ

infix 4 _N∋_
data _N∋_ : NCtx → NVar → Set
  where
    instance
      zero : ∀ {ξ x} → {{φ : True (fresh x ξ)}}
                     → ξ , x N∋ x

      suc : ∀ {ξ x y} → {{φ : True (fresh y ξ)}} → ξ N∋ x
                      → ξ , y N∋ x

_N∌_ : NCtx → NVar → Set
ξ N∌ x = ¬ (ξ N∋ x)

fresh→N∌ : ∀ {x ξ} → {{φ : True (fresh x ξ)}}
                    → ξ N∌ x
fresh→N∌ {x} {{φ}}  zero             with x N≟ x
fresh→N∌ {x} {{()}} zero             | yes refl
fresh→N∌ {x} {{φ}}  zero             | no x≢x   = refl ↯ x≢x
fresh→N∌ {x} {{φ}}  (suc {y = y} i)  with x N≟ y
fresh→N∌ {x} {{()}} (suc {y = .x} i) | yes refl
fresh→N∌ {x} {{φ}}  (suc {y = y} i)  | no x≢y   = i ↯ fresh→N∌

infix 4 _N⊇_
data _N⊇_ : NCtx → NCtx → Set
  where
    done : ∀ {ξ} → ξ N⊇ ∅

    step : ∀ {ξ ξ′ x} → {{φ : True (fresh x ξ)}} → ξ′ N⊇ ξ → ξ′ N∋ x
                      → ξ′ N⊇ ξ , x

extN⊇ : ∀ {ξ ξ′} → (∀ {x} → ξ N∋ x → ξ′ N∋ x)
                 → ξ′ N⊇ ξ
extN⊇ {∅}     f = done
extN⊇ {ξ , x} f = step (extN⊇ (λ i → f (suc i))) (f zero)

renN∋ : ∀ {ξ ξ′ x} → ξ′ N⊇ ξ → ξ N∋ x
                   → ξ′ N∋ x
renN∋ done       ()
renN∋ (step η j) zero    = j
renN∋ (step η j) (suc i) = renN∋ η i

reflN⊇ : ∀ {ξ} → ξ N⊇ ξ
reflN⊇ = extN⊇ id

transN⊇ : ∀ {ξ ξ′ ξ″} → ξ″ N⊇ ξ′ → ξ′ N⊇ ξ → ξ″ N⊇ ξ
transN⊇ η₁ η₂ = extN⊇ (λ i → renN∋ η₁ (renN∋ η₂ i))

dropN⊇ : ∀ {x ξ ζ} → ξ N⊇ ζ → {{φ : True (fresh x ξ)}}
                   → ξ , x N⊇ ζ
dropN⊇ η = transN⊇ (extN⊇ suc) η

keepN⊇ : ∀ {x ξ ζ} → ξ N⊇ ζ → {{φ₁ : True (fresh x ξ)}} {{φ₂ : True (fresh x ζ)}}
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

    _,_ : ∀ {ξ ζ x} → NSub ξ ζ → NExp ξ → {{φ : True (fresh x ζ)}}
                    → NSub ξ (ζ , x)

renNS : ∀ {ζ ξ ξ′} → ξ′ N⊇ ξ → NSub ξ ζ
                   → NSub ξ′ ζ
renNS {∅}     η ∅       = ∅
renNS {ζ , x} η (σ , M) = renNS η σ , renNE η M

dropNS : ∀ {x ξ ζ} → NSub ξ ζ → {{φ : True (fresh x ξ)}}
                   → NSub (ξ , x) ζ
dropNS σ = renNS (dropN⊇ reflN⊇) σ

keepNS : ∀ {x y ξ ζ} → NSub ξ ζ → {{φ₁ : True (fresh x ξ)}} {{φ₂ : True (fresh y ζ)}}
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

    ∇_∶_ : ∀ {ξ} → (x : NVar) {{φ : True (fresh x ξ)}} → Type (ξ , x)
                 → Type ξ


freshup : ∀ {x y ξ} → y ≢ x → {{φ : True (fresh y ξ)}}
                    → True (not ⌊ y N≟ x ⌋ and fresh y ξ)
freshup {x} {y}  x≢y {{φ}} with x N≟ y
freshup {x} {.x} x≢y {{φ}} | yes refl = refl ↯ x≢y
freshup {x} {y}  x≢y {{φ}} | no x≢y′  = {!!}

gensym : (ξ : NCtx) → Σ NVar (λ x → True (fresh x ξ))
gensym ∅       = a , yes
gensym (ξ , x) with gensym ξ
gensym (ξ , x) | y  , φ with y N≟ x
gensym (ξ , x) | .x , φ | yes refl = {!!}
gensym (ξ , x) | y  , φ | no y≢x   = y , {!!}


refresh : NVar → (ξ : NCtx) → Σ NVar (λ x′ → True (fresh x′ ξ))
refresh x ∅       = x , yes
refresh x (ξ , y) with refresh x ξ
refresh x (ξ , a) | a , φ = {!!}
refresh x (ξ , a) | b , φ = {!!}
refresh x (ξ , a) | c , φ = {!!}
refresh x (ξ , a) | d , φ = {!!}
refresh x (ξ , a) | e , φ = {!!}
refresh x (ξ , a) | (x′ ′) , φ = {!!}
refresh x (ξ , b) | a , φ = {!!}
refresh x (ξ , b) | b , φ = {!!}
refresh x (ξ , b) | c , φ = {!!}
refresh x (ξ , b) | d , φ = {!!}
refresh x (ξ , b) | e , φ = {!!}
refresh x (ξ , b) | (x′ ′) , φ = {!!}
refresh x (ξ , c) | a , φ = {!!}
refresh x (ξ , c) | b , φ = {!!}
refresh x (ξ , c) | c , φ = {!!}
refresh x (ξ , c) | d , φ = {!!}
refresh x (ξ , c) | e , φ = {!!}
refresh x (ξ , c) | (x′ ′) , φ = {!!}
refresh x (ξ , d) | a , φ = {!!}
refresh x (ξ , d) | b , φ = {!!}
refresh x (ξ , d) | c , φ = {!!}
refresh x (ξ , d) | d , φ = {!!}
refresh x (ξ , d) | e , φ = {!!}
refresh x (ξ , d) | (x′ ′) , φ = {!!}
refresh x (ξ , e) | a , φ = {!!}
refresh x (ξ , e) | b , φ = {!!}
refresh x (ξ , e) | c , φ = {!!}
refresh x (ξ , e) | d , φ = {!!}
refresh x (ξ , e) | e , φ = {!!}
refresh x (ξ , e) | (x′ ′) , φ = {!!}
refresh x (ξ , (y ′)) | a , φ = {!!}
refresh x (ξ , (y ′)) | b , φ = {!!}
refresh x (ξ , (y ′)) | c , φ = {!!}
refresh x (ξ , (y ′)) | d , φ = {!!}
refresh x (ξ , (y ′)) | e , φ = {!!}
refresh x (ξ , (y ′)) | (x′ ′) , φ = {!!}

refreshN⊇ : ∀ x {ξ ξ′} → ξ′ N⊇ ξ → {{φ : True (fresh x ξ)}}
                       → Σ NVar (λ x′ → True (fresh x′ ξ′))
refreshN⊇ x done {{φ}} = {!!}
refreshN⊇ x (step η x₂) {{φ}} = {!!}

refreshNS : ∀ x {ξ ζ} → NSub ξ ζ → {{φ : True (fresh x ζ)}}
                      → Σ NVar (λ x′ → True (fresh x′ ξ))
refreshNS x {∅}               σ {{φ}} = x , yes
refreshNS x {ξ , y}           σ {{φ}} with x N≟ y
refreshNS x {(ξ , .x) {{φ′}}} σ {{φ}} | yes refl = {!!}
refreshNS x {ξ , y}           σ {{φ}} | no x≢y   = {!!}

renT : ∀ {ξ ξ′} → ξ′ N⊇ ξ → Type ξ
                → Type ξ′
renT η (M == N)  = renNE η M == renNE η N
renT η (~ A)     = ~ (renT η A)
renT η (A ∧ B)   = renT η A ∧ renT η B
renT η (A ⊃ B)   = renT η A ⊃ renT η B
renT η (∇_∶_ x {{φ}} A) = let x′ , φ′ = refreshN⊇ x η in
                          ∇_∶_ x′ {{φ′}} (renT {!keepN⊇ η {{φ′}} !} A)

subT : ∀ {ξ ζ} → NSub ξ ζ → Type ζ
               → Type ξ
subT σ (M == N)  = subNE σ M == subNE σ N
subT σ (~ A)     = ~ (subT σ A)
subT σ (A ∧ B)   = subT σ A ∧ subT σ B
subT σ (A ⊃ B)   = subT σ A ⊃ subT σ B
subT σ (∇ x ∶ A) = let y = {!!} in
                   ∇_∶_ y {{{!!}}} (subT (keepNS σ {{{!!}}}) A)
