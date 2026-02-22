{-# OPTIONS --cubical #-}

open import CubicalPrelude

private variable
  ℓ ℓ' ℓ'' : Level

--- Part 1

refl : {A : Type ℓ} {x : A} → x ≡ x
refl {x = x} i = x

sym : {A : Type ℓ} {x y : A} → x ≡ y → y ≡ x
sym p i = p (~ i)

symInvo : {A : Type ℓ} {x y : A} (p : x ≡ y) → sym (sym p) ≡ p
symInvo p i = p

symRefl : {A : Type ℓ} {x : A} → sym (refl {x = x}) ≡ refl
symRefl = refl

cong : {A : Type ℓ} {B : A → Type ℓ'} (f : (a : A) → B a) {x y : A} (p : x ≡ y) → PathP (λ i → B (p i)) (f x) (f y)
cong f p i = f (p i)

--- Part 2

transport : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → A → B
transport p a = transp (λ i → p i) i0 a

transportRefl : ∀ {ℓ} {A : Set ℓ} (x : A) → transport (λ _ → A) x ≡ x
transportRefl {A = A} x i = transp (λ _ → A) i x

J : {A : Type ℓ} {x : A} (P : ∀ y → x ≡ y → Type ℓ) (r : P x refl) {y : A} (p : x ≡ y) → P y p
J P r p = transport (λ i → P (p i) (λ j → p (i ∧ j))) r


--- Part 3

partialBool : (i : I) → Partial (~ i ∨ i) Bool
partialBool i (i = i0) = false
partialBool i (i = i1) = true

infixr 30 _∙_
_∙_ : {A : Type ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z


compFaces : {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) (i j : I) → Partial (i ∨ ~ i) A
compFaces {x = x} p q i j (i = i0) = x
compFaces p q i j (i = i1)  = q j

_∙_ p q i = hcomp (compFaces p q i) (p i)

compPath-filler : {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) → PathP (λ j → x ≡ q j) p (p ∙ q)
compPath-filler p q j i = hfill (compFaces p q i) (inS (p i)) j

module _ {A : Type ℓ} where
  infixr 2 step-≡ _≡⟨⟩_
  infix  3 _∎

  step-≡ : (x : A) {y z : A} → y ≡ z → x ≡ y → x ≡ z
  step-≡ _ q p = p ∙ q

  syntax step-≡ x y p = x ≡⟨ p ⟩ y

  _≡⟨⟩_ : (x : A) {y : A} → x ≡ y → x ≡ y
  _ ≡⟨⟩ p = p

  _∎ : (x : A) → x ≡ x
  _ ∎ = refl

lUnit : {A : Type ℓ} {x y : A} (p : x ≡ y) → p ≡ refl ∙ p
lUnit {A = A} {x = x} p k i = f i i1 k
  where
  u : (i k : I) → (j : I) → Partial (i ∨ ~ i ∨ k ∨ ~ k) A
  u i k j (i = i0) = x
  u i k j (i = i1) = (sym p) (k ∧ ~ j)
  u i k j (k = i0) = p i
  u i k j (k = i1) = compPath-filler refl p j i

  f : (i j k : I) → A
  f i j k = hfill (u i k) (inS (p (i ∧ ~ k))) j


rUnit : {A : Type ℓ} {x y : A} (p : x ≡ y) → p ≡ p ∙ refl
rUnit {x = x} p j i = hfill (compFaces p refl i) (inS (p i)) j

rCancel : {A : Type ℓ} {x y : A} (p : x ≡ y) → p ∙ sym p ≡ refl
rCancel {A = A} {x = x} p k i = {!f i i1 k  !}
  where
  
  u : (i k : I) → (j : I) → Partial (i ∨ ~ i ∨ k ∨ ~ k) A
  u i k j (i = i0) = x
  u i k j (i = i1) = (sym p) j 
  u i k j (k = i0) = p (i ∧ ~ j)
  u i k j (k = i1) = compPath-filler p (sym p) j i

  f : (i j k : I) → A
  f i j k = hfill (u i k) (inS (p i)) j
  
cong-∙ : {A : Type ℓ} {B : Type ℓ'} (f : A → B) {x y z : A} (p : x ≡ y) (q : y ≡ z) → cong f (p ∙ q) ≡ (cong f p) ∙ (cong f q)
cong-∙ f p q i j = {!!}

--- Part 4

data Interval : Type where
  Is : Interval
  It : Interval
  Ip : Is ≡ It


Interval≃1 : Interval ≃ Unit
Interval≃1 = isoToEquiv (iso f g η ϵ)
  where

  f : Interval → Unit
  f _ = tt

  g : Unit → Interval
  g tt = Is

  η : g ∘ f ∼ id
  η Is j = Is 
  η It j = Ip j
  η (Ip i) j = Ip (j ∧ i)

  ϵ : f ∘ g ∼ id
  ϵ tt k = tt


--- Part 5

data Circle : Type where
  base : Circle
  loop : base ≡ base


data Torus : Type where
  point : Torus
  loop1 : point ≡ point
  loop2 : point ≡ point
  square : PathP (λ i → loop1 i ≡ loop1 i) loop2 loop2

C²≃T : Circle × Circle ≃ Torus
C²≃T = isoToEquiv (iso f g η ϵ)
  where

  f : Circle × Circle → Torus
  f (base , base) = point
  f (base , loop i) = loop2 i
  f (loop i , base) = loop1 i
  f (loop i , loop j) = square i j

  g : Torus → Circle × Circle
  g point = base , base
  g (loop1 i) = (loop i) , base
  g (loop2 i) = base , loop i
  g (square i j) = (loop i) , (loop j)

  η : g ∘ f ∼ id
  η (base , base) k = base , base
  η (base , loop i) k = base , (loop i)
  η (loop i , base) k = (loop i) , base
  η (loop i , loop j) k = (loop i) , (loop j)

  ϵ : f ∘ g ∼ id
  ϵ point k = point
  ϵ (loop1 i) k = loop1 i
  ϵ (loop2 i) k = loop2 i
  ϵ (square i j) k = square i j

data Circle' : Type where
  base1 : Circle'
  base2 : Circle'
  path1 : base1 ≡ base2
  path2 : base1 ≡ base2

C≃C' : Circle ≃ Circle'
C≃C' = isoToEquiv (iso f g η ϵ)
  where

  f : Circle → Circle'
  f base = base1
  f (loop i) = {!!}

  g : Circle' → Circle
  g base1 = base
  g base2 = base
  g (path1 i) = loop i
  g (path2 i) = loop i

  η : g ∘ f ∼ id
  η base k = loop k
  η (loop i) k = {!!}

  ϵ : f ∘ g ∼ id
  ϵ base1 k = base1
  ϵ base2 k = path1 k
  ϵ (path1 i) k = path1 (i ∧ k)
  ϵ (path2 i) k = {!!}
