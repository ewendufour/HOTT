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
lUnit {A = A} {x = x} p i j = hfill f (inS x) j
      where

      f : (k : I) → Partial (i ∨ ~ i ∨ j ∨ ~ j ) A
      f k (i = i0) = p (k ∧ j)
      f k (i = i1) = compPath-filler refl p k j
      f k (j = i0) = x
      f k (j = i1) = p k


rUnit : {A : Type ℓ} {x y : A} (p : x ≡ y) → p ≡ p ∙ refl
rUnit {x = x} p j i = hfill (compFaces p refl i) (inS (p i)) j

rCancel : {A : Type ℓ} {x y : A} (p : x ≡ y) → p ∙ sym p ≡ refl
rCancel p i j = hfill {!!} {!!} {!!}
