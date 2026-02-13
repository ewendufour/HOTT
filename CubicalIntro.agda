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
transport p a = ?
