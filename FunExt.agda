{-# OPTIONS --without-K #-}

open import Prelude
open import Path
open import HLevels
open import Equivalence
open import Univalence

private variable
  ℓ ℓ' ℓ'' : Level


--- Part 1


lComp : {A : Type ℓ} {B : Type ℓ'} (f : A → B) → id ∘ f ≡ f
lComp f = refl

rComp : {A : Type ℓ} {B : Type ℓ'} (f : A → B) → f ∘ id ≡ f
rComp f = refl


--- Part 2

Path : (A : Type ℓ) → Type ℓ
Path A = Σ A λ x → Σ A λ y → x ≡ y

PathSrc : {A : Type ℓ} → Path A → A
PathSrc (x , p) = x

PathCst : {A : Type ℓ} → A → Path A
PathCst x = x , (x , refl)


Homotopy : (A : Type ℓ) (B : Type ℓ') → Type (ℓ-max ℓ ℓ')
Homotopy A B = Σ (A → B) λ f → Σ (A → B) λ g → f ∼ g

Homotopy' : (A : Type ℓ) (B : Type ℓ') → Type (ℓ-max ℓ ℓ')
Homotopy' A B = A → Path B

Homotopy≃Homotopy' : (A : Type ℓ) (B : Type ℓ') → Homotopy A B ≃ Homotopy' A B
Homotopy≃Homotopy' A B  = isoToEquiv (f , (g , (linv , rinv)))
  where

  f : Homotopy A B → Homotopy' A B
  f (f , g , h) a = f a , (g a) , (h a)

  g : Homotopy' A B → Homotopy A B
  g h = (λ a → PathSrc (h a)) , ((λ a → fst (snd (h a))) , λ a → (h a) .snd .snd)

  linv : g ∘ f ∼ id
  linv x = refl

  rinv : f ∘ g ∼ id
  rinv x = refl




PathContract : (A : Type ℓ) → Path A ≃ A
PathContract A = isoToEquiv (PathSrc , (PathCst , (linv , λ x → refl)))
  where

  linv : (PathCst ∘ PathSrc) ∼ id
  linv (x , x' , refl) = refl

PathContractTest : (A : Type ℓ) → equivFun (PathContract A) ≡ PathSrc
PathContractTest A = refl


equiv→R : {A : Type ℓ} {B B' : Type ℓ'} → B ≃ B' → (A → B) ≃ (A → B')
equiv→R {A = A} {B = B} {B' = B'} e = isoToEquiv (f , (g , ({!!} , {!!})))
  where

  f : (A → B) → A → B'
  f h = equivFun e ∘ h

  g : (A → B') → A → B
  g h = invEq e ∘ h

equiv→RTest : {A : Type ℓ} {B B' : Type ℓ'} (e : B ≃ B') (f : A → B) → equivFun (equiv→R e) f ≡ equivFun e ∘ f
equiv→RTest e f = refl

Homotopy≃Path : (A : Type ℓ) (B : Type ℓ') → Homotopy A B ≃ Path (A → B)
Homotopy≃Path A B = {!!}

≃Injective : {A : Type ℓ} {B : Type ℓ'} (e : A ≃ B) {x y : A} → equivFun e x ≡ equivFun e y → x ≡ y
≃Injective e p = {!!}


funExtND : {A : Type ℓ} {B : Type ℓ'} {f g : A → B} → ((x : A) → f x ≡ g x) → f ≡ g
funExtND fsg = {!!}


--- Part 3

isContr→ : {A : Type ℓ} {B : Type ℓ'} → isContr B → isContr (A → B)
isContr→ (b , f) = (λ a → b) , (λ g → funExtND (λ x → f (g x)))

funExtW : {A : Type ℓ} {B : A → Type ℓ'} → ((x : A) → isContr (B x)) → isContr ((x : A) → B x)
funExtW f = {!!}

funExt : {A : Type ℓ} {B : A → Type ℓ'} {f g : (x : A) → B x} → ((x : A) → f x ≡ g x) → f ≡ g
funExt fsg = {!!}


--- Part 5

postulate
  funExtEquiv : {A : Type ℓ} {B : A → Type ℓ'} {f g : (x : A) → B x} → ((x : A) → f x ≡ g x) ≃ (f ≡ g)

isPropRespectEquiv : {A : Type ℓ} {B : Type ℓ'} (e : A ≃ B) → isProp A → isProp B
isPropRespectEquiv e = {!!}

isSet→ : {A : Type ℓ} {B : Type ℓ'} → isSet B → isSet (A → B)
isSet→ sB = {!!}
