{-# OPTIONS --without-K #-}

open import Prelude
open import Path
open import HLevels
open import Equivalence

private variable
  ℓ ℓ' : Level

--- Part 1

pathToEquiv : {A B : Type ℓ} → A ≡ B → A ≃ B
pathToEquiv {A = A} {B = B} refl = isoToEquiv (transport refl , (transport refl) , (invl , invr))
  where

  invl : transport refl ∘ transport refl ∼ id
  invl x = refl

  invr : transport refl ∘ transport refl ∼ id
  invr x = refl


pathToEquivTest : {A B : Type ℓ} (p : A ≡ B) → equivFun (pathToEquiv p) ≡ transport p
pathToEquivTest refl = refl

postulate
  -- Univalence!
  isEquivPathToEquiv : {A B : Type ℓ} → isEquiv (pathToEquiv {A = A} {B = B})

univalence : {A B : Type ℓ} → (A ≡ B) ≃ (A ≃ B)
univalence = pathToEquiv , isEquivPathToEquiv

ua : {A B : Type ℓ} → A ≃ B → A ≡ B
ua eqAB = invEq univalence eqAB

uaβ : {A B : Type ℓ} (e : A ≃ B) → transport (ua e) ≡ equivFun e
uaβ e = trans (sym (pathToEquivTest (ua e))) (cong fst lemma)
  where
    lemma : pathToEquiv (ua e) ≡ e 
    lemma =
      pathToEquiv (ua e) ≡⟨ secEq univalence e ⟩
      id e ≡⟨ refl ⟩
      e ∎

uaη : {A B : Type ℓ} (p : A ≡ B) → ua (pathToEquiv p) ≡ p
uaη p = retEq univalence p

uaIdEquiv : {A : Type ℓ} → ua (idEquiv {A = A}) ≡ refl
uaIdEquiv = uaη refl


--- Part 2

isContr≃≡⊤ : {A : Type} → isContr A ≃ (A ≡ ⊤)
isContr≃≡⊤ = compEquiv isContr≃≃⊤ (invEquiv univalence)

is¬≃≡⊥ : {A : Type} → (¬ A) ≃ (A ≡ ⊥)
is¬≃≡⊥ = compEquiv {!!} (invEquiv univalence)

--- Part 3

≃ind : (P : {A B : Type ℓ} → (A ≃ B) → Type ℓ') →
       ({A : Type ℓ} → P (idEquiv {A = A})) →
       {A B : Type ℓ} (e : A ≃ B) → P e
≃ind P Pi e = {!!}
