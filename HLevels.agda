{-# OPTIONS --without-K #-}

open import Prelude
open import Path
open import FunExtPostulate

private variable
  ℓ ℓ' : Level

--- Part 1

isContr : Type ℓ → Type ℓ
isContr A = Σ A (λ x → (y : A) → x ≡ y)

isContr⊤ : isContr ⊤
isContr⊤ = tt , λ _ → refl

¬isContrBool : ¬ (isContr Bool)
¬isContrBool (false , f) = true≢false (sym (f true))
¬isContrBool (true , f) = true≢false (f false)

isContr× : {A : Type ℓ} {B : Type ℓ'} → isContr A → isContr B → isContr (A × B)
isContr× (a , fa) (b , fb) = (((a , b) ) , λ y → ×≡ (fa (fst y)) (fb (snd y)))

isContr→isContrPath : {A : Type ℓ} → isContr A → (x y : A) → isContr (x ≡ y)
isContr→isContrPath (a , fa) x y = (trans (sym (fa x)) (fa y) , λ { refl → lCancel (fa x) })

singl : {A : Type ℓ} → A → Type ℓ
singl {A = A} a = Σ A λ x → a ≡ x

isContrSingl : {A : Type ℓ} (a : A) → isContr (singl a)
isContrSingl a = (((a , refl) ) , λ { (_ , refl) → refl })



