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
isContr→isContrPath (x0 , p) x y = (trans (sym (p x)) (p y) , λ {refl → lCancel (p x) } )

singl : {A : Type ℓ} → A → Type ℓ
singl {A = A} a = Σ A λ x → a ≡ x

isContrSingl : {A : Type ℓ} (x : A) → isContr (singl x)
isContrSingl x =  ( ((x , refl)) , λ (y , p) → Σ≡ p (trans (substInPathsR refl p) (lUnit p)))

--- Part 2

isProp : Type ℓ → Type ℓ
isProp A = (x y : A) → x ≡ y

isProp⊥ : isProp ⊥
isProp⊥ ()

isProp⊤ : isProp ⊤
isProp⊤ tt tt = refl

¬isPropBool : ¬ (isProp Bool)
¬isPropBool f = true≢false (f true false)

isContr→isProp : {A : Type ℓ} → isContr A → isProp A
isContr→isProp (x0 , p) x y = trans (sym (p x)) (p y)

isProp→isContr : {A : Type ℓ} → isProp A → A → isContr A
isProp→isContr f x = (x , λ y → f x y)

isContr→isProp' : {A : Type ℓ} → (A → isContr A) → isProp A
isContr→isProp' f x y = fst (isContr→isContrPath (f x) x y)

isProp→isContrPath : {A : Type ℓ} → isProp A → (x y : A) → isContr (x ≡ y)
isProp→isContrPath PA x y = isContr→isContrPath (isProp→isContr PA x) x y 

isProp' : Type ℓ → Type ℓ
isProp' A = (x y : A) → isContr (x ≡ y)

isProp'→isProp : (A : Type ℓ) → isProp' A → isProp A
isProp'→isProp A P x y = fst (P x y)

isProp→isProp' : {A : Type ℓ} → isProp A → isProp' A
isProp→isProp' P x y = isContr→isContrPath (isProp→isContr P x) x y

isPropIsContr : {A : Type ℓ} → isProp (isContr A)
isPropIsContr {A = A }(x , px) (y , py) = Σ≡ (px y) (funExt λ z → {!!} )
