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
isPropIsContr {A = A }(x , px) (y , py) =
  Σ≡ (px y)
     (funExt λ z →  isContr→isProp (isContr→isContrPath ((y , py)) y z)
                                   (subst (λ x₁ → (y₁ : A) → x₁ ≡ y₁) (px y) px z)
                                   (py z))

isPropIsProp : {A : Type ℓ} → isProp (isProp A)
isPropIsProp P Q =
  funExt λ x →
    funExt λ y →
      isContr→isProp (isContr→isContrPath (isProp→isContr P x) x y)
                     (P x y) (Q x y)

isProp× : {A : Type ℓ} {B : Type ℓ'} → isProp A → isProp B → isProp (A × B)
isProp× P Q (a , b) (a' , b') = ×≡ (P a a') (Q b b')

isProp⊎ : {A : Type ℓ} {B : Type ℓ'} → isProp A → isProp B → (A → B → ⊥) → isProp (A ⊎ B)
isProp⊎ P Q f (inl a) (inl b) = cong (λ z → inl z) (P a b)
isProp⊎ P Q f (inl a) (inr b) = ⊥-rec (f a b)
isProp⊎ P Q f (inr a) (inl b) = ⊥-rec (f b a)
isProp⊎ P Q f (inr a) (inr b) = cong (λ z → inr z) (Q a b)

isProp→ : {A : Type ℓ} {B : Type ℓ'} → isProp B → isProp (A → B)
isProp→ P f g = funExt (λ z → P (f z) (g z))

isPropΠ : {A : Type ℓ} (B : A → Type ℓ') → ((x : A) → isProp (B x)) → isProp ((x : A) → B x)
isPropΠ B P f g = funExt (λ z → P z (f z) (g z))

isProp¬ : {A : Type ℓ} → isProp (¬ A)
isProp¬ f g = funExt (λ z → isProp⊥ (f z) (g z))

isPropΣ : {A : Type ℓ} (B : A → Type ℓ') → isProp A → ((x : A) → isProp (B x)) → isProp (Σ A B)
isPropΣ B P Q (a , b) (a' , b') = Σ≡ (P a a') (Q a' (subst B (P a a') b) b')

Dec : Type ℓ → Type ℓ
Dec A = A ⊎ ¬ A

isPropDec : {A : Type ℓ} → isProp A → isProp (Dec A)
isPropDec P (inl x) (inl y) = cong (λ z → inl z) (P x y)
isPropDec P (inl x) (inr f) = ⊥-rec (f x)
isPropDec P (inr g) (inl y) = ⊥-rec (g y)
isPropDec P (inr g) (inr f) = cong (λ z → inr z) (isProp→ isProp⊥ g f)

hProp : (ℓ : Level) → Type (ℓ-suc ℓ)
hProp ℓ = Σ (Type ℓ) isProp

_∧_ : hProp ℓ → hProp ℓ → hProp ℓ
_∧_ (P , PP)  (Q , QP) = (P × Q , isProp× PP QP )

sub : {A : Type ℓ} (P : A → hProp ℓ) → Type ℓ
sub {A = A} P = Σ A (fst ∘ P)

subInj : {A : Type ℓ} (P : A → hProp ℓ) {x y : sub P} → fst x ≡ fst y → x ≡ y
subInj P {x = x , Px} {y = y , Py} p = Σ≡ p (P y .snd (subst (λ z → fst (P z)) p Px) Py)

--- Part 3

isSet : Type ℓ → Type ℓ
isSet A = (x y : A) → isProp (x ≡ y)

isSet⊤ : isSet ⊤
isSet⊤ tt tt refl refl = refl

isSetBool : isSet Bool
isSetBool true true refl refl = refl
isSetBool false false refl refl = refl


isSetℕ : isSet ℕ
isSetℕ zero zero refl refl = refl
isSetℕ zero (suc n') () 
isSetℕ (suc n) zero ()
isSetℕ (suc n) (suc n') p q = {!!}
