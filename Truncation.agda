{-# OPTIONS --without-K #-}

open import Prelude
open import Path
open import HLevels
open import FunExtPostulate

private variable
  ℓ ℓ' : Level

postulate
  ∥_∥₁ : Type ℓ → Type ℓ
  ∣_∣₁ : {A : Type ℓ} → A → ∥ A ∥₁
  isPropPropTrunc : {A : Type ℓ} → isProp ∥ A ∥₁
  propTrunc-rec : {A : Type ℓ} {B : Type ℓ'} → isProp B → (A → B) → (∥ A ∥₁ → B)
  propTrunc-beta : {A : Type ℓ} {B : Type ℓ'} (P : isProp B) (f : A → B) (x : A) → propTrunc-rec P f ∣ x ∣₁ ≡ f x

--- Part 7

_∨_ : hProp ℓ → hProp ℓ → hProp ℓ
(A , _) ∨ (B , _) = (∥ A ⊎ B ∥₁ , isPropPropTrunc)

∨-assocr : (A B C : hProp ℓ) → fst ((A ∨ B) ∨ C) → fst (A ∨ (B ∨ C))
∨-assocr A B C f = propTrunc-rec isPropPropTrunc
                   (λ { (inl f') → propTrunc-rec isPropPropTrunc
                                   (λ {(inl a) → ∣ inl a ∣₁ ;
                                       (inr b) → ∣ inr ∣ inl b ∣₁ ∣₁}) f' ;
                        (inr c ) → ∣ inr ∣ inr c ∣₁ ∣₁ }) f


propTrunc-map : {A : Type ℓ} {B : Type ℓ'} → (A → B) → ∥ A ∥₁ → ∥ B ∥₁
propTrunc-map f At = propTrunc-rec isPropPropTrunc (λ a → ∣ f a ∣₁) At 


propTrunc→¬¬ : {A : Type ℓ} → ∥ A ∥₁ → ¬ ¬ A
propTrunc→¬¬ At f = propTrunc-rec isProp⊥ f At

PT : Type ℓ → (ℓ' : Level) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
PT A ℓ' = (B : Type ℓ') → isProp B → (A → B) → B


inclPT : {A : Type ℓ} → A → PT A ℓ'
inclPT a B BP f = f a

isPropPT : (A : Type ℓ) → isProp (PT A ℓ)
isPropPT A p q = funExt (λ B → funExt (λ pB → funExt (λ f → pB (p B pB f) (q B pB f)))) 

PTtrunc : (A : Type ℓ) → PT A ℓ ↔ ∥ A ∥₁
PTtrunc A = ( (λ Apt → Apt ∥ A ∥₁ isPropPropTrunc (λ x → ∣ x ∣₁) ) , λ At → propTrunc-rec (isPropPT A) inclPT At )

isConnected : (A : Type ℓ) → Type ℓ
isConnected A = ∥ A ∥₁ × ((x y : A) → ∥ x ≡ y ∥₁)

comp : {A : Type ℓ} → A → Type ℓ
comp {A = A} a = Σ A λ x → ∥ a ≡ x ∥₁

isConnectedComp : {A : Type ℓ} (x : A) → isConnected (comp x)
isConnectedComp x = (∣ (x , ∣ refl ∣₁) ∣₁ ,
                       λ y z → propTrunc-rec isPropPropTrunc
                         (λ p → propTrunc-rec isPropPropTrunc
                           (λ q → ∣ Σ≡ (sym p ∙ q)
                             (isPropPropTrunc (subst (λ v → ∥ x ≡ v ∥₁)
                               (sym p ∙ q) (y .snd)) (z .snd)) ∣₁) (z .snd)) (y .snd ))


postulate
  ∥_∥₂ : Type ℓ → Type ℓ
  ∣_∣₂ : {A : Type ℓ} → A → ∥ A ∥₂
  isSetSetTrunc : {A : Type ℓ} → isSet ∥ A ∥₂
  setTrunc-elim : {A : Type ℓ} (B : ∥ A ∥₂ → Type ℓ') → ((x : A) → isSet (B ∣ x ∣₂)) → ((x : A) → B ∣ x ∣₂) → ((x : ∥ A ∥₂) → B x)
  setTrunc-beta : {A : Type ℓ} (B : ∥ A ∥₂ → Type ℓ') (set : (x : A) → isSet (B ∣ x ∣₂)) (f : (x : A) → B ∣ x ∣₂) (x : A) → setTrunc-elim B set f ∣ x ∣₂ ≡ f x


setTrunc-rec : {A : Type ℓ} {B : Type ℓ'} → isSet B → (A → B) → (∥ A ∥₂ → B)
setTrunc-rec {B = B} sB f = setTrunc-elim (λ _ → B) (λ _ → sB) f

setTrunc-map : {A : Type ℓ} {B : Type ℓ'} → (A → B) → (∥ A ∥₂ → ∥ B ∥₂)
setTrunc-map f a = setTrunc-rec isSetSetTrunc (λ a → ∣ f a ∣₂) a



