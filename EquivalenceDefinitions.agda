{-# OPTIONS --without-K #-}

open import Prelude
open import Path
open import HLevels
open import Equivalence hiding (isPropIsEquiv ; equivEq)
open import FunExtPostulate

private variable
  ℓ ℓ' ℓ'' : Level

--- Part 1

isHAE : {A : Type ℓ} {B : Type ℓ'} (f : A → B) → Type (ℓ-max ℓ ℓ')
isHAE {A = A} {B} f = Σ (B → A) (λ g → Σ (g ∘ f ∼ id) λ η → Σ (f ∘ g ∼ id) λ ϵ → (x : A) → cong f (η x) ≡ ϵ (f x))

∼natural : {A : Type ℓ} {B : Type ℓ'} {f g : A → B} (α : f ∼ g) {x y : A} (p : x ≡ y) → α x ∙ cong g p ≡ cong f p ∙ α y
∼natural α {x = x} refl = trans (sym (rUnit (α x))) (lUnit (α x))

∼natural' : {A : Type ℓ} {f : A → A} (α : f ∼ id) (x : A) → α (f x) ≡ cong f (α x)
∼natural' {f = f} α x = 
  α (f x) ≡⟨ trans (rUnit (α (f x))) (cong (λ y → (α (f x)) ∙ y) (sym (rCancel (α x)))) ⟩
  α (f x) ∙ α x ∙ (sym (α x)) ≡⟨ sym (assoc (α (f x)) (α x) (sym (α x)) )⟩
  (α (f x) ∙ α x) ∙ (sym (α x)) ≡⟨ cong (λ z → z ∙ (sym (α x)) ) nat ⟩
  (cong f (α x) ∙ α x) ∙ (sym (α x)) ≡⟨ assoc (cong f (α x)) (α x) (sym (α x)) ⟩
  cong f (α x) ∙ α x ∙ (sym (α x)) ≡⟨ trans (cong (λ z → (cong f (α x)) ∙ z) (rCancel (α x))) (sym (rUnit (cong f (α x)))) ⟩
  cong f (α x) ∎

  where

  nat : α (f x) ∙ α x ≡ cong f (α x) ∙ α x
  nat =
    α (f x) ∙ α x ≡⟨ cong (λ z → α (f x) ∙ z) (sym (congId (α x))) ⟩
    α (f x) ∙ cong id (α x) ≡⟨ ∼natural α (α x) ⟩
    cong f (α x) ∙ α x ∎

hasQInv→isHAE : {A : Type ℓ} {B : Type ℓ'} (f : A → B) → hasQInv f → isHAE f
hasQInv→isHAE {A = A } f (g , η , ϵ) = g , (η , ϵ' , {!!})
  where

  ϵ' : (λ x → f (g x)) ∼ id
  ϵ' x = sym (ϵ (f (g x))) ∙ ( (cong f (η (g x))) ∙ ϵ x  )  

  p : (x : A) → cong f (η (g (f x))) ∙ ϵ (f x) ≡ ϵ (f (g (f x))) ∙ cong f (η x)
  p x =
    cong f (η (g (f x))) ∙ ϵ (f x) ≡⟨ cong (λ z → z ∙ ϵ (f x)) {!!} ⟩
    cong (f ∘ g ∘ f) (η x) ∙ (ϵ (f x)) ≡⟨ {!!} ⟩
    ϵ (f (g (f x))) ∙ cong f (η x) ∎
