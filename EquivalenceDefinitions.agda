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
hasQInv→isHAE {A = A} f (g , η , ϵ) = g , (η , ϵ' , τ)
  where

  ϵ' : (λ x → f (g x)) ∼ id
  ϵ' x = sym (ϵ (f (g x))) ∙ ( (cong f (η (g x))) ∙ ϵ x)

  p' : (x : A) → cong f (η (g (f x))) ≡ cong (f ∘ g ∘ f) (η x)
  p' x =
    cong f (η (g (f x))) ≡⟨ cong (λ z → cong f z) (∼natural' η x) ⟩
    cong f (cong (λ z → g (f z)) (η x)) ≡⟨ sym (cong∘ (g ∘ f) f (η x)) ⟩
    cong (f ∘ g ∘ f) (η x) ∎

  p'' : (x : A) → ϵ ((f ∘ g ∘ f) x) ∙ cong f (η x) ≡ cong (f ∘ g ∘ f) (η x) ∙ ϵ (f x)
  p'' x =
    ϵ ((f ∘ g ∘ f) x) ∙ cong f (η x) ≡⟨ cong (λ z → (ϵ ∘ f ∘ g ∘ f ) x ∙ z) (sym (congId (cong f (η x)))) ⟩
    ϵ (f (g (f x))) ∙ cong id (cong f (η x)) ≡⟨ ∼natural ϵ {x = (f ∘ g ∘ f) x} {y = (f x)} (cong f (η x)) ⟩
    cong (λ z → f (g z)) (cong f (η x)) ∙ ϵ (f x) ≡⟨ cong (λ z → z ∙ ϵ (f x)) (sym (cong∘ f (f ∘ g) (η x)))  ⟩
    cong (f ∘ g ∘ f) (η x) ∙ ϵ (f x) ∎

  p : (x : A) → cong f (η (g (f x))) ∙ ϵ (f x) ≡ ϵ (f (g (f x))) ∙ cong f (η x)
  p x =
    cong f (η (g (f x))) ∙ ϵ (f x) ≡⟨ cong (λ z → z ∙ ϵ (f x)) (p' x) ⟩
    cong (f ∘ g ∘ f) (η x) ∙ (ϵ (f x)) ≡⟨ sym (p'' x) ⟩
    ϵ (f (g (f x))) ∙ cong f (η x) ∎

  τ : (x : A) → cong f (η x) ≡ ϵ' (f x)
  τ x =
    cong f (η x) ≡⟨ sym (rotate∙≡ ((ϵ ∘ f ∘ g ∘ f ) x) (cong f (η x)) (cong f (η (g (f x))) ∙ ϵ (f x)) (sym (p x))) ⟩
    ϵ' (f x) ∎


--- Part 2

fiber : {A : Type ℓ} {B : Type ℓ'} → (A → B) → B → Type (ℓ-max ℓ ℓ')
fiber {A = A} f y = Σ A (λ x → f x ≡ y)

hasContrFibers : {A : Type ℓ} {B : Type ℓ'} (f : A → B) → Type (ℓ-max ℓ ℓ')
hasContrFibers {B = B} f = (y : B) → isContr (fiber f y)

symDist : {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) → sym (p ∙ q) ≡ sym q ∙ sym p
symDist refl refl = refl

isHAE→hasContrFibers : {A : Type ℓ} {B : Type ℓ'} (f : A → B) → isHAE f → hasContrFibers f
isHAE→hasContrFibers f (g , η , ϵ , τ ) y = ((g y) , (ϵ y)) , ftp
  where

  ftp : (x : fiber f y) → (g y , ϵ y) ≡ x
  ftp (x , p) = Σ≡ (cong g (sym p) ∙ (η x)) pbp
    where

    pbp : PathOver (λ v → f v ≡ y) (cong g (sym p) ∙ η x) (ϵ y) p
    pbp =
      subst (λ v → f v ≡ y) (cong g (sym p) ∙ η x) (ϵ y) ≡⟨ substInPaths f (λ _ → y) (cong g (sym p) ∙ (η x)) (ϵ y) ⟩
      sym (cong f (cong g (sym p) ∙ η x)) ∙ ϵ y ∙ cong (λ _ → y) (cong g (sym p) ∙ η x) ≡⟨ cong (λ z → sym (cong f (cong g (sym p) ∙ η x)) ∙ z) (cong (λ z → ϵ y ∙ z) (congConst ((cong g (sym p)) ∙ (η x)))) ⟩
      sym (cong f (cong g (sym p) ∙ η x)) ∙ ϵ y ∙ refl ≡⟨ sym (assoc (sym (cong f (trans (cong g (sym p)) (η x)))) (ϵ y) refl) ⟩
      (sym (cong f (cong g (sym p) ∙ η x)) ∙ ϵ y) ∙ refl ≡⟨ sym (rUnit (sym (cong f (cong g (sym p) ∙ η x)) ∙ ϵ y)) ⟩
      sym (cong f (cong g (sym p) ∙ η x)) ∙ ϵ y ≡⟨ cong (λ z → (sym z) ∙ ϵ y) ( congComposite f (cong g (sym p)) (η x)) ⟩
      sym (cong f (cong g (sym p)) ∙ cong f (η x)) ∙ ϵ y ≡⟨ cong (λ z → sym (z ∙ cong f (η x)) ∙ ϵ y) (sym (cong∘ g f (sym p))) ⟩
      sym (cong (f ∘ g) (sym p) ∙ cong f (η x)) ∙ ϵ y ≡⟨ cong (λ z → sym (z ∙ (cong f (η x))) ∙ ϵ y) (congSym (f ∘ g) p) ⟩
      sym (sym (cong (f ∘ g) p) ∙ cong f (η x)) ∙ ϵ y ≡⟨ cong (λ z → z ∙ ϵ y) (symDist (sym (cong (f ∘ g) p)) (cong f (η x))) ⟩
      (sym (cong f (η x)) ∙ sym (sym (cong (f ∘ g) p))) ∙ ϵ y ≡⟨ cong (λ z → (sym (cong f (η x)) ∙ z) ∙ ϵ y) (sym (symInvo (cong (f ∘ g) p))) ⟩
      (sym (cong f (η x)) ∙ cong (f ∘ g) p) ∙ ϵ y ≡⟨ assoc (sym (cong f (η x))) (cong (f ∘ g) p) (ϵ y) ⟩
      sym (cong f (η x)) ∙ cong (f ∘ g) p ∙ ϵ y ≡⟨ cong (λ z → sym (cong f (η x)) ∙ z) (sym (∼natural ϵ p)) ⟩
      sym (cong f (η x)) ∙ ϵ (f x) ∙ cong id p ≡⟨ cong (λ z → sym (cong f (η x)) ∙ ϵ (f x) ∙ z) (congId p) ⟩
      sym (cong f (η x)) ∙ ϵ (f x) ∙ p  ≡⟨ cong (λ z → (sym z) ∙ ϵ (f x) ∙ p) (τ x) ⟩
      sym (ϵ (f x)) ∙ (ϵ (f x)) ∙ p ≡⟨ sym (assoc (sym (ϵ (f x))) (ϵ (f x)) p) ⟩
      (sym (ϵ (f x)) ∙ (ϵ (f x))) ∙ p ≡⟨ cong (λ z → z ∙ p) (lCancel (ϵ (f x))) ⟩
      refl ∙ p ≡⟨ lUnit p ⟩
      p ∎


isEquiv→hasContrFibers : {A : Type ℓ} {B : Type ℓ'} (e : A ≃ B) → hasContrFibers (equivFun e)
isEquiv→hasContrFibers e = isHAE→hasContrFibers (equivFun e) (hasQInv→isHAE (equivFun e) (isEquiv→hasQInv (equivFun e) (e .snd)))

hasContrFibers→isEquiv : {A : Type ℓ} {B : Type ℓ'} (f : A → B) → hasContrFibers f → isEquiv f
hasContrFibers→isEquiv {A = A} {B = B} f hcff = hasQInv→isEquiv f (g , (η , ϵ))
  where

  g : B → A
  g y = hcff y .fst .fst

  ϵ : f ∘ g ∼ id
  ϵ y = hcff y .fst .snd

  η : g ∘ f ∼ id
  η y = cong fst ((hcff (f y) .snd) (y , refl))  



--- Part 3

precomp≃ : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} (e : A ≃ B) → (B → C) ≃ (A → C)
precomp≃ {A = A} {B = B} {C = C} e = isoToEquiv (f , (g , (η , ϵ)))
  where

  f : (B → C) → A → C
  f h a = h ((equivFun e) a)

  g : (A → C) → B → C
  g h b = h ((invEq e) b)

  η : g ∘ f ∼ id
  η h = funExt (λ b → cong h (secEq e b))

  ϵ : f ∘ g ∼ id
  ϵ h = funExt (λ a → cong h (retEq e a))

substIsContr≃ : {A : Type ℓ} {B : Type ℓ'} → A ≃ B → isContr A → isContr B
substIsContr≃ {A = A} {B = B} e (a , p) = f a , λ y → cong f (p (g y)) ∙ (secEq e y)
  where

  f : A → B
  f = equivFun e

  g : B → A
  g = invEq e

ΣEquiv : {A : Type ℓ} {B B' : A → Type ℓ'} → ((x : A) → B x ≃ B' x) → Σ A B ≃ Σ A B'
ΣEquiv {A = A} {B = B} {B' = B'} e = isoToEquiv (f , (g , (η , ϵ)))
  where

  f : Σ A B → Σ A B'
  f (a , h) = a , (equivFun (e a) h)

  g : Σ A B' → Σ A B
  g (a , h) = a , (invEq (e a) h)

  η : g ∘ f ∼ id
  η (a , h)  = Σ≡ refl (retEq (e a) h)

  ϵ : f ∘ g ∼ id
  ϵ (a , h) = Σ≡ refl (secEq (e a) h)
  
isContrHasLInv : {A : Type ℓ} {B : Type ℓ'} (e : A ≃ B) → isContr (hasLInv (equivFun e))
isContrHasLInv {A = A} {B = B} e = {!!}
  where

  f : A → B
  f = equivFun e

  
