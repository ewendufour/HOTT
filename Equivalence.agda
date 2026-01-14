{-# OPTIONS --without-K #-}

open import Prelude
open import Path
open import HLevels

private variable
  ℓ ℓ' ℓ'' : Level

--- Part 1

_∼_ : {A : Type ℓ} {B : A → Type ℓ'} (f g : (x : A) → B x) → Type (ℓ-max ℓ ℓ')
f ∼ g = (x : _) → f x ≡ g x
infixr 4 _∼_

∼refl : {A : Type ℓ} {B : A → Type ℓ'} {f : (x : A) → B x} → f ∼ f
∼refl x = refl

∼sym : {A : Type ℓ} {B : A → Type ℓ'} {f g : (x : A) → B x} → f ∼ g → g ∼ f
∼sym α x = sym (α x)

∼trans : {A : Type ℓ} {B : A → Type ℓ'} {f g h : (x : A) → B x} → f ∼ g → g ∼ h → f ∼ h
∼trans α β x = trans (α x) (β x)

∼LWhisk : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} (f : A → B) {g g' : B → C} → g ∼ g' → (g ∘ f) ∼ (g' ∘ f)
∼LWhisk f α x = α (f x)

∼RWhisk : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} {f f' : A → B} → f ∼ f' → (g : B → C) → (g ∘ f) ∼ (g ∘ f')
∼RWhisk α g x =  cong g (α x)


--- Part 2

module _ {A : Type ℓ} {B : Type ℓ'} (f : A → B) where

  hasLInv : Type (ℓ-max ℓ ℓ')
  hasLInv = Σ (B → A) (λ g → g ∘ f ∼ id)

  hasRInv : Type (ℓ-max ℓ ℓ')
  hasRInv = Σ (B → A) (λ g → f ∘ g ∼ id)

  hasQInv : Type (ℓ-max ℓ ℓ')
  hasQInv = Σ (B → A) (λ g → (g ∘ f ∼ id) × (f ∘ g ∼ id))

  isEquiv : Type (ℓ-max ℓ ℓ')
  isEquiv = hasLInv × hasRInv

  hasQInv→isEquiv : hasQInv → isEquiv
  hasQInv→isEquiv (f , qI) = ((f , qI .fst) , (f , qI .snd))

  isEquiv→hasQInv : isEquiv → hasQInv
  isEquiv→hasQInv ((g , lI) , (h , rI)) = ( g , (lI , λ x →  cong (f ∘ g) (sym (rI x)) ∙ cong f (lI (h x)) ∙ rI x) )

  postulate
    isPropIsEquiv : isProp isEquiv


Iso : (A : Type ℓ) (B : Type ℓ') → Type (ℓ-max ℓ ℓ')
Iso A B = Σ (A → B) hasQInv

_≃_ : (A : Type ℓ) (B : Type ℓ') → Type (ℓ-max ℓ ℓ')
A ≃ B = Σ (A → B) isEquiv
infix 4 _≃_

module _ {A : Type ℓ} {B : Type ℓ'} (e : A ≃ B) where
  equivFun : A → B
  equivFun = fst e

  invEq : B → A
  invEq = isEquiv→hasQInv equivFun (snd e) .fst

  retEq : invEq ∘ equivFun ∼ id
  retEq = isEquiv→hasQInv equivFun (snd e) .snd .fst

  secEq : equivFun ∘ invEq ∼ id
  secEq = isEquiv→hasQInv equivFun (snd e) .snd .snd


isoToEquiv : {A : Type ℓ} {B : Type ℓ'} → Iso A B → A ≃ B
isoToEquiv (f , inv) = (f , hasQInv→isEquiv f inv)

idEquiv : {A : Type ℓ} → A ≃ A
idEquiv = (id , ((( id , λ _ → refl)) , (id , λ _ → refl)))

invEquiv : {A : Type ℓ} {B : Type ℓ'} → A ≃ B → B ≃ A
invEquiv {A = A} {B = B} eqAB =  isoToEquiv invIso
  where
  invIso : Iso B A
  invIso = ((invEq eqAB , isEquiv→hasQInv (invEq eqAB) (((( eqAB .fst , secEq eqAB)) , (equivFun eqAB , retEq eqAB))) ))

compEquiv : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} → A ≃ B → B ≃ C → A ≃ C
compEquiv {A = A} {B = B} {C = C} eqAB eqBC = isoToEquiv compIso
  where
  f : A → B
  f = equivFun eqAB

  fI : B → A
  fI = invEq eqAB

  g : B → C
  g = equivFun eqBC

  gI : C → B
  gI = invEq eqBC

  ∼LinvID : (λ x → fI (gI (g (f x)))) ∼ id
  ∼LinvID = ∼trans (∼RWhisk (λ x → retEq eqBC (f x) ) fI) (retEq eqAB)

  ∼RinvID : (λ x → g (f (fI (gI x)))) ∼ id
  ∼RinvID = ∼trans (∼RWhisk (λ x → secEq eqAB (gI x)) g) (secEq eqBC)

  
  compIso : Iso A C
  compIso = (g ∘ f , (fI ∘ gI , (∼LinvID , ∼RinvID)) )


_≃⟨_⟩_ : (A : Type ℓ) {B : Type ℓ'} {C : Type ℓ''} → (A ≃ B) → (B ≃ C) → (A ≃ C)
_ ≃⟨ f ⟩ g = compEquiv f g

_■ : (A : Type ℓ) → (A ≃ A)
_■ A = idEquiv

infixr  0 _≃⟨_⟩_
infix   1 _■

equivEq : {A : Type ℓ} {B : Type ℓ'} {e e' : A ≃ B} → equivFun e ≡ equivFun e' → e ≡ e'
equivEq eq = {!!}

--- Part 3

points≃ : (A : Type ℓ) → A ≃ (⊤ → A)
points≃ A = (λ x y → x) , (((λ z → z tt) , (λ x → refl)) , ((λ z → id z tt) , (λ x → refl)))


isContr→≃⊤ : {A : Type} → isContr A → A ≃ ⊤
isContr→≃⊤  (x , f) = (λ _ → tt) , ((λ _ → x) , λ y → f y) , (λ _ → x) , (λ y → refl)

≃⊤→isContr : {A : Type} → A ≃ ⊤ → isContr A
≃⊤→isContr eq = invEq eq tt , λ y → eq .snd .fst .snd y

not : Bool → Bool
not false = true
not true = false

not≃ : Bool ≃ Bool
not≃ = not , hasQInv→isEquiv not (not , ((λ x → notInvol x) , λ x → notInvol x))
  where

  notInvol : (x : Bool) → not (not x) ≡ x
  notInvol false = refl
  notInvol true = refl

×≡Equiv : {A : Type ℓ} {B : Type ℓ} {x x' : A} {y y' : B} → ((x , y) ≡ (x' , y')) ≃ (x ≡ x') × (y ≡ y')
×≡Equiv {A = A} {B = B} {x = x} {x' = x'} {y = y} {y' = y' } = isoToEquiv ((λ p → cong fst p , cong snd p) ,  pair≡ (x , y) (x' , y') , invl , invr )
  where

  pair≡ : (z z' : A × B) → (fst z ≡ fst z') × (snd z ≡ snd z') → z ≡ z'
  pair≡ (a , b) (a' , b') (refl , refl) = refl

  invl : (λ z → pair≡ (x , y) (x' , y') (cong (λ p → fst p) z , cong (λ p → snd p) z)) ∼ id
  invl refl = refl

  invr : (λ z → cong (λ p → fst p) (pair≡ (x , y) (x' , y') z) , cong (λ p → snd p) (pair≡ (x , y) (x' , y') z)) ∼ id
  invr (refl , refl) = refl

Σ≡Equiv : {A : Type ℓ} (B : A → Type ℓ') {x x' : A} {y : B x} {y' : B x'} → ((x , y) ≡ (x' , y')) ≃ Σ (x ≡ x') (λ p → PathOver B p y y')
Σ≡Equiv B {x = x} {x' = x'} {y = y} {y' = y'} = isoToEquiv f
  where

  f : Iso ((x , y) ≡ (x' , y')) (Σ (x ≡ x') (λ p → PathOver B p y y'))
  f = {!!} , {!!}



