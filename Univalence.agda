{-# OPTIONS --without-K #-}

open import Prelude
open import Path
open import HLevels
open import Equivalence
open import FunExtPostulate

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

uβ : {A B : Type ℓ} → (e : A ≃ B) → pathToEquiv (ua e) ≡ e 
uβ e =
  pathToEquiv (ua e) ≡⟨ secEq univalence e ⟩
  id e ≡⟨ refl ⟩
  e ∎


uaβ : {A B : Type ℓ} (e : A ≃ B) → transport (ua e) ≡ equivFun e
uaβ e = trans (sym (pathToEquivTest (ua e))) (cong fst (uβ e))
    
uaη : {A B : Type ℓ} (p : A ≡ B) → ua (pathToEquiv p) ≡ p
uaη p = retEq univalence p

uaIdEquiv : {A : Type ℓ} → ua (idEquiv {A = A}) ≡ refl
uaIdEquiv = uaη refl


--- Part 2

isContr≃≡⊤ : {A : Type} → isContr A ≃ (A ≡ ⊤)
isContr≃≡⊤ = compEquiv isContr≃≃⊤ (invEquiv univalence)


is¬→≃⊥ : {A : Type} → ¬ A → A ≃ ⊥
is¬→≃⊥ f = isoToEquiv (f , (⊥-rec , ((λ x → ⊥-rec (f x)) , λ ())))

≃⊥→is¬ : {A : Type} → A ≃ ⊥ → ¬ A
≃⊥→is¬ (f , _) a = f a

is¬≃≡⊥ : {A : Type} → (¬ A) ≃ (A ≡ ⊥)
is¬≃≡⊥ = compEquiv (↔≃ (isProp→ isProp⊥) (isPropΣ isEquiv (isProp→ isProp⊥) isPropIsEquiv) .fst ( is¬→≃⊥ , ≃⊥→is¬)) (invEquiv univalence)

--- Part 3    

≃ind : (P : {A B : Type ℓ} → (A ≃ B) → Type ℓ') →
       ({A : Type ℓ} → P (idEquiv {A = A})) →
       {A B : Type ℓ} (e : A ≃ B) → P e
≃ind P Pi {A = A} {B = B} e = transport (cong P (uβ e)) (f (ua e))
  where
  f : (p : A ≡ B) → P (pathToEquiv p )
  f refl = Pi

symEquiv : {A : Type ℓ} {B : Type ℓ} (e : A ≃ B) → sym (ua e) ≡ ua (invEquiv e)
symEquiv e = ≃ind (λ z → sym (ua z) ≡ ua (invEquiv z)) ideq e
  where

  ideq : {A : Type ℓ} → sym (ua {A = A}idEquiv) ≡ ua (invEquiv idEquiv)
  ideq =
    sym (ua idEquiv) ≡⟨ cong sym uaIdEquiv ⟩
    refl ≡⟨ sym uaIdEquiv ⟩
    ua idEquiv ≡⟨ cong ua refl ⟩
    ua (invEquiv idEquiv) ∎

--- Part 4

¬isSetType : ¬ (isSet Type)
¬isSetType sT  = true≢false t≡f
  where

  p : Bool ≡ Bool
  p = ua not≃

  t≡f : true ≡ false
  t≡f =
   true ≡⟨ happly (sym (uaβ not≃)) false ⟩
   transport p false ≡⟨ happly (cong transport (sT Bool Bool p refl)) false ⟩
   transport refl false ≡⟨ refl ⟩
   false ∎


--- Part 5

¬notb≡b : (b : Bool) → ¬ (not b ≡ b)
¬notb≡b false = λ ()
¬notb≡b true = λ ()

¬NNE : ¬ ((A : Type) → ¬ ¬ A → A)
¬NNE nne = ¬notb≡b (f u) (trans (sym (happly (uaβ not≃) (f u))) p3 )
  where
  u : ¬ ¬ Bool
  u f = f true

  p : Bool ≡ Bool
  p = ua not≃

  f : ¬ ¬ Bool → Bool
  f = nne Bool

  g : ¬ ¬ Bool → Bool
  g = subst (λ X → ¬ ¬ X → X) p f

  q : g ≡ f
  q = congP (λ X → ¬ ¬ X → X) nne p

  p1 : g u ≡ (transport p (f (subst (λ X → ¬ ¬ X) (sym p) u)))
  p1 = happly (funTypeTransp (λ X → ¬ (¬ X)) id p f) u

  p2 : subst (λ X → ¬ ¬ X) (sym p) u ≡ u
  p2 = funExt (λ x → ⊥-rec (u x))

  p3 : transport p (f u) ≡ f u
  p3 =
    transport p (f u) ≡⟨ cong (transport p) (cong f (sym p2 )) ⟩
    transport p (f (subst (λ X → ¬ ¬ X) (sym p) u)) ≡⟨ sym p1 ⟩
    g u ≡⟨ happly q u ⟩
    f u ∎


LEM→NNE : ((A : Type) → (A ⊎ ¬ A)) → ((B : Type) → ¬ ¬ B → B)
LEM→NNE lem A = f (lem A)
  where

  f : (a : A ⊎ ¬ A) → ¬ ¬ A → A
  f (inl a) = λ _ → a
  f (inr a) = λ g → ⊥-rec (g a)


¬LEM : ¬ ((A : Type) → A ⊎ ¬ A)
¬LEM lem = ¬NNE (LEM→NNE lem)

--- Part 6

decProp : Σ Type (λ A → isProp A × Dec A) ≃ Bool
decProp = isoToEquiv (f , (g , (invl , invr)))
  where

  f : Σ Type (λ A → isProp A × Dec A) → Bool
  f (T , _ , inl t) = true
  f (T , _ , inr t) = false

  g : Bool → Σ Type (λ A → isProp A × Dec A)
  g false = ⊥ , (isProp⊥ , (inr (λ ())))
  g true = ⊤ , ((isProp⊤ , (inl tt)))

  invl : g ∘ f ∼ id
  invl (T , PT , inl t) =
    Σ≡ (sym (ua (isContr→≃⊤ (isProp→isContr PT t))))
       (×≡ (isPropIsProp (subst (λ A → isProp A × Dec A)
                                (sym (isEquivPathToEquiv .fst .fst (isContr→≃⊤ (isProp→isContr PT t))))
                                (isProp⊤ , inl tt) .fst)
                         PT)
           (isPropDec PT (subst (λ A → isProp A × Dec A)
                                (sym (isEquivPathToEquiv .fst .fst (isContr→≃⊤ (isProp→isContr PT t))))
                                (isProp⊤ , inl tt) .snd)
                         (inl t)))
  invl (T , PT , inr t) =
    Σ≡ (sym (ua (is¬→≃⊥ t)))
       (×≡ (isPropIsProp (subst (λ A → isProp A × Dec A)
                                (sym (isEquivPathToEquiv .fst .fst (is¬→≃⊥ t)))
                                (isProp⊥ , inr (λ ())) .fst)
                         PT)
           (isPropDec PT (subst (λ A → isProp A × Dec A)
                                (sym (isEquivPathToEquiv .fst .fst (is¬→≃⊥ t)))
                                (isProp⊥ , inr (λ ())) .snd)
                         (inr t)))

  invr : f ∘ g ∼ id
  invr false = refl
  invr true = refl
