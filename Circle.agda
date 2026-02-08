{-# OPTIONS --without-K --rewriting #-}

open import Prelude
open import Path
open import HLevels
open import Equivalence
open import FunExtPostulate
open import Univalence

private variable
  ℓ ℓ' ℓ'' : Level

--- Part 1

postulate
  Circle : Type₀
  base : Circle
  loop : base ≡ base


postulate
  Circle-ind : (P : Circle → Type ℓ) (b : P base) (l : PathOver P loop b b) → (x : Circle) → P x

{-# BUILTIN REWRITE _≡_ #-}

postulate
  Circle-comp-base : ∀ {i} (P : Circle → Type i) (b : P base) (l : PathOver P loop b b) → Circle-ind P b l base ≡ b
  {-# REWRITE Circle-comp-base #-}
  Circle-comp-loop : ∀ {i} (P : Circle → Type i) (b : P base) (l : PathOver P loop b b) → congP P (Circle-ind P b l) loop ≡ l
  {-# REWRITE Circle-comp-loop #-}


--- Part 2

Circle-rec : {A : Type ℓ} (b : A) (l : b ≡ b) → (x : Circle) → A
Circle-rec {A = A} b l = Circle-ind (λ _ → A) b (substConst loop b)

Circle-comp-base-nd : {P : Type ℓ} (b : P) (l : b ≡ b) → Circle-rec b l base ≡ b
Circle-comp-base-nd {P = P} b l = Circle-comp-base (λ _ → P) b (substConst loop b)

rev : Circle → Circle
rev x = Circle-rec base (sym loop) x

postulate
  Circle-comp-loop-nd : {P : Type ℓ} (b : P) (l : b ≡ b) → cong (Circle-rec b l) loop ≡ l

loop≢refl : ¬ (loop ≡ refl)
loop≢refl lr = true≢false teqf
  where

  p : Bool ≡ Bool
  p = ua not≃
  
  P : Circle → Type
  P = Circle-rec Bool p

  p≡r : p ≡ refl
  p≡r =
    p ≡⟨ sym (Circle-comp-loop-nd Bool p) ⟩
    cong P loop ≡⟨ cong (λ x → cong P x) lr ⟩
    cong P {x = base}refl ≡⟨ refl ⟩
    refl


  teqf : true ≡ false
  teqf =
    true ≡⟨ happly (sym (uaβ not≃)) false ⟩
    transport p false ≡⟨ cong (λ x → transport x false) p≡r ⟩
    transport refl false ≡⟨ refl ⟩
    false ∎ 

postulate
  Circle-unique :
    {A : Type ℓ}
    (f g : Circle → A)
    (p : f base ≡ g base)
    (q : PathOver (λ x → x ≡ x) p (cong f loop) (cong g loop))
    (x : Circle) → f x ≡ g x

Circle-ext : (x : Circle) → Circle-rec base loop x ≡ x
Circle-ext = Circle-unique (Circle-rec base loop) id refl p
  where

  p : PathOver (λ x → x ≡ x) refl (cong (Circle-rec base loop) loop) (cong id loop)
  p =
    subst (λ x → x ≡ x) refl (cong (Circle-rec base loop) loop) ≡⟨ cong (λ z  → subst (λ x → x ≡ x ) refl z ) (Circle-comp-loop-nd base loop) ⟩
    subst (λ x → x ≡ x) refl loop ≡⟨ sym (congId loop) ⟩
    cong id loop ∎


Loops : Type ℓ → Type ℓ
Loops A = Σ A (λ x → x ≡ x)

Circle≡Loops : {A : Type ℓ} → (Circle → A) ≡ Loops A
Circle≡Loops {A = A} = ua (isoToEquiv ({!!} , ({!!} , ({!!} , {!!}))))
  where

  f : (Circle → A) → Loops A
  f g = (g base) , (cong g loop)

  g : Loops A → Circle → A
  g (b , l) = Circle-rec b l

  η : g ∘ f ∼ id
  η h =
    (g ∘ f) h ≡⟨ refl ⟩
    Circle-rec (h base) (cong h loop) ≡⟨ funExt (Circle-unique (Circle-rec (h base) (cong h loop)) h (Circle-comp-base-nd (h base) (cong h loop)) {!!}) ⟩
    h ∎
    
  ϵ : f ∘ g ∼ id
  ϵ x = {!!}

--- Part 2
