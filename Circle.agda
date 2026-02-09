{-# OPTIONS --without-K --rewriting #-}

open import Prelude
open import Path
open import HLevels
open import Equivalence
open import FunExtPostulate
open import Univalence
open import Int

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
Circle-rec {A = A} b l = Circle-ind (λ _ → A) b (substConst loop b ∙ l)

Circle-comp-base-nd : {P : Type ℓ} (b : P) (l : b ≡ b) → Circle-rec b l base ≡ b
Circle-comp-base-nd {P = P} b l = Circle-comp-base (λ _ → P) b (substConst loop b ∙ l)

rev : Circle → Circle
rev x = Circle-rec base (sym loop) x

Circle-comp-loop-nd : {P : Type ℓ} (b : P) (l : b ≡ b) → cong (Circle-rec b l) loop ≡ l
Circle-comp-loop-nd {P = P}b l =
  cong (Circle-ind (λ _ → P)  b (substConst loop b ∙ l)) loop ≡⟨ lemma loop ⟩
  sym (substConst loop (Circle-ind (λ _ → P) b (substConst loop b ∙ l) base)) ∙
  congP (λ _ → P) (Circle-ind (λ _ → P) b (substConst loop b ∙ l)) loop ≡⟨ cong (λ z → sym ( substConst loop (Circle-ind (λ _ → P) b (substConst loop b ∙ l) base)) ∙ z) (Circle-comp-loop (λ _ → P) b (substConst loop b ∙ l)) ⟩
  sym (substConst loop (Circle-ind (λ _ → P) b (substConst loop b ∙ l) base))
  ∙ substConst loop b ∙ l ≡⟨ refl ⟩
  sym (substConst loop b) ∙ substConst loop b ∙ l ≡⟨ sym (assoc (sym (substConst loop b)) (substConst loop b) l )⟩
  (sym (substConst loop b) ∙ substConst loop b) ∙ l ≡⟨ cong (λ z → z ∙ l) (lCancel (substConst loop b)) ⟩
  refl ∙ l ≡⟨ refl ⟩
  l ∎
  
  where

  lemma : {A : Type ℓ} {B : Type ℓ'} {f : A → B} {x y : A} (p : x ≡ y) → cong f p ≡ sym (substConst p (f x)) ∙ congP _  f p
  lemma refl = refl
  
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
Circle≡Loops {A = A} = ua (isoToEquiv (f , (g , (η , ϵ))))
  where

  f : (Circle → A) → Loops A
  f g = (g base) , (cong g loop)

  g : Loops A → Circle → A
  g (b , l) = Circle-rec b l

  η : g ∘ f ∼ id
  η h =
    (g ∘ f) h ≡⟨ refl ⟩
      Circle-rec (h base) (cong h loop) ≡⟨ funExt (Circle-unique (Circle-rec (h base) (cong h loop)) h refl (cong id (Circle-comp-loop-nd (h base) (cong h loop)))) ⟩
    h ∎    
    
  ϵ : f ∘ g ∼ id
  ϵ (a , p) =
    (Circle-rec a p base , cong (Circle-rec a p) loop)  ≡⟨ Σ≡ refl (cong id (Circle-comp-loop-nd a p)) ⟩
    (a , p) ∎

--- Part 2

suc≃ : ℤ ≃ ℤ
suc≃ = isoToEquiv (f , (g , (η , ϵ)))
  where

  f : ℤ → ℤ
  f = sucℤ

  g : ℤ → ℤ
  g = predℤ

  η : g ∘ f ∼ id
  η (pos n) = refl
  η (negsuc zero) = refl
  η (negsuc (suc n)) = refl

  ϵ : f ∘ g ∼ id
  ϵ (pos zero) = refl
  ϵ (pos (suc n)) = refl
  ϵ (negsuc n) = refl

suc≡ : ℤ ≡ ℤ
suc≡ = ua suc≃


loops : ℤ → base ≡ base
loops (pos zero) = refl
loops (pos (suc n)) = loop ∙ loops (pos n)
loops (negsuc zero) = sym loop
loops (negsuc (suc n)) = sym loop ∙ loops (negsuc n)

code : Circle → Type
code x = base ≡ x

encode : (x : Circle) → base ≡ x → code x
encode x p = subst code p (loops (pos zero))
