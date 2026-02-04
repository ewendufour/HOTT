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
Circle-rec {A = A} b l x = Circle-ind (λ _ → A) b {!!} x 

Circle-comp-base-nd : {P : Type ℓ} (b : P) (l : b ≡ b) → Circle-rec b l base ≡ b
Circle-comp-base-nd {P = P} b l = Circle-comp-base (λ _ → P) b {!!}

rev : Circle → Circle
rev x = Circle-rec base (sym loop) x

postulate
  Circle-comp-loop-nd : {P : Type ℓ} (b : P) (l : b ≡ b) → cong (Circle-rec b l) loop ≡ l

rev² : rev ∘ rev ≡ id
rev² = funExt λ x → Circle-ind (λ x → rev (rev x) ≡ id x) rrb {!!} x
  where

  rrb : rev (rev base ) ≡ base
  rrb =
    rev (rev base) ≡⟨ {!!} ⟩
    {!!} ≡⟨ {!!} ⟩
    base ∎


