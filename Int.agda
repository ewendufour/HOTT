{-# OPTIONS --without-K #-}

open import Prelude
open import Path

-- The integers
data ℤ : Set where
  pos :    (n : ℕ) → ℤ --    pos n means n
  negsuc : (n : ℕ) → ℤ -- negsuc n means -n-1

-- Zero
0ℤ : ℤ
0ℤ = pos zero

-- One
1ℤ : ℤ
1ℤ = pos (suc zero)

-- Successor function
sucℤ : ℤ → ℤ
sucℤ (pos n)          = pos (suc n)
sucℤ (negsuc zero)    = pos 0
sucℤ (negsuc (suc n)) = negsuc n

-- Predecessor function
predℤ : ℤ → ℤ
predℤ (pos zero)    = negsuc zero
predℤ (pos (suc n)) = pos n 
predℤ (negsuc n)    = negsuc (suc n)

sucPred : (n : ℤ) → sucℤ (predℤ n) ≡ n
sucPred (pos zero)    = refl
sucPred (pos (suc n)) = refl
sucPred (negsuc n)    = refl

predSuc : (n : ℤ) → predℤ (sucℤ n) ≡ n
predSuc (pos n)          = refl
predSuc (negsuc zero)    = refl
predSuc (negsuc (suc n)) = refl

_+_ : ℤ → ℤ → ℤ
pos zero + n       = n
pos (suc m) + n    = sucℤ (pos m + n)
negsuc zero + n    = predℤ n
negsuc (suc m) + n = predℤ (negsuc m + n)

addZero : (n : ℤ) → n + 0ℤ ≡ n
addZero (pos zero)       = refl
addZero (pos (suc n))    = cong sucℤ (addZero (pos n))
addZero (negsuc zero)    = refl
addZero (negsuc (suc n)) = cong predℤ (addZero (negsuc n))

negℤ : ℤ → ℤ
negℤ (pos zero) = pos zero
negℤ (pos (suc n)) = negsuc n
negℤ (negsuc n) = pos (suc n)

_-_ : ℤ → ℤ → ℤ
m - n = m + (negℤ n)

open import HLevels

postulate
  -- Left to the reader...
  discreteℤ : Discrete ℤ

isSetℤ : isSet ℤ
isSetℤ = Discrete→isSet discreteℤ
