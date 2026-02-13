{-# OPTIONS --cubical #-}

open import Agda.Builtin.Cubical.Path public
open import Agda.Builtin.Cubical.Sub public
  renaming (primSubOut to outS)
open import Agda.Primitive.Cubical public
  renaming ( primIMin       to _∧_
           ; primIMax       to _∨_
           ; primINeg       to ~_
           ; isOneEmpty     to empty
           ; primComp       to comp
           ; primHComp      to hcomp
           ; primTransp     to transp
           ; itIsOne        to 1=1 )
-- import Agda.Builtin.Cubical.Glue
open import Agda.Primitive public
  using    ( Level
           ; SSet )
  renaming ( lzero to ℓ-zero
           ; lsuc  to ℓ-suc
           ; _⊔_   to ℓ-max
           ; Set   to Type )
open import Agda.Builtin.Sigma public

_[_↦_] : ∀ {ℓ} (A : Type ℓ) (φ : I) (u : Partial φ A) → SSet ℓ
A [ φ ↦ u ] = Sub A φ u

infix 4 _[_↦_]

private variable
  ℓ ℓ' ℓ'' : Level

-- Homogeneous filling
hfill : {A : Type ℓ}
        {φ : I}
        (u : ∀ i → Partial φ A)
        (u0 : A [ φ ↦ u i0 ])
        -----------------------
        (i : I) → A
hfill {φ = φ} u u0 i =
  hcomp (λ j → λ { (φ = i1) → u (i ∧ j) 1=1
                 ; (i = i0) → outS u0 })
        (outS u0)

---
--- Basic types
---

infixr 5 _×_
_×_ : (A : Type ℓ) (B : Type ℓ') → Type (ℓ-max ℓ ℓ')
A × B = Σ A λ _ → B

-- Unit
data Unit : Type ℓ-zero where
  tt : Unit

-- Booleans
data Bool : Type ℓ-zero where
  false : Bool
  true  : Bool

---
--- Functions
---

id : {A : Type ℓ} → A → A
id x = x

infixr 9 _∘_
_∘_ : {A : Type ℓ} {B : A → Type ℓ'} {C : (a : A) → B a → Type ℓ''} (g : {a : A} → (b : B a) → C a b) → (f : (a : A) → B a) → (a : A) → C a (f a)
g ∘ f = λ x → g (f x)
{-# INLINE _∘_ #-}

infixr 4 _∼_
_∼_ : {A : Type ℓ} {B : A → Type ℓ'} (f g : (x : A) → B x) → Type (ℓ-max ℓ ℓ')
f ∼ g = (x : _) → f x ≡ g x

---
--- Equivalences
---

infix 4 _≃_
_≃_ : (A : Type ℓ) (B : Type ℓ') → Type (ℓ-max ℓ ℓ')
A ≃ B = Σ (A → B) λ f → (Σ (B → A) (λ g → g ∘ f ∼ id)) × (Σ (B → A) (λ g → f ∘ g ∼ id))

data Iso (A : Type ℓ) (B : Type ℓ') : Type (ℓ-max ℓ ℓ') where
  iso : (f : A → B) (g : B → A) (gf : g ∘ f ∼ id) (fg : f ∘ g ∼ id) → Iso A B

isoToEquiv : {A : Type ℓ} {B : Type ℓ'} → Iso A B → A ≃ B
isoToEquiv (iso f g gf fg) = f , ((g , gf) , (g , fg))
