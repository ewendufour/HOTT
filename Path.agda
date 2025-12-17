{-# OPTIONS --without-K #-}
open import Prelude

private variable
  ℓ ℓ' ℓ'' : Level

--- Part 2

sym : { A : Type ℓ } { x y : A } → x ≡ y → y ≡ x
sym refl = refl

J : { A : Type ℓ } { x : A } (P : (y : A) → x ≡ y → Type ℓ') → P x refl → { y : A } → (p : x ≡ y) → P y p
J _ r refl = r

sym' : {A : Type ℓ} {x y : A} → x ≡ y → y ≡ x
sym' {x = x}  = J (λ y p → y ≡ x) refl

trans : {A : Type ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl p = p

infixr 30 _∙_
_∙_ = trans

lUnit : {A : Type ℓ} {x y : A} (p : x ≡ y) → p ≡ refl ∙ p
lUnit refl = refl

rUnit : {A : Type ℓ} {x y : A} (p : x ≡ y) → p ≡ p ∙ refl
rUnit refl = refl


lCancel : {A : Type ℓ} {x y : A} (p : x ≡ y) → sym p ∙ p ≡ refl
lCancel refl = refl

rCancel : {A : Type ℓ} {x y : A} (p : x ≡ y) → p ∙ sym p ≡ refl
rCancel refl = refl

assoc : {A : Type ℓ} {x y z w : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
assoc refl refl refl = refl

symInvo : {A : Type ℓ} {x y : A} (p : x ≡ y) → p ≡ sym (sym p) 
symInvo refl = refl

--- Part 3

cong : {A : Type ℓ} {B : Type ℓ'} (f : A → B) {x y : A} (p : x ≡ y) → f x ≡ f y
cong _ refl = refl

≡× : {A : Type ℓ} {B : Type ℓ'} {x x' : A} {y y' : B} → (x , y) ≡ (x' , y') → (x ≡ x') × (y ≡ y')
≡× refl = (refl , refl)

congConst : {A : Type ℓ} {B : Type ℓ'} {x' : B} {x y : A} (p : x ≡ y) → cong (λ _ → x') p ≡ refl
congConst refl = refl

congComposite : {A : Type ℓ} {B : Type ℓ'} (f : A → B) {x y z : A} (p : x ≡ y) (q : y ≡ z) → cong f (p ∙ q) ≡ (cong f p) ∙ (cong f q)
congComposite _ refl refl = refl

congSym : {A : Type ℓ} {B : Type ℓ'} (f : A → B) {x y : A} (p : x ≡ y) → cong f (sym p) ≡ sym (cong f p)
congSym _ refl = refl

congId : {A : Type ℓ} {x y : A} (p : x ≡ y) → cong (λ x → x) p ≡ p
congId refl = refl

cong∘ : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} (f : A → B) (g : B → C) {x y : A} (p : x ≡ y) → cong (g ∘ f) p ≡ cong g (cong f p)
cong∘ _ _ refl = refl

cong₂ : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} (f : A → B → C) {x y : A} {x' y' : B} (p : x ≡ y) (q : x' ≡ y') → f  x   x'  ≡  f  y   y'
cong₂ _ refl refl = refl

rotate∙≡ : {A : Type ℓ} {x y y' : A} (p : x ≡ y) (q : y ≡ y') (p' : x ≡ y') → p ∙ q ≡ p' → sym p ∙ p' ≡ q
rotate∙≡ p q p' α =
  sym p ∙ p' ≡⟨ cong (λ r → sym p ∙ r ) (sym α) ⟩
  sym p ∙ p ∙ q ≡⟨ sym (assoc (sym p) p q) ⟩
  (sym p ∙ p) ∙ q ≡⟨ cong (λ r → r ∙ q) (lCancel p) ⟩
  refl ∙ q ≡⟨ lUnit q ⟩ 
  q ∎


happly : {A : Type ℓ} {B : A → Type ℓ'} {f g : (x : A) → B x} → f ≡ g → (x : A) → f x ≡ g x
happly refl _ = refl


--- Part 4

subst : {A : Type ℓ} (B : A → Type ℓ') {x y : A} (p : x ≡ y) → B x → B y
subst _ refl p = p

true≢false : ¬ (true ≡ false)
true≢false p = subst (λ b → if b then ⊤ else ⊥) p tt



