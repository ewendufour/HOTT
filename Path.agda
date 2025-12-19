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

cong₂ : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} (f : A → B → C) {x y : A} {x' y' : B} (p : x ≡ y) (q : x' ≡ y') → f x x'  ≡  f y y'
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

transport : {A B : Type ℓ} → A ≡ B → A → B
transport e a = subst (λ X → X) e a

subst' : {A : Type ℓ} {B : A → Type ℓ'} {x y : A} (p : x ≡ y) → B x → B y
subst' {B = B} p bx = transport (cong B p) bx

substComposite : {A : Type ℓ} (B : A → Type ℓ) {x y z : A} (p : x ≡ y) (q : y ≡ z) (x' : B x) → subst B (p ∙ q) x' ≡ subst B q (subst B p x')
substComposite _ refl refl _ = refl

substConst : { ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} {x y : A} (p : x ≡ y) (x' : B) → subst (λ _ → B) p x' ≡ x'
substConst refl _ = refl

substInPathsR : {A : Type ℓ} {x y y' : A} (p : x ≡ y) (q : y ≡ y') → subst (λ y → x ≡ y) q p ≡ p ∙ q
substInPathsR refl refl = refl

substInPathsL : {A : Type ℓ} {x x' y : A} (p : x ≡ x') (q : x ≡ y) → subst (λ x → x ≡ y) p q ≡ sym p ∙ q
substInPathsL refl refl = refl

substInPaths : {A : Type ℓ} {B : Type ℓ'} {x y : A} (f g : A → B) (p : x ≡ y) (q : f x ≡ g x) → subst (λ x → f x ≡ g x) p q ≡ sym (cong f p) ∙ q ∙ cong g p
substInPaths f g refl q = rUnit q

substInPathsL' : {A : Type ℓ} {B : Type ℓ'} {x x' : A} (f : A → B) {y : B} (p : x ≡ x') (q : f x ≡ y) → subst (λ x → f x ≡ y) p q ≡ sym (cong f p) ∙ q
substInPathsL' {x' = x'} f {y = y} p q =
  subst (λ x → f x ≡ y) p q ≡⟨ substInPaths f (λ _ → y) p q ⟩
  sym (cong f p) ∙ q ∙ cong (λ _ → y) p ≡⟨ cong (λ r → sym (cong f p) ∙ q ∙ r ) (congConst p) ⟩
  sym (cong f p) ∙ q ∙ refl ≡⟨ cong (λ x → sym (cong f p) ∙ x) (sym (rUnit q)) ⟩
  sym (cong f p) ∙ q ∎

--- Part 5

PathOver : {A : Type ℓ} (B : A → Type ℓ') {x y : A} (p : x ≡ y) (x' : B x) (y' : B y) → Type ℓ'
PathOver B p x' y' = subst B p x' ≡ y'

×≡ : {A : Type ℓ} {B : Type ℓ'} {x x' : A} {y y' : B} → (p : x ≡ x') (q : y ≡ y') → (x , y) ≡ (x' , y')
×≡ refl refl = refl

Σ≡ : {A : Type ℓ} {B : A → Type ℓ'} {x x' : A} (p : x ≡ x') {y : B x} {y' : B x'} → PathOver B p y y' → (x , y) ≡ (x' , y')
Σ≡ p q = {!!}
