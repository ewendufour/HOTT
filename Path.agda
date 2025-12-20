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
Σ≡ {x = x} refl q = cong (λ y → x , y) q

congP : {A : Type ℓ} (B : A → Type ℓ') (f : (x : A) → B x) { x y : A} (p : x ≡ y) → PathOver B p (f x) (f y)
congP _ _ refl = refl

funTypeTranspR : {A : Type ℓ} {B B' : Type ℓ'} (p : B ≡ B') (f : A → B) → subst (λ X → A → X) p f ≡ transport p ∘ f
funTypeTranspR refl _ = refl

funTypeTranspL : {A A' : Type ℓ} {B : Type ℓ'} (p : A ≡ A') (f : A → B) → subst (λ X → X → B) p f ≡ f ∘ transport (sym p)
funTypeTranspL refl _ = refl

funTypeTransp : {A : Type ℓ} (B : A → Type ℓ') (C : A → Type ℓ'') {x y : A} (p : x ≡ y) (f : B x → C x) → PathOver (λ x → B x → C x) p f (subst C p ∘ f ∘ subst B (sym p))
funTypeTransp _ _ refl _ = refl

--- Part 6

UIP : Type₁
UIP = {A : Type} {x y : A} (p q : x ≡ y) → p ≡ q

URP : Type₁
URP = {A : Set} {x : A} (p : x ≡ x) → p ≡ refl

K : Type₁
K = {A : Type} {x : A} (P : (x ≡ x) → Set) → P refl → (p : x ≡ x) → P p

UIP→URP : UIP → URP
UIP→URP = λ uip p → uip p refl

URP→UIP : URP → UIP
URP→UIP = λ urp → λ {refl q → sym (urp q)}

URP→K : URP → K
URP→K = λ urp P Pr p → subst P (sym (urp p)) Pr

K→URP : K → URP
K→URP = λ k p → k (λ x → x ≡ refl) refl p


--- Part 7

_==_ : {ℓ : Level} {A : Type ℓ} → A → A → Type _
_==_ {ℓ} {A} x y = (P : A → Type ℓ) → P x → P y


Lrefl : {A : Type ℓ} {x : A} → x == x
Lrefl _ px = px


Lsym : {A : Type ℓ} {x y : A} → x == y → y == x
Lsym {x = x} lxy P = lxy (λ z → P z → P x) (Lrefl P)


Ltrans : {A : Type ℓ} {x y z : A} → x == y → y == z → x == z
Ltrans {z = z} lxy lyz P px = lyz P (lxy P px)

Lto≡ : {A : Type ℓ} {x y : A} → x == y → x ≡ y
Lto≡ {x = x} lxy = lxy (λ z → x ≡ z) refl

≡toL : {A : Type ℓ} {x y : A} → x ≡ y → x == y
≡toL refl = Lrefl

≡to≡ : {A : Type ℓ} {x y : A} (p : x ≡ y) → Lto≡ (≡toL p) ≡ p
≡to≡ refl = refl

--- Part 8

J' : {A : Type ℓ} (P : (x y : A) → x ≡ y → Type ℓ') → ((x : A) → P x x refl) → {x y : A} (p : x ≡ y) → P x y p
J' P f {x = x} p = J (P x) (f x) p

J'' : {A : Type ℓ} {x : A} (P : (y : A) → x ≡ y → Type ℓ') → P x refl → {y : A} (p : x ≡ y) → P y p
J'' {A = A} P Pxr p = f p P Pxr
  where
  D : (x y : A) → (x ≡ y) → Type _
  D x y p =  (C : (z : A) → (x ≡ z) → Type _) → C x refl → C y p 
  d : (x : A) → D x x refl
  d x C c = c
  f : {x y : A} → (p : x ≡ y) → D x y p
  f = J' D d

--- Part 9

_■ᵣ_ : {A : Type ℓ} {a b c : A} {p q : a ≡ b} (α : p ≡ q) (r : b ≡ c) → p ∙ r ≡ q ∙ r
_■ᵣ_ {p = p} {q = q} α refl = sym (rUnit p) ∙ α ∙ rUnit q


lemma1 : {A : Type ℓ} {x : A } (α : refl { x = x } ≡ refl) →  α ■ᵣ refl ≡ sym (rUnit refl) ∙ α ∙ rUnit refl
lemma1 _ = refl

_■ₗ_ : {A : Type ℓ} {a b c : A} {r s : b ≡ c} (q : a ≡ b ) (β : r ≡ s) → q ∙ r ≡ q ∙ s
_■ₗ_ {r = r} {s = s} refl β = sym (lUnit r) ∙ β ∙ lUnit s

lemma2 : {A : Type ℓ} {x : A} (β : refl { x = x } ≡ refl) → refl ■ₗ β ≡ sym (lUnit refl) ∙ β ∙ lUnit refl
lemma2 _ = refl

_⋆_ : {A : Type ℓ} {a b c : A} {p q : a ≡ b} {r s : b ≡ c} (α : p ≡ q) (β : r ≡ s) → p ∙ r ≡ q ∙ s
_⋆_ {q = q} {r = r} α β = (α ■ᵣ r) ∙ (q ■ₗ β)

_⋆'_ : {A : Type ℓ} {a b c : A} {p q : a ≡ b} {r s : b ≡ c} (α : p ≡ q) (β : r ≡ s) → p ∙ r ≡ q ∙ s
_⋆'_ {p = p} {s = s} α β = (p ■ₗ β) ∙ (α ■ᵣ s)

starToTrans : { A : Type ℓ} {x : A} (α β : refl {x = x} ≡ refl) → (α ⋆ β) ≡ (α ∙ β)
starToTrans {A = A} {x = x} α β =
  (α ⋆ β) ≡⟨ refl ⟩
  (α ■ᵣ refl ) ∙ (refl ■ₗ β) ≡⟨ cong (λ z →  z ∙ (refl ■ₗ β)) (lemma1 α) ⟩
  (sym (rUnit refl) ∙ α ∙ rUnit refl) ∙ (refl ■ₗ β) ≡⟨ assoc (sym (rUnit refl) ∙ α) (rUnit refl) (refl ■ₗ β ) ⟩
  sym (rUnit refl) ∙ α ∙ rUnit refl ∙ (refl ■ₗ β) ≡⟨ cong (λ z → sym (rUnit refl) ∙ α ∙ rUnit refl ∙ z)  refl ⟩
  sym (rUnit refl) ∙ α ∙ rUnit refl ∙ sym (lUnit refl) ∙ β ∙ lUnit refl ≡⟨ refl ⟩
  α ∙ β ∙ refl ≡⟨ cong (λ z →  α ∙ z ) (sym (rUnit β)) ⟩
  α ∙ β ∎

starToStar' : { A : Type ℓ } {a b c : A} (p : a ≡ b) {q : a ≡ b} (r : b ≡ c) {s : b ≡ c} (α : p ≡ q) (β : r ≡ s) → α ⋆ β ≡ α ⋆' β
starToStar' refl refl refl refl = refl

star'ToTrans : {A : Type ℓ} {x : A} (α β : refl {x = x} ≡ refl) → (α ⋆' β) ≡ (β ∙ α)
star'ToTrans {A = A} {x = x} α β =
  α ⋆' β ≡⟨ refl ⟩
  (refl ■ₗ β) ∙ (α ∙ refl) ≡⟨ cong (λ z → ((refl ■ₗ β) ∙ z)) (lemma1 α) ⟩
  (refl ■ₗ β) ∙ sym (rUnit refl) ∙ α ∙ rUnit refl ≡⟨ cong (λ z → z ∙ sym (rUnit refl) ∙ α ∙ rUnit refl) (lemma2 β) ⟩
  (sym (lUnit refl) ∙ β ∙ lUnit refl) ∙ sym (rUnit refl) ∙ α ∙ rUnit refl ≡⟨ assoc (sym (lUnit refl) ∙ β) (lUnit refl) (sym (rUnit refl) ∙ α ∙ rUnit refl) ⟩
  β ∙ α ∙ refl ≡⟨ cong (λ z → β ∙ z) ( sym (rUnit α)) ⟩
  β ∙ α ∎

EH : {A : Type ℓ} {x : A} (α β : refl {x = x} ≡ refl) → α ∙ β ≡ β ∙ α
EH α β =
  α ∙ β ≡⟨ sym (starToTrans α β) ⟩
  α ⋆ β ≡⟨ starToStar' refl refl α β ⟩
  α ⋆' β ≡⟨ star'ToTrans α β ⟩
  β ∙ α ∎
  
  
