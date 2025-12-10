open import Prelude

---Part 3
comm× : { A B : Type} → A × B → B × A
comm× (a , b) = (b , a)


comm×-involutive : { A B : Type} (a : A) (b : B) → comm× (comm× (a , b)) ≡ (a , b)
comm×-involutive _ _ = refl

assoc× : { A B C : Type} → (A × B) × C → A × (B × C )
assoc× ((a , b), c) = (a , (b , c))

comm⊎ : { A B : Type} → A ⊎ B → B ⊎ A
comm⊎ (inl x) = inr x
comm⊎ (inr x) = inl x

comm⊎-involutive : { A B : Type} (x : A ⊎ B) → comm⊎ (comm⊎ x) ≡ x
comm⊎-involutive (inl x) = refl
comm⊎-involutive (inr x) = refl

dist⊎ : {A B C : Type} → A × (B ⊎ C) → (A × B) ⊎ (A × C)
dist⊎ (a , inl x) = inl (a , x)
dist⊎ (a , inr x) = inr (a , x)

_⟷_ : ( A B : Type) → Type
A ⟷ B = (A → B) × (B → A)

currying : { A B C : Type } → (A × B → C) ⟷ (A → B → C)
currying = ((λ f a b → f (a , b))  , λ f (a , b) → f a b)

---Part 4

_+_ : ℕ → ℕ → ℕ
zero + b = b
suc a + b = suc (a + b)

pred : ℕ → ℕ
pred zero = zero
pred (suc x) = x

+-unitl : (n : ℕ) → 0 + n ≡ n
+-unitl zero = refl
+-unitl (suc n) = refl

cong : {A B : Type} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong _ refl = refl

+-unitr : (n : ℕ) → n + 0 ≡ n
+-unitr zero = refl
+-unitr (suc n) = cong suc (+-unitr n)

+-assoc : (m n o : ℕ) → ((m + n) + o) ≡ (m + (n + o))
+-assoc zero n o = refl 
+-assoc (suc m) n o = cong suc (+-assoc m n o)

sym : {A : Type} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Type} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

+-suc : (m n : ℕ) → m + (suc n) ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n = cong suc (+-suc m n)

+-comm : (m n : ℕ) → m + n  ≡ n + m
+-comm m zero = trans (+-unitr m) refl
+-comm m (suc n) = trans (+-suc m n) (cong suc (+-comm m n))

pred-suc : (n : ℕ) → pred (suc n) ≡ n
pred-suc _ = refl

suc-pred : (n : ℕ) → ¬ (n ≡ 0) → suc (pred n) ≡ n
suc-pred zero nz = ⊥-rec (nz refl)
suc-pred (suc n) nz = cong suc refl

zero-suc : (n : ℕ) → ¬ (zero ≡ suc n)
zero-suc zero ()
zero-suc (suc n) ()

suc-inj : { m n : ℕ} → suc m ≡ suc n → m ≡ n
suc-inj refl = refl

nat-dec-eq : (m n : ℕ) → (m ≡ n) ⊎ ¬ (m ≡ n)
nat-dec-eq zero zero = inl refl
nat-dec-eq zero (suc n) = inr (zero-suc n)
nat-dec-eq (suc m) zero = inr λ ()  
nat-dec-eq (suc m) (suc n) with nat-dec-eq m n 
...| inl e = inl (cong suc e)
...| inr f = inr λ smsn -> f (suc-inj smsn)

div2 : (n : ℕ) → Σ ℕ (λ q → (q + q ≡ n ⊎ suc (q + q) ≡ n))
div2 zero = (0 , inl refl )
div2 (suc n) with div2 n
...| (q , inl f) = (q , inr (cong suc f))
...| (q , inr f) = ( suc q , inl (cong suc (trans (+-comm q (suc q)) f)) )

subst  : { A : Type} (P : A → Type) {x y : A} → x ≡ y → P x → P y
subst _ refl px = px

data Even : ℕ → Type where
  evenZero : Even zero
  evenSuc  : {n : ℕ} → Even n → Even (suc (suc n))

double-even : (n : ℕ) → Even (n + n)
double-even zero = evenZero
double-even (suc n) = subst Even (sym (+-suc (suc n) n)) (evenSuc (double-even n))

---Part 5

rec⊎ : {A B C : Type} → (A → C) → (B → C) → A ⊎ B → C
rec⊎ fa _ (inl a) = fa a
rec⊎ _ fb (inr b) = fb b


elim⊎ : {A B : Type} (C : A ⊎ B → Type) → ((x : A) → C (inl x)) → ((x : B) → C (inr x)) → (x : A ⊎ B) → C x
elim⊎ _ Cl _  (inl x) = Cl x
elim⊎ _ _  Cr (inr x) = Cr x

comp⊎l : {A B : Type} (C : A ⊎ B → Type) (f : (x : A) → C (inl x)) (g : (x : B) → C (inr x)) (x : A) → elim⊎ C f g (inl x) ≡ f x
comp⊎l _ _ _ _ = refl

comp⊎r : {A B : Type} (C : A ⊎ B → Type) (f : (x : A) → C (inl x)) (g : (x : B) → C (inr x)) (x : B) → elim⊎ C f g (inr x) ≡ g x
comp⊎r _ _ _ _ = refl

uniq⊎ : {A B : Type} (x : A ⊎ B) → elim⊎ (λ _ → A ⊎ B) inl inr x ≡ x
uniq⊎ (inl x) = refl
uniq⊎ (inr x) = refl

elim× : {A B : Type} (C : A × B → Type) → ((x : A) → (y : B) → C (x , y) ) → (x : A × B) → C x
elim× _ f (a , b) = f a b

comp× : {A B : Type} (C : A × B → Type) (f : (x : A) → (y : B) → C (x , y)) (x : A ) (y : B) → elim× C f (x , y) ≡ f x y
comp× _ _ _ _ = refl


uniq× : { A B : Type} (x : A × B) → elim× (λ _ → A × B) (λ a b → (a , b)) x ≡ x
uniq× (a , b) = refl



