{-# OPTIONS --without-K #-}

open import Prelude
open import Path
open import HLevels
open import Equivalence
open import EquivalenceDefinitions
open import Univalence
open import FunExtPostulate

--- Part 1

module Duality {ℓ : Level} (B : Type ℓ) where

  Fam : Type (ℓ-suc ℓ)
  Fam = B → Type ℓ

  Fib : Type (ℓ-suc ℓ)
  Fib = Σ (Type ℓ) (λ A → A → B)

  src : Fib → Type ℓ
  src (A , _) = A


--- Part 2

  total : Fam → Fib
  total P = (Σ B λ y → P y) , fst

  fib : Fib → Fam
  fib f y = Σ (src f) (λ x → f .snd x ≡ y)

  fiberTotal : (P : Fam) (x : B) → fib (total P) x ≃ P x
  fiberTotal P x =
    fib (total P) x ≃⟨ idEquiv ⟩
    Σ (Σ B P) (λ (b , y) → total P .snd  (b , y) ≡ x )  ≃⟨ idEquiv ⟩
    Σ (Σ B P) (λ (b , y) → b ≡ x) ≃⟨ eq1 ⟩
    Σ B (λ b → (Σ (P b) (λ y → b ≡ x))) ≃⟨ ΣEquiv eq2 ⟩
    Σ B (λ b → (b ≡ x) × P b) ≃⟨ eq3 ⟩
    Σ (Σ B (λ b → b ≡ x)) (λ f → P (f .fst) ) ≃⟨ eq4 ⟩
    Σ ⊤ (λ _ → P x) ≃⟨ eq5 ⟩
    P x ■

    where

    eq1 : Σ (Σ B P) (λ (b , y) → b ≡ x) ≃ Σ B (λ b → (Σ (P b) (λ y → b ≡ x)))
    eq1 = isoToEquiv (f , g , ((λ _ → refl) , λ _ → refl ))
      where

      f : Σ (Σ B P) (λ (b , y) → b ≡ x) → Σ B (λ b → (Σ (P b) (λ y → b ≡ x)))
      f ((b , p) , h) = b , (p , h)

      g : Σ B (λ b → (Σ (P b) (λ y → b ≡ x))) → Σ (Σ B P) (λ (b , y) → b ≡ x)
      g (b , p , h) = (b , p) , h

    eq2 : (y : B) → Σ (P y) (λ _ → y ≡ x) ≃ (y ≡ x) × P y
    eq2 y = isoToEquiv (f , (g , ((λ _ → refl) , λ _ → refl)))
      where

      f : Σ (P y) (λ _ → y ≡ x) → (y ≡ x) × P y
      f (p , f') = f' , p

      g : (y ≡ x) × P y → Σ (P y) (λ _ → y ≡ x)
      g (p , q) = q , p

    eq3 : Σ B (λ b → (b ≡ x) × P b) ≃ Σ (Σ B (λ b → b ≡ x)) (λ f → P (f .fst) )
    eq3 = isoToEquiv (f , (g , ((λ _ → refl) , λ _ → refl)))
      where

      f : Σ B (λ b → (b ≡ x) × P b) → Σ (Σ B (λ b → b ≡ x)) (λ f → P (f .fst))
      f (b , p , pb) = (b , p) , pb

      g : Σ (Σ B (λ b → b ≡ x)) (λ f → P (f .fst)) → Σ B (λ b → (b ≡ x) × P b)
      g ((b , p) , pb ) = b , (p , pb)

    eq4 : Σ (Σ B (λ b → b ≡ x)) (λ f → P (f .fst) ) ≃ Σ ⊤ (λ _ → P x)
    eq4 = isoToEquiv (f , g , (η , λ _ → refl))
      where

      f : Σ (Σ B (λ b → b ≡ x)) (λ f → P (f .fst) ) → Σ ⊤ (λ _ → P x)
      f ((b , p) , pb) = tt , subst P p pb

      g : Σ ⊤ (λ _ → P x) → Σ (Σ B (λ b → b ≡ x)) (λ f → P (f .fst) )
      g (_ , px) = (x , refl) , px

      η : g ∘ f ∼ id
      η ((b , refl) , pb) = refl

    eq5 : Σ ⊤ (λ _ → P x) ≃ P x
    eq5 = isoToEquiv ((λ p → p .snd) , ((λ y → (tt , y) ) , (λ _ → refl) , λ _ → refl))

  totalEquiv : (f : Fib) → Σ B (fib f) ≃ src f
  totalEquiv (A , f) =
    Σ B (fib (A , f)) ≃⟨ idEquiv ⟩
    Σ B (λ b → Σ A (λ a → f a ≡ b)) ≃⟨ isoToEquiv ((λ (b , a , p) → a , (b , p)) ,
                                                  ((λ (a , b , p) → b , (a , p)) ,
                                                  ((λ _ → refl) , (λ _ → refl)))) ⟩
    Σ A (λ a → Σ B (λ b → f a ≡ b)) ≃⟨ eq1 ⟩
    Σ A (λ _ → ⊤) ≃⟨ isoToEquiv ((λ (a , _) → a) , ((λ a → (a , tt)) , ((λ x → refl) , (λ x → refl)))) ⟩
    A ■
    where

    eq1 : Σ A (λ a → Σ B (λ b → f a ≡ b)) ≃ Σ A (λ _ → ⊤)
    eq1 = isoToEquiv (f' , (g , (η , ϵ)))
      where

      f' : Σ A (λ a → Σ B (λ b → f a ≡ b)) → Σ A (λ _ → ⊤)
      f' (a , b , p) = a , tt

      g : (Σ A (λ _ → ⊤)) → Σ A (λ a → Σ B (λ b → f a ≡ b)) 
      g (a , _)= a , ((f a) , refl)

      η : g ∘ f' ∼ id
      η (a , b , refl)= refl

      ϵ : f' ∘ g ∼ id
      ϵ x = refl

 
  Fib≃Fam : {A : Type ℓ} → Fib ≃ Fam
  Fib≃Fam = isoToEquiv (fib , (total ,
                       ((λ f → Σ≡ (ua (totalEquiv f)) (p f)) ,
                       (λ P → funExt (λ x → ua (fiberTotal P x))))))
      where

      p : (f : Fib) → PathOver (λ A → A → B) (ua (totalEquiv f)) fst (f .snd)
      p f =
        subst (λ A → A → B) (ua (totalEquiv f)) fst ≡⟨ funTypeTranspL (ua (totalEquiv f)) fst ⟩
        fst ∘ transport (sym (ua (totalEquiv f))) ≡⟨ cong (λ z → fst ∘ transport z) (symEquiv (totalEquiv f)) ⟩
        fst ∘ (transport (ua (invEquiv (totalEquiv f)))) ≡⟨ cong (λ z → fst ∘ z) (uaβ (invEquiv (totalEquiv f))) ⟩
        fst ∘ (equivFun (invEquiv (totalEquiv f))) ≡⟨ refl ⟩
        f .snd ∎


--- Part 3

  Map : Fam → Fam → Type ℓ
  Map P Q = (x : B) → P x → Q x

  totalMap : {P Q : Fam} → Map P Q → Σ B P → Σ B Q
  totalMap f w = (fst w) , (f (fst w) (snd w))

  open import EquivalenceDefinitions

  fibTotalMap : {P Q : Fam} (F : Map P Q) (x : B) (x' : Q x) → fiber (totalMap F) (x , x') ≡ fiber (F x) x'
  fibTotalMap {P = P} {Q = Q}  F y x =
    fiber (totalMap F) (y , x) ≡⟨ refl ⟩
    Σ (Σ B P) (λ (y' , x') → totalMap F (y' , x') ≡ (y , x)) ≡⟨ refl ⟩
    Σ (Σ B P) (λ (y' , x') → (y' , F y' x') ≡ (y , x)) ≡⟨ ua eq1 ⟩
    Σ B (λ y' → Σ (P y') (λ x' → (y' , F y' x' ) ≡ (y , x)))  ≡⟨ ua eq2 ⟩
    Σ B (λ y' → Σ (P y') (λ x' → Σ (y' ≡ y) (λ p → PathOver Q p (F y' x') x)))  ≡⟨ ua eq3 ⟩
    Σ B (λ y' → Σ (y' ≡ y) (λ p → Σ (P y') (λ x' → PathOver Q p (F y' x') x))) ≡⟨ ua eq4 ⟩
    Σ (Σ B (λ y' → y' ≡ y)) (λ (y' , p) → Σ (P y') (λ x' → PathOver Q p (F y' x') x)) ≡⟨ ua eq5 ⟩
    Σ (P y) (λ x' → F y x' ≡ x) ≡⟨ refl ⟩
    fiber (F y) x ∎
    where

    eq1 : Σ (Σ B P) (λ (y' , x') → (y' , F y' x') ≡ (y , x)) ≃ Σ B (λ y' → Σ (P y') (λ x' → (y' , F y' x' ) ≡ (y , x)))
    eq1 = isoToEquiv (f , (g ,((λ _ → refl) , λ _ → refl))) 
      where

      f : Σ (Σ B P) (λ (y' , x') → (y' , F y' x') ≡ (y , x)) → Σ B (λ y' → Σ (P y') (λ x' → (y' , F y' x' ) ≡ (y , x)))
      f ((b , pb) , p) = b , pb , p

      g :  Σ B (λ y' → Σ (P y') (λ x' → (y' , F y' x' ) ≡ (y , x))) → Σ (Σ B P) (λ (y' , x') → (y' , F y' x') ≡ (y , x))
      g (b , pb , p) = (b , pb) , p

    eq2 : Σ B (λ y' → Σ (P y') (λ x' → (y' , F y' x' ) ≡ (y , x))) ≃ Σ B (λ y' → Σ (P y') (λ x' → Σ (y' ≡ y) (λ p → PathOver Q p (F y' x') x)))
    eq2 = isoToEquiv (f , (g , (η , ϵ)))
      where

      f : Σ B (λ y' → Σ (P y') (λ x' → (y' , F y' x' ) ≡ (y , x))) → Σ B (λ y' → Σ (P y') (λ x' → Σ (y' ≡ y) (λ p → PathOver Q p (F y' x') x)))
      f (b , pb , refl) = b , pb , refl , refl

      g : Σ B (λ y' → Σ (P y') (λ x' → Σ (y' ≡ y) (λ p → PathOver Q p (F y' x') x))) → Σ B (λ y' → Σ (P y') (λ x' → (y' , F y' x' ) ≡ (y , x)))
      g (b , pb , p , q) = b , pb , Σ≡ p q

      η : g ∘ f ∼ id
      η (b , pb , refl) = refl

      ϵ : f ∘ g ∼ id
      ϵ (b , pb , refl , refl) = refl

    eq3 : Σ B (λ y' → Σ (P y') (λ x' → Σ (y' ≡ y) (λ p → PathOver Q p (F y' x') x))) ≃ Σ B (λ y' → Σ (y' ≡ y) (λ p → Σ (P y') (λ x' → PathOver Q p (F y' x') x)))
    eq3 = isoToEquiv (( λ (b , pb , p , q) → b , p , pb , q) ,
                      (λ (b , p , pb , q) → b , pb , p , q) ,
                      ((λ _ → refl) , λ _ → refl))

    eq4 : Σ B (λ y' → Σ (y' ≡ y) (λ p → Σ (P y') (λ x' → PathOver Q p (F y' x') x))) ≃ Σ (Σ B (λ y' → y' ≡ y)) (λ (y' , p) → Σ (P y') (λ x' → PathOver Q p (F y' x') x))
    eq4 = isoToEquiv ((λ (b , p , pb , q) → (b , p) , pb , q) ,
                       (λ ((b , p) , pb , q) → b , p , pb , q) ,
                       ((λ _ → refl) , λ _ → refl))

    eq5 : Σ (Σ B (λ y' → y' ≡ y)) (λ (y' , p) → Σ (P y') (λ x' → PathOver Q p (F y' x') x)) ≃ Σ (P y) (λ x' → F y x' ≡ x)
    eq5 = isoToEquiv (f , (g , (η , ϵ)))
      where

      f : Σ (Σ B (λ y' → y' ≡ y)) (λ (y' , p) → Σ (P y') (λ x' → PathOver Q p (F y' x') x)) → Σ (P y) (λ x' → F y x' ≡ x)
      f ((b , refl) , pb , q) = pb , q

      g : Σ (P y) (λ x' → F y x' ≡ x) → Σ (Σ B (λ y' → y' ≡ y)) (λ (y' , p) → Σ (P y') (λ x' → PathOver Q p (F y' x') x))
      g (pb , q) = (y , refl) , (pb , q)

      η : g ∘ f ∼ id
      η ((b , refl) , pb , q) = refl

      ϵ : f ∘ g ∼ id
      ϵ (pb , q) = refl
       

  fiberEquiv : {P Q : Fam} (F : Map P Q) → isEquiv (totalMap F) → (x : B) → isEquiv (F x)
  fiberEquiv F e x = hasContrFibers→isEquiv (F x) λ y → subst isContr (fibTotalMap F x y) (isEquiv→hasContrFibers ((totalMap F) , e) (x , y))

  totalMapEquiv : {P Q : Fam} (F : Map P Q) → ((x : B) → isEquiv (F x)) → isEquiv (totalMap F)
  totalMapEquiv F h = hasContrFibers→isEquiv (totalMap F) (λ x → subst isContr (sym (fibTotalMap F (x .fst) (x .snd ))) (isEquiv→hasContrFibers ((F (x .fst)) , (h (x .fst))) (x .snd)))


--- Part 4

  MapOver : Fib → Fib → Type ℓ
  MapOver (A , f)  (A' , f') = Σ (A → A') (λ g → (f' ∘ g ≡ f))

  -- mapEquiv : (P Q : Fam) → Map P Q ≃ MapOver (total P) (total Q)
  -- mapEquiv P Q = {!!}
  --   where
  --
  --   f : Map P Q → MapOver (total P) (total Q)
  --   f F = (totalMap F) , refl
  --
  --   g : MapOver (total P) (total Q) → Map P Q
  --   g (h , p) x px = subst Q pt (h (x , px) .snd)
  --     where
  --
  --     pt : fst (h (x , px)) ≡ x
  --     pt =
  --       fst (h (x , px))  ≡⟨ happly p ((x , px)) ⟩
  --       x ∎
  --
  --   η : g ∘ f ∼ id
  --   η F = refl
  --
  --   ϵ : f ∘ g ∼ id
  --   ϵ (h , p) = Σ≡ (funExt pt) pt'
  --     where
  --
  --     pt : (x : Σ B P) → totalMap (g (h , p)) x ≡ h x
  --     pt x =
  --       totalMap (g (h , p)) x ≡⟨ happly (cong totalMap refl) x ⟩
  --       totalMap (λ y py → subst Q (happly p (y , py)) (h (y , py) .snd) ) x ≡⟨ refl ⟩
  --       fst x , (subst Q (happly p x) (h x . snd)) ≡⟨ Σ≡ (sym (happly p x)) refl ⟩
  --       (fst (h x)) , subst Q (sym (happly p x))
  --                           (subst Q (happly p x) (h x .snd)) ≡⟨ Σ≡ refl (J (λ y p → subst Q (sym p) (subst Q p (h x .snd)) ≡ (h x .snd)) refl (happly p x)) ⟩
  --       h x ∎
  --
  --     pt' : PathOver (λ k → (λ x → fst (k x)) ≡ fst) (funExt pt) refl p
  --     pt' =
  --       subst (λ k → (fst ∘ k ) ≡ fst) (funExt pt) refl ≡⟨ {!!} ⟩
  --       {!!} ≡⟨ {!!} ⟩
  --       --- substInPathsL' (λ k → fst ∘ k) (funExt pt) refl ⟩
  --   ---    sym (cong (λ k → fst ∘ k) (funExt pt)) ∙ refl ≡⟨ sym (rUnit (sym (cong (λ k → fst ∘ k) (funExt pt)))) ⟩
  --   --- sym (cong (λ k → fst ∘ k) (funExt pt )) ≡⟨ sym (funExtη (sym (cong (λ k x → fst (k x)) (funExt pt)))) ⟩
  --   ---    funExt (happly (sym (cong (λ k x → fst (k x)) (funExt pt)))) ≡⟨ cong funExt (funExt (λ x → J (λ y q → {!!}) {!!} (happly p x)))  ⟩
  --       funExt (happly p) ≡⟨ funExtη p ⟩
  --       p ∎
