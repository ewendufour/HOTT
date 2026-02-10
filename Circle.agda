{-# OPTIONS --without-K --rewriting #-}

open import Prelude
open import Path
open import HLevels
open import Equivalence
open import EquivalenceDefinitions
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
rev = Circle-rec base (sym loop)

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

rev² : rev ∘ rev ≡ id
rev² = funExt (Circle-ind (λ z → (rev ∘ rev) z ≡ id z) refl p)
  where

  p : PathOver (λ z → rev (rev z) ≡ z) loop refl refl
  p =
    subst (λ z → rev (rev z) ≡ z) loop refl ≡⟨ substInPaths (rev ∘ rev) id loop refl ⟩
    sym (cong (λ x → rev (rev x)) loop) ∙ refl ∙ cong id loop ≡⟨ cong (λ z → sym (cong (λ x → rev (rev x)) loop) ∙ refl ∙ z) (congId loop) ⟩
    sym (cong (Circle-rec base (sym loop) ∘ Circle-rec base (sym loop)) loop) ∙ loop ≡⟨ cong (λ z → sym z ∙ loop) (cong∘ (Circle-rec base (sym loop)) (Circle-rec base (sym loop)) loop) ⟩
    sym (cong (Circle-rec base (sym loop)) (cong (Circle-rec base (sym loop)) loop)) ∙ loop ≡⟨ cong (λ z → sym (cong (Circle-rec base (sym loop)) z) ∙ loop) (Circle-comp-loop-nd base (sym loop)) ⟩
    sym (cong (Circle-rec base (sym loop)) (sym loop)) ∙ loop ≡⟨ cong (λ z → sym z ∙ loop) (congSym (Circle-rec base (sym loop)) loop) ⟩
    sym (sym (cong (Circle-rec base (sym loop)) loop)) ∙ loop ≡⟨ cong (λ z → sym (sym z) ∙ loop) (Circle-comp-loop-nd base (sym loop)) ⟩
    sym (sym (sym loop)) ∙ loop ≡⟨ cong (λ z → z ∙ loop) (sym (symInvo (sym loop))) ⟩
    sym loop ∙ loop ≡⟨ lCancel loop ⟩
    refl ∎
  
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

Circle-unique :
    {A : Type ℓ}
    (f g : Circle → A)
    (p : f base ≡ g base)
    (q : PathOver (λ x → x ≡ x) p (cong f loop) (cong g loop))
    (x : Circle) → f x ≡ g x
Circle-unique f g p q = Circle-ind (λ x → f x ≡ g x) p path
  where

  path : PathOver (λ z → f z ≡ g z) loop p p
  path =
    subst (λ z → f z ≡ g z) loop p ≡⟨ substInPaths f g loop p ⟩
    sym (cong f loop) ∙ p ∙ cong g loop ≡⟨ cong (λ z → sym (cong f loop) ∙ z ∙ cong g loop) (symInvo p) ⟩
    sym (cong f loop) ∙ sym (sym p) ∙ cong g loop ≡⟨ sym (assoc (sym (cong f loop)) (sym (sym p)) (cong g loop)) ⟩
    (sym (cong f loop) ∙ sym (sym p)) ∙ cong g loop ≡⟨ cong (λ z → z ∙ cong g loop) (sym (symDist (sym p) (cong f loop))) ⟩
    sym (sym p ∙ cong f loop) ∙ cong g loop ≡⟨ cong (λ z → sym (sym z ∙ cong f loop) ∙ cong g loop) (sym (congId p)) ⟩
    sym (sym (cong id p) ∙ cong f loop) ∙ cong g loop ≡⟨ rotate∙≡ (sym (cong id p) ∙ cong f loop) (cong id p) (cong g loop) path' ⟩
    cong id p ≡⟨ congId p ⟩
    p ∎
    where

    
    path' : (sym (cong id p) ∙  cong f loop) ∙ cong id p ≡ cong g loop
    path' =
      (sym (cong id p) ∙ cong f loop) ∙ cong id p ≡⟨ assoc (sym (cong id p)) (cong f loop) (cong id p) ⟩
      sym (cong id p) ∙ cong f loop ∙ cong id p ≡⟨ sym (substInPaths id id p (cong f loop)) ⟩
      subst (λ x → x ≡ x) p (cong f loop) ≡⟨ q ⟩
      cong g loop ∎



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

pred≃ : ℤ ≃ ℤ
pred≃ = isoToEquiv (f , (g , (η , ϵ)))
  where

  g : ℤ → ℤ
  g = sucℤ

  f : ℤ → ℤ
  f = predℤ

  η : g ∘ f ∼ id
  η (negsuc n) = refl
  η (pos zero) = refl
  η (pos (suc n)) = refl

  ϵ : f ∘ g ∼ id
  ϵ (negsuc zero) = refl
  ϵ (negsuc (suc n)) = refl
  ϵ (pos n) = refl

pred≡ : ℤ ≡ ℤ
pred≡ = ua pred≃


loops : ℤ → base ≡ base
loops (pos zero) = refl
loops (pos (suc n)) = loops (pos n) ∙ loop 
loops (negsuc zero) = sym loop
loops (negsuc (suc n)) = loops (negsuc n) ∙ sym loop

code : Circle → Type
code = Circle-rec ℤ suc≡

encode : (x : Circle) → base ≡ x → code x
encode x p = subst code p (pos zero)

substLoop : (n : ℤ) → subst code loop n ≡ sucℤ n
substLoop n  =
  subst code loop n ≡⟨ substComp code id loop n ⟩
  subst id (cong code loop) n ≡⟨ cong (λ z → subst id z n) (Circle-comp-loop-nd ℤ suc≡) ⟩
  subst id suc≡ n ≡⟨ cong (λ z → z n) (uaβ suc≃) ⟩ 
  sucℤ n ∎


symEquiv : {A : Type ℓ} {B : Type ℓ} (e : A ≃ B) → sym (ua e) ≡ ua (invEquiv e)
symEquiv e = ≃ind (λ z → sym (ua z) ≡ ua (invEquiv z)) ideq e
  where

  ideq : {A : Type ℓ} → sym (ua {A = A}idEquiv) ≡ ua (invEquiv idEquiv)
  ideq =
    sym (ua idEquiv) ≡⟨ cong sym uaIdEquiv ⟩
    refl ≡⟨ sym uaIdEquiv ⟩
    ua idEquiv ≡⟨ cong ua refl ⟩
    ua (invEquiv idEquiv) ∎
 
substSymLoop : (n : ℤ) → subst code (sym loop) n ≡ predℤ n
substSymLoop n =
  subst code (sym loop) n ≡⟨ substComp code id (sym loop) n  ⟩
  subst id (cong code (sym loop)) n ≡⟨ cong (λ z → subst id z n) (congSym code loop) ⟩
  subst id (sym (cong code loop)) n ≡⟨ cong (λ z → subst id (sym z) n) (Circle-comp-loop-nd ℤ suc≡) ⟩
  subst id (sym suc≡) n  ≡⟨ cong (λ z → subst id z n) (symEquiv suc≃) ⟩
  subst id (ua (invEquiv suc≃)) n ≡⟨ cong (λ z → z n) (uaβ (invEquiv suc≃)) ⟩
  predℤ n ∎

substLoops : (m n : ℤ) → subst code (loops m) n ≡ m + n
substLoops (pos zero) n = refl
substLoops (pos (suc m)) n =
  subst code (loops (pos m) ∙ loop) n ≡⟨ substComposite code (loops (pos m)) loop n ⟩
  subst code loop (subst code (loops (pos m)) n) ≡⟨ substLoop (subst code (loops (pos m)) n) ⟩
  sucℤ (subst code (loops (pos m)) n) ≡⟨ cong sucℤ (substLoops (pos m) n) ⟩
  (pos (suc m) + n) ∎
substLoops (negsuc zero) n = substSymLoop n
substLoops (negsuc (suc m)) n =
  subst code (loops (negsuc m) ∙ sym loop) n ≡⟨ substComposite code (loops (negsuc m)) (sym loop) n ⟩
  subst code (sym loop) (subst code (loops (negsuc m)) n) ≡⟨ cong (subst code (sym loop)) (substLoops (negsuc m) n) ⟩
  subst code (sym loop) (negsuc m + n) ≡⟨ substSymLoop (negsuc m + n) ⟩
  (negsuc (suc m) + n) ∎


substLoopLoops : subst (λ x → code x → base ≡ x) loop loops ≡ loops
substLoopLoops =
  subst (λ x → code x → base ≡ x) loop loops ≡⟨ funTypeTransp code (λ x → base ≡ x) loop loops ⟩
  subst (λ z → base ≡ z) loop ∘ loops ∘ (subst code (sym loop)) ≡⟨ funExt (λ y → cong (λ t → subst (λ z → base ≡ z) loop (loops t)) (substSymLoop y)) ⟩
  subst (λ x → base ≡ x) loop ∘ loops ∘ predℤ ≡⟨ funExt (λ z → substInPathsR (loops (predℤ z)) loop) ⟩
  (λ z → loops (predℤ z) ∙ loop) ≡⟨ funExt p ⟩
  loops ∎

  where

  p : (z : ℤ) → loops (predℤ z) ∙ loop ≡ loops z
  p (pos zero) = lCancel loop
  p (pos (suc n)) = refl 
  p (negsuc zero) =
    (sym loop ∙ sym loop) ∙ loop ≡⟨ assoc (sym loop) (sym loop) loop ⟩
    sym loop ∙ (sym loop ∙ loop) ≡⟨ cong (λ z → (sym loop) ∙ z) (lCancel loop) ⟩
    sym loop ∙ refl ≡⟨ sym (rUnit (sym loop)) ⟩
    sym loop ∎
  p (negsuc (suc n)) =
    loops (predℤ (negsuc (suc n))) ∙ loop ≡⟨ assoc ((loops (negsuc n)) ∙ (sym loop)) (sym loop) loop ⟩
    (loops (negsuc n) ∙ sym loop) ∙ sym loop ∙ loop ≡⟨ cong (λ z → (loops (negsuc n) ∙ sym loop) ∙ z) (lCancel loop) ⟩
    trans (loops (negsuc n)) (sym loop) ∙ refl ≡⟨ sym (rUnit (loops (negsuc (suc n)))) ⟩
    loops (negsuc (suc n)) ∎

decode : (x : Circle) → code x → base ≡ x
decode = Circle-ind (λ x → code x → base ≡ x) loops substLoopLoops
  
decodeEncode : (x : Circle) (p : base ≡ x) → decode x (encode x p) ≡ p
decodeEncode x refl = refl

encodeDecode : (x : Circle) (n : code x) → encode x (decode x n) ≡ n
encodeDecode = Circle-ind (λ x → (n : code x) → encode x (decode x n) ≡ n) bcase
               (funExt (λ z → isSetℤ (encode base (decode base z))
               z
               (subst (λ x → (n : code x) → encode x (decode x n) ≡ n) loop bcase z)
               (bcase z)))
  where

  bcase : (n : code base) → encode base (decode base n) ≡ n
  bcase n =
    subst code (loops n) (pos zero) ≡⟨ substLoops n (pos zero) ⟩
    (n + (pos zero)) ≡⟨ addZero n ⟩
    n ∎

loopEquiv : (x : Circle) → (base ≡ x) ≃ code x
loopEquiv x = isoToEquiv ((encode x) , (decode x , (decodeEncode x) , (encodeDecode x)))

loopCircle : (base ≡ base) ≃ ℤ
loopCircle = loopEquiv base

--- Part 3


open import Truncation

isConnectedCircle' : (x : Circle) → ∥ base ≡ x ∥₁
isConnectedCircle' = Circle-ind (λ z → ∥ base ≡ z ∥₁) ∣ loop ∣₁ (isPropPropTrunc (subst (λ z → ∥ base ≡ z ∥₁) loop ∣ loop ∣₁) ∣ loop ∣₁)

isConnectedCircle : isConnected Circle
isConnectedCircle = ∣ base ∣₁ ,
                    Circle-ind (λ z → (y : Circle) → ∥ z ≡ y ∥₁)
                               isConnectedCircle'
                               (isPropΠ (λ z → ∥ base ≡ z ∥₁)
                                        (λ x → isPropPropTrunc)
                                        (subst (λ z → (y : Circle) → ∥ z ≡ y ∥₁)
                                               loop isConnectedCircle')
                                        isConnectedCircle')


isGroupoidCircle : isGroupoid Circle
isGroupoidCircle x y =
  propTrunc-rec isPropIsSet
                (λ p → propTrunc-rec isPropIsSet
                                     (λ q → f p q)
                                     (isConnectedCircle .snd base y))
                (isConnectedCircle .snd base x)
  where
  
  pathInCircle≡ls : {x y : Circle} → (x ≡ base) → (y ≡ base) → ((x ≡ y) ≡ (base ≡ base))
  pathInCircle≡ls {x = x} {y = y} refl refl = refl

  f : (p : base ≡ x) (q : base ≡ y) → isSet (x ≡ y)
  f p q = subst isSet (sym (pathInCircle≡ls (sym p) (sym q) ∙ ua loopCircle)) isSetℤ
  
  
