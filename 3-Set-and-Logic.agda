module 3-Set-and-Logic where

open import 2-Homotopy-Type-Theory public
    
-- 3.1 Sets and n-types

isSet : U ℓ → U ℓ
isSet A = (x y : A) (p q : x ≡ y) → p ≡ q

𝟙-isSet : isSet 𝟙
𝟙-isSet * .* (refl *) (refl *) = refl (refl *)

𝟘-isSet : isSet 𝟘
𝟘-isSet ()

ℕ-isSet : isSet ℕ
ℕ-isSet zero zero (refl .zero) (refl .zero) = refl (refl zero)
ℕ-isSet (suc x) (suc .x) (refl .(suc x)) (refl .(suc x)) = refl (refl (suc x))

is-1-type : U ℓ → U ℓ
is-1-type A = (x y : A) (p q : x ≡ y) (r s : p ≡ q) → r ≡ s

lem-3-1-8 : isSet A → is-1-type A
lem-3-1-8 f x .x (refl .x) (refl .x) (refl .(refl x)) (refl .(refl x)) = refl (refl (refl x))

{-
U-isnotSet : ¬ (isSet U)
U-isnotSet x = {!!}
  where
  f : 𝟚 → 𝟚
  f 0₂ = 1₂
  f 1₂ = 0₂

  f-isequiv : isequiv f
  f-isequiv = f , (λ{ 0₂ → refl 0₂ ; 1₂ → refl 1₂}) , f , (λ{ 0₂ → refl 0₂ ; 1₂ → refl 1₂})

  p : 𝟚 ≡ 𝟚
  p = ua (f , f-isequiv)

  q : 𝟚 ≡ 𝟚
  q = refl 𝟚
-}

-- 3.2 Propositions as types?

-- 3.3 Mere propositions

isProp : U ℓ → U ℓ
isProp P = (x y : P) → x ≡ y

𝟘-isProp : isProp 𝟘
𝟘-isProp ()

𝟙-isProp : isProp 𝟙
𝟙-isProp * * = refl *

lem-3-3-2 : (P : U ℓ) → isProp P → (x₀ : P) → P ≃ 𝟙
lem-3-3-2 P P-isProp x₀ = f , g , (λ * → refl *) , g , (λ x → P-isProp (g (f x)) x)
  where
  f : P → 𝟙
  f x = *

  g : 𝟙 → P
  g * = x₀

lem-3-3-3 : (P : U ℓ₁) (Q : U ℓ₂) → isProp P → isProp Q
  → (P → Q) → (Q → P) → P ≃ Q
lem-3-3-3 P Q P-isProp Q-isProp f g
  = f , g , (λ y → Q-isProp (f (g y)) y) , g , (λ x → P-isProp (g (f x)) x)

{-
lem-3-3-4 : (A : U ℓ) → isProp A → isSet A
lem-3-3-4 A f x y p q = {!apd (x ≡_) g q!}
  where
  g : (y : A) → x ≡ y
  g y = f x y

  haha : (y z : A) (p : y ≡ z) → g y ∙ p ≡ g z
  haha y z p = {!lem-2-11-1-3 x (g y) p!}
-}

-- 3.4 Classical vs. intuitionistic logic

LEM = {ℓ : _} (A : U ℓ) → isProp A → A + ¬ A

LDN = {ℓ : _} (A : U ℓ) → isProp A → ¬ ¬ A → A

LEM∞ = {ℓ : _} (A : U ℓ) → A + ¬ A

is-decidable : (A : U ℓ) → U ℓ
is-decidable A = A + ¬ A

is-decidable-fam : {A : U ℓ₁} (P : A → U ℓ₂) → U (ℓ₁ ⊔ ℓ₂)
is-decidable-fam {A = A} P = (a : A) → P a + ¬ (P a)

is-decidable-eq : (A : U ℓ) → U ℓ
is-decidable-eq A = (a b : A) → a ≡ b + ¬ (a ≡ b)

-- 3.5 Subsets and propositional resizing

lem-3-5-1 : ((x : A) → isProp (P x)) → (u v : Σ[ x ∈ A ] P x) → pr₁ u ≡ pr₁ v → u ≡ v
lem-3-5-1 f (x , p) (x , q) (refl x) = pair≡ (refl x , f x p q)

SetU : (ℓ : _) → U (lsuc ℓ)
SetU ℓ = Σ[ A ∈ U ℓ ] isSet A

PropU : (ℓ : _) → U (lsuc ℓ)
PropU ℓ = Σ[ A ∈ U ℓ ] isProp A

{-
Set-suc : SetU ℓ → SetU (lsuc ℓ)
Set-suc (A , s) = {!A!} , {!!}
-}

∥_∥ : (A : U ℓ) → U ℓ
∥ A ∥ = A × {!???!}
