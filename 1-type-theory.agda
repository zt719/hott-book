module 1-Type-Theory where

open import 0-Preamble public

-- 1.1 Type theory versus set theory

-- 1.2 Function types

id : A → A
id x = x

const : A → B → A
const x y = x

infixr 9 _∘_
_∘_ : (B → C) → (A → B) → A → C
(f ∘ g) x = f (g x)

-- 1.3 Universes and families

-- 1.4 Depdendent function types (Π-types)

swap : {C : A → B → U ℓ}
  → ((a : A) (b : B) → C a b)
  → (b : B) (a : A) → C a b
swap g b a = g a b

-- 1.5 Product types

record 𝟙 : U where
  constructor *

rec𝟙 : (C : U ℓ) → C → 𝟙 → C
rec𝟙 C c * = c

ind𝟙 : (C : 𝟙 → U ℓ)
  → C * → (x : 𝟙) → C x
ind𝟙 C c * = c

-- 1.6 Dependent pair types (Σ-types)

infixr 4 _,_
record Σ (A : U ℓ₁) (B : A → U ℓ₂) : U (ℓ₁ ⊔ ℓ₂) where
  constructor _,_
  field
    pr₁ : A
    pr₂ : B pr₁
open Σ public
{-# BUILTIN SIGMA Σ #-}

infix 2 Σ-syntax
Σ-syntax : (A : U ℓ₁) → (A → U ℓ₂) → U (ℓ₁ ⊔ ℓ₂)
Σ-syntax = Σ
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

recΣ : {B : A → U ℓ₁} (C : U ℓ₂)
  → ((x : A) → B x → C) → Σ[ x ∈ A ] B x → C
recΣ C g (a , b) = g a b

indΣ : {B : A → U ℓ₁} (C : Σ[ x ∈ A ] B x → U ℓ₂)
  → ((a : A) (b : B a) → C (a , b)) → (p : Σ[ x ∈ A ] B x) → C p
indΣ C g (a , b) = g a b

ac : {R : A → B → U ℓ}
  → ((x : A) → Σ[ y ∈ B ] R x y)
  → Σ[ f ∈ (A → B) ] ((x : A) → R x (f x))
ac g = (λ x → pr₁ (g x)) , λ x → pr₂ (g x)

infixr 2 _×_
_×_ : (A : U ℓ₁) (B : U ℓ₂) → U (ℓ₁ ⊔ ℓ₂)
A × B = Σ[ x ∈ A ] B

rec× : (C : U ℓ) → (A → B → C)
  → A × B → C
rec× C g (a , b) = g a b

ind× : (C : A × B → U ℓ)
  → ((x : A) (y : B) → C (x , y))
  → (x : A × B) → C x
ind× C g (a , b) = g a b

Magma : U (lsuc ℓ)
Magma {ℓ} = Σ[ A ∈ U ℓ ] (A → A → A)

PointedMagma : U (lsuc ℓ)
PointedMagma {ℓ} = Σ[ A ∈ U ℓ ] ((A → A → A) × A)

-- 1.7 Coproduct types

infixr 1 _+_
data _+_ (A : U ℓ₁) (B : U ℓ₂) : U (ℓ₁ ⊔ ℓ₂) where
  inl : A → A + B
  inr : B → A + B

rec+ : (C : U ℓ) → (A → C) → (B → C)
  → A + B → C
rec+ C g₀ g₁ (inl a) = g₀ a
rec+ C g₀ g₁ (inr b) = g₁ b

ind+ : (C : A + B → U ℓ)
  → ((a : A) → C (inl a))
  → ((b : B) → C (inr b))
  → (x : A + B) → C x
ind+ C g₀ g₁ (inl a) = g₀ a
ind+ C g₀ g₁ (inr b) = g₁ b

data 𝟘 : U where

rec𝟘 : (C : U ℓ) → 𝟘 → C
rec𝟘 C ()

ind𝟘 : (C : 𝟘 → U ℓ) (z : 𝟘) → C z
ind𝟘 C ()

-- 1.8 The type of booleans

data 𝟚 : U where
  0₂ : 𝟚
  1₂ : 𝟚

rec𝟚 : (C : U ℓ)
  → C → C → 𝟚 → C
rec𝟚 C c₀ c₁ 0₂ = c₀
rec𝟚 C c₀ c₁ 1₂ = c₁

ind𝟚 : (C : 𝟚 → U ℓ)
  → C 0₂ → C 1₂ → (x : 𝟚) → C x
ind𝟚 C c₀ c₁ 0₂ = c₀
ind𝟚 C c₀ c₁ 1₂ = c₁

private
  _+′_ : (A B : U) → U
  A +′ B = Σ[ x ∈ 𝟚 ] rec𝟚 (U) A B x

  inl′ : A → A +′ B
  inl′ a = 0₂ , a

  inr′ : B → A +′ B
  inr′ b = 1₂ , b

  _×′_ : (A B : U) → U
  A ×′ B = (x : 𝟚) → rec𝟚 (U) A B x

  pr₁′ : A ×′ B → A
  pr₁′ p = p 0₂

  pr₂′ : A ×′ B → B
  pr₂′ p = p 1₂

-- 1.9 The natural numbers

data ℕ : U where
  zero : ℕ
  suc  : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

double : ℕ → ℕ
double zero = zero
double (suc n) = suc (suc (double n))

add : ℕ → ℕ → ℕ
add zero n = n
add (suc m) n = suc (add m n)

recℕ : (C : U ℓ)
  → C
  → (ℕ → C → C)
  → ℕ → C
recℕ C c₀ cs zero = c₀
recℕ C c₀ cs (suc n) = cs n (recℕ C c₀ cs n)

private 
  double′ : ℕ → ℕ
  double′ = recℕ ℕ zero (λ n y → suc (suc y))

  add′ : ℕ → ℕ → ℕ
  add′ = recℕ (ℕ → ℕ) (λ n → n) (λ m g n → suc (g n))

indℕ : (C : ℕ → U ℓ)
  → C zero
  → ((n : ℕ) → C n → C (suc n))
  → (n : ℕ) → C n
indℕ C c₀ cs zero = c₀
indℕ C c₀ cs (suc n) = cs n (indℕ C c₀ cs n)

-- 1.10 Pattern matching and recursion

-- 1.11 Proposition as types

infix 3 ¬_
¬_ : U ℓ → U ℓ
¬ A = A → 𝟘

deMor : ¬ A × ¬ B → ¬ (A + B)
deMor (¬A , ¬B) (inl A) = ¬A A
deMor (¬A , ¬B) (inr B) = ¬B B

-- 1.12 Identity types

infix 4 _≡_
data _≡_ {A : U ℓ} : A → A → U ℓ where
  refl : (a : A) → a ≡ a

ind≡ : (C : (x y : A) → x ≡ y → U ℓ)
  → (c : (x : A) → C x x (refl x))
  → (x y : A) (p : x ≡ y) → C x y p
ind≡ C c x .x (refl x) = c x

ind′≡ : (a : A)
  → (C : (x : A) → a ≡ x → U ℓ)
  → (c : C a (refl a))
  → (x : A) (p : a ≡ x) → C x p
ind′≡ a C c .a (refl a) = c

private
  ind≡′ : (C : (x y : A) → x ≡ y → U ℓ)
    → (c : (x : A) → C x x (refl x))
    → (x y : A) (p : x ≡ y) → C x y p
  ind≡′ C c x y p = ind′≡ x (C x) (c x) y p

  ind′≡′ : {A : U ℓ} (a : A)
    → (C : (x : A) → a ≡ x → U ℓ)
    → (c : C a (refl a))
    → (x : A) (p : a ≡ x) → C x p
  ind′≡′ {ℓ} {A} a C c x p = f a x p C c
    where
    D : (x y : A) → x ≡ y → U (lsuc ℓ)
    D x y p = (C : (z : A) → x ≡ z → U ℓ) → C x (refl x) → C y p

    d : (x : A) → D x x (refl x)
    d x C c = c

    f : (x y : A) (p : x ≡ y) → D x y p
    f x y p = ind≡ D d x y p

infix 4 _≢_
_≢_ : (A B : U ℓ) → U (lsuc ℓ)
A ≢ B = ¬ (A ≡ B)

uniq× : (x : A × B) → (pr₁ x , pr₂ x) ≡ x
uniq× (a , b) = refl (a , b)

uniq𝟙 : (x : 𝟙) → x ≡ *
uniq𝟙 * = refl *

private
  _≤_ : ℕ → ℕ → U
  n ≤ m = Σ[ k ∈ ℕ ] (add n k ≡ m)

  _<_ : ℕ → ℕ → U
  n < m = Σ[ k ∈ ℕ ] (add n (suc k) ≡ m)

  _<′_ : ℕ → ℕ → U
  n <′ m = n ≤ m × ¬ (n ≡ m)

Semigroup : U (lsuc ℓ)
Semigroup {ℓ} =
  Σ[ A ∈ U ℓ ] Σ[ m ∈ (A → A → A) ]
  ((x y z : A) → m x (m y z) ≡ m (m x y) z)

-- Exercises

data Fin : ℕ → U where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} → Fin n → Fin (suc n)


