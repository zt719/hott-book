module 2-Homotopy-Type-Theory where

open import 1-Type-Theory public

-- 2.1 Types are higher groupoids

sym : {x y : A} → x ≡ y → y ≡ x
sym (refl x) = refl x

infix 6 _⁻¹
_⁻¹ = sym

trans : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans (refl x) q = q

infixl 5 _∙_
_∙_ = trans

module ≡-Reasoning {A : U ℓ} where

  infix  1 begin_
  begin_ : {x y : A} → x ≡ y → x ≡ y
  begin x≡y  =  x≡y
  
  infixr 2 step-≡-∣
  step-≡-∣ : (x : A) {y : A} → x ≡ y → x ≡ y
  step-≡-∣ x x≡y  =  x≡y

  infixr 2 step-≡-⟩
  step-≡-⟩ : (x : A) {y z : A} → y ≡ z → x ≡ y → x ≡ z
  step-≡-⟩ x y≡z x≡y  =  trans x≡y y≡z

  syntax step-≡-∣ x x≡y      =  x ≡⟨⟩ x≡y
  syntax step-≡-⟩ x y≡z x≡y  =  x ≡⟨  x≡y ⟩ y≡z

  infix  3 _∎
  _∎ : (x : A) → x ≡ x
  x ∎ = refl x

open ≡-Reasoning

idr : {x y : A} (p : x ≡ y) → p ≡ p ∙ (refl y)
idr (refl x) = refl (refl x)

idl : {x y : A} (p : x ≡ y) → p ≡ (refl x) ∙ p
idl (refl x) = refl (refl x)

invo : {x y : A} (p : x ≡ y) → (p ⁻¹) ⁻¹ ≡ p
invo (refl x) = refl (refl x)

assoc : {x y z m : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ m) → p ∙ (q ∙ r) ≡ (p ∙ q) ∙ r
assoc (refl x) q r = refl (q ∙ r)

Ω : (A : U ℓ) (a : A) → U ℓ
Ω A a = a ≡ a

_Ω×_ : {A : U ℓ} {a : A} → Ω A a → Ω A a → Ω A a
_Ω×_ = trans

Ω² : (A : U ℓ) (a : A) → U ℓ
Ω² A a = Ω (Ω A a) (refl a)

_Ω²×_ : {A : U ℓ} {a : A} → Ω² A a → Ω² A a → Ω² A a
_Ω²×_ = _Ω×_

thm2-1-6 : {A : U ℓ} {a : A} (α β : Ω² A a) → α Ω²× β ≡ β Ω²× α
thm2-1-6 (refl (refl a)) (refl .(refl a)) = refl (refl (refl a))

U∙ : U (lsuc ℓ)
U∙ {ℓ} = Σ[ A ∈ U ℓ ] A 

Ω⁰ : (A : U ℓ) (a : A) → U∙
Ω⁰ A a = (a ≡ a) , refl a

Ωⁿ : ℕ → U∙ {ℓ} → U∙ {ℓ}
Ωⁿ zero (A , a) = Ω⁰ A a
Ωⁿ (suc n) (A , a) = Ωⁿ n (Ω⁰ A a)

-- 2.2 Functions are functors

ap : (f : A → B) {x y : A} (p : x ≡ y) → f x ≡ f y
ap f (refl x) = refl (f x)

ap-trans : (f : A → B) {x y z : A} (p : x ≡ y) (q : y ≡ z) → ap f (p ∙ q) ≡ ap f p ∙ ap f q
ap-trans f (refl x) q = refl (ap f q)

ap-sym : (f : A → B) {x y : A} (p : x ≡ y) → ap f (p ⁻¹) ≡ (ap f p) ⁻¹
ap-sym f (refl x) = refl (refl (f x))

ap-∘ : (f : A → B) (g : B → C) {x y : A} (p : x ≡ y) → ap g (ap f p) ≡ ap (g ∘ f) p
ap-∘ f g (refl x) = refl (refl ((g ∘ f) x))

ap-id : {x y : A} (p : x ≡ y) → ap id p ≡ p
ap-id (refl x) = refl (refl x)

-- 2.3 Type families are fibrations

tr : (P : A → U ℓ) {x y : A} → x ≡ y → P x → P y
tr P (refl a) u = u

lift : (P : A → U ℓ) {x y : A} (u : P x) (p : x ≡ y) → (x , u) ≡ (y , tr P p u)
lift P u (refl x) = refl (x , u)

apd : (P : A → U ℓ) (f : (x : A) → P x) {x y : A} (p : x ≡ y) → tr P p (f x) ≡ f y
apd P f (refl x) = refl (f x)

tr-const : (B : U ℓ) {x y : A} (p : x ≡ y) (b : B) → tr (const B) p b ≡ b
tr-const B (refl x) b = refl b

lem2-3-8 : (f : A → B) {x y : A} (p : x ≡ y) → apd (const B) f p ≡ tr-const B p (f x) ∙ ap f p
lem2-3-8 f (refl x) = refl (refl (f x))

lem2-3-9 : (P : A → U ℓ) {x y z : A} (u : P x) (p : x ≡ y) (q : y ≡ z) → tr P q (tr P p u) ≡ tr P (p ∙ q) u
lem2-3-9 P u (refl x) q = refl (tr P q u)

lem2-3-10 : (f : A → B) (P : B → U ℓ) {x y : A} (p : x ≡ y) (u : P (f x)) → tr (P ∘ f) p u ≡ tr P (ap f p) u
lem2-3-10 f P (refl x) u = refl u

lem2-3-11 : (P Q : A → U ℓ) (f : (x : A) → P x → Q x) {x y : A} (p : x ≡ y) (u : P x) → tr Q p (f x u) ≡ f y (tr P p u)
lem2-3-11 P Q f (refl x) u = refl (f x u)

-- 2.4 Homotopies and equivalences

_~_ : {A : U ℓ₁} {P : A → U ℓ₂} (f g : (x : A) → P x) → U (ℓ₁ ⊔ ℓ₂)
f ~ g = (x : _) → f x ≡ g x

~refl : {f : (x : A) → P x} → f ~ f
~refl {f = f} x = refl (f x)

~sym : {f g : (x : A) → P x} → f ~ g → g ~ f
~sym H x = sym (H x)

~trans : {f g h : (x : A) → P x} → f ~ g → g ~ h → f ~ h
~trans H J x = trans (H x) (J x)

~nat : {f g : A → B} (H : f ~ g) {x y : A} (p : x ≡ y) → H x ∙ ap g p ≡ ap f p ∙ H y
~nat H (refl x) = (idr (H x)) ⁻¹

left-unwhisk : {x y z : A} (p : x ≡ y) {q r : y ≡ z}
  → p ∙ q ≡ p ∙ r → q ≡ r
left-unwhisk (refl x) s = s

right-unwhisk : {x y z : A} {p q : x ≡ y} (r : y ≡ z)
  → p ∙ r ≡ q ∙ r → p ≡ q
right-unwhisk {p = p} {q} (refl x) s = (idr p) ∙ s ∙ (idr q) ⁻¹ 

cor2-4-4 : {A : U} (f : A → A) (H : f ~ id) (x : A) → H (f x) ≡ ap f (H x)
cor2-4-4 f H x = right-unwhisk (H x) aux
  where
  aux : H (f x) ∙ H x ≡ ap f (H x) ∙ H x
  aux =
    begin
      H (f x) ∙ H x
    ≡⟨ ap (H (f x) ∙_) (sym (ap-id (H x))) ⟩
      H (f x) ∙ ap id (H x)
    ≡⟨ ~nat H (H x) ⟩
      ap f (H x) ∙ H (id x)
    ≡⟨⟩
      ap f (H x) ∙ H x
    ∎

qinv : {A : U ℓ₁} {B : U ℓ₂} (f : A → B) → U (ℓ₁ ⊔ ℓ₂)
qinv f = Σ[ g ∈ _ ] (f ∘ g) ~ id × (g ∘ f) ~ id

isequiv : {A : U ℓ₁} {B : U ℓ₂} (f : A → B) → U (ℓ₁ ⊔ ℓ₂)
isequiv f = Σ[ g ∈ _ ] (f ∘ g) ~ id × Σ[ h ∈ _ ] (h ∘ f)~ id

qinv→isequiv : {f : A → B} → qinv f → isequiv f
qinv→isequiv (g , α , β) = g , α , g , β

isequiv→qinv : {f : A → B} → isequiv f → qinv f
isequiv→qinv {f = f} (g , α , h , β) = g , α , β′
  where
  γ : g ~ h
  γ x = sym (β (g x)) ∙ ap h (α x)

  β′ : (g ∘ f) ~ id
  β′ x = γ (f x) ∙ β x

_≃_ : U ℓ₁ → U ℓ₂ → U (ℓ₁ ⊔ ℓ₂)
A ≃ B = Σ[ f ∈ (A → B) ] isequiv f

_≃′_ : U ℓ₁ → U ℓ₂ → U (ℓ₁ ⊔ ℓ₂)
A ≃′ B = Σ[ f ∈ (A → B) ] qinv f

≃→≃′ : A ≃ B → A ≃′ B
≃→≃′ (f , f-isequiv) = f , isequiv→qinv f-isequiv

≃′→≃ : A ≃′ B → A ≃ B
≃′→≃ (f , f-qinv) = f , qinv→isequiv f-qinv

≃′refl : (A : U ℓ) → A ≃′ A
≃′refl A = id , id , refl , refl

≃refl : (A : U ℓ) → A ≃ A
≃refl A = ≃′→≃ (≃′refl A)

≃′sym : {A B : U ℓ} → A ≃′ B → B ≃′ A
≃′sym (f , g , α , β) = g , f , β , α

≃sym : {A B : U ℓ} → A ≃ B → B ≃ A
≃sym f = ≃′→≃ (≃′sym (≃→≃′ f))

postulate
  ≃′trans : {A B C : U ℓ} → A ≃′ B → B ≃′ C → A ≃′ C
{-  
≃′trans (f₁ , g₁ , α₁ , β₁) (f₂ , g₂ , α₂ , β₂)
  = f₂ ∘ f₁ , g₁ ∘ g₂ , {!!} , {!!}
-}

≃trans : {A B C : U ℓ} → A ≃ B → B ≃ C → A ≃ C
≃trans f g = ≃′→≃ (≃′trans (≃→≃′ f) (≃→≃′ g))

-- 2.5 The higher groupoid structure of type formers

-- 2.6 Cartesian product types

thm-2-6-2 : {x y : A × B} → (x ≡ y) ≃ ((pr₁ x ≡ pr₁ y) × (pr₂ x ≡ pr₂ y))
thm-2-6-2 {x = x} {y} = f , g , α , g , β
  where
  f : x ≡ y → pr₁ x ≡ pr₁ y × pr₂ x ≡ pr₂ y
  f (refl x) = refl (pr₁ x) , refl (pr₂ x)

  g : pr₁ x ≡ pr₁ y × pr₂ x ≡ pr₂ y → x ≡ y
  g (refl x , refl y) = refl (x , y)

  α : (f ∘ g) ~ id
  α (refl a , refl b) = refl (refl a , refl b)

  β : (g ∘ f) ~ id
  β (refl (p , q)) = refl (refl (p , q))

pair≡′ : {x y : A × B} → pr₁ x ≡ pr₁ y × pr₂ x ≡ pr₂ y → x ≡ y
pair≡′ (refl x , refl y) = refl (x , y)

private
  _×′_ : (P : A → U ℓ₁) (Q : A → U ℓ₂) → A → U (ℓ₁ ⊔ ℓ₂)
  (P ×′ Q) x = P x × Q x

thm-2-6-4 : {A : U ℓ} {P : A → U ℓ₁} {Q : A → U ℓ₂} {x y : A} (p : x ≡ y) (u : (P ×′ Q) x) → tr (P ×′ Q) p u ≡ (tr P p (pr₁ u) , tr Q p (pr₂ u))
thm-2-6-4 (refl x) u = refl u

thm-2-6-5 : {A A′ B B′ : U ℓ}
  → (g : A → A′) (h : B → B′)
  → let f : A × B → A′ × B′
        f x = g (pr₁ x) , h (pr₂ x)
    in
  {x y : A × B} (p : pr₁ x ≡ pr₁ y) (q : pr₂ x ≡ pr₂ y) → ap f (pair≡′ (p , q)) ≡ pair≡′ (ap g p , ap h q) 
thm-2-6-5 g h (refl a) (refl b) = refl (refl (g a , h b))

-- 2.7 Σ-types

thm-2-7-2 : {A : U ℓ₁} {P : A → U ℓ₂} {w w′ : Σ[ x ∈ A ] P x} → (w ≡ w′) ≃ (Σ[ p ∈ pr₁ w ≡ pr₁ w′ ] tr P p (pr₂ w) ≡ pr₂ w′)
thm-2-7-2 {A = A} {P} {w} {w′} = f , g , α , g , β
  where
  f : w ≡ w′ → Σ[ p ∈ pr₁ w ≡ pr₁ w′ ] tr P p (pr₂ w) ≡ pr₂ w′
  f (refl w) = refl (pr₁ w) , refl (pr₂ w)

  g : Σ[ p ∈ pr₁ w ≡ pr₁ w′ ] tr P p (pr₂ w) ≡ pr₂ w′ → w ≡ w′
  g (refl a , refl b) = refl (a , b)

  α : (f ∘ g) ~ id
  α (refl a , refl b) = refl (refl a , refl b)

  β : (g ∘ f) ~ id
  β (refl w) = refl (refl w)

cor-2-7-3 : {A : U ℓ₁} {P : A → U ℓ₂} (z : Σ[ x ∈ A ] P x) → z ≡ (pr₁ z , pr₂ z)
cor-2-7-3 z = refl z

pair≡ : {w w′ : Σ[ x ∈ A ] P x} → Σ[ p ∈ pr₁ w ≡ pr₁ w′ ] tr P p (pr₂ w) ≡ pr₂ w′ → w ≡ w′
pair≡ {P = P} {w = w} (p , refl .(tr P p (pr₂ w))) = lift P (pr₂ w) p

thm-2-7-4 : (P : A → U ℓ₁) (Q : Σ[ x ∈ A ] P x → U ℓ₂)
  → let PQ : A → U (ℓ₁ ⊔ ℓ₂)
        PQ x = Σ[ u ∈ P x ] Q (x , u)
    in {x y : A} (p : x ≡ y) (uz : Σ[ u ∈ P x ] Q (x , u))
  → tr PQ p uz ≡ (tr P p (pr₁ uz) , tr Q (pair≡ (p , refl (tr P p (pr₁ uz)))) (pr₂ uz))
thm-2-7-4 P Q (refl x) uz = refl uz

-- 2.8 The unit type

thm-2-8-1 : {x y : 𝟙} → (x ≡ y) ≃ 𝟙
thm-2-8-1 {x} {y} = f , g , α , g , β
  where
  f : x ≡ y → 𝟙
  f p = *

  g : 𝟙 → x ≡ y
  g * = refl *

  α : (f ∘ g) ~ id
  α * = refl *

  β : (g ∘ f) ~ id
  β (refl *) = refl (refl *)

-- 2.9 Π-types & function extensionality

private variable
  f g h : (x : A) → P x

happly : f ≡ g → (x : A) → f x ≡ g x
happly (refl f) x = refl (f x)

postulate
  funext : ((x : A) → f x ≡ g x) → f ≡ g
  happly-funext : (h : (x : A) → f x ≡ g x) (x : A) → happly (funext h) x ≡ h x
  funext-happly : (p : f ≡ g) (x : A) → p ≡ funext (λ x → happly p x)

f-refl : (f : (x : A) → P x) → f ≡ f
f-refl f = funext (λ x → refl (f x))

f-sym : f ≡ g → g ≡ f
f-sym α = funext (λ x → sym (happly α x))

f-trans : f ≡ g → g ≡ h → f ≡ h
f-trans α β = funext (λ x → trans (happly α x) (happly β x))

private
  _→′_ : (P : A → U ℓ₁) (Q : A → U ℓ₂) → A → U (ℓ₁ ⊔ ℓ₂)
  (P →′ Q) x = P x → Q x

thm-2-9-4 : (P : A → U ℓ₁) (Q : A → U ℓ₂) {x y : A} (p : x ≡ y) (f : P x → Q x) → tr (P →′ Q) p f ≡ λ u → tr Q p (f (tr P (p ⁻¹) u))
thm-2-9-4 P Q (refl x) f = refl f

private
  Π : (P : A → U ℓ₁) (Q : (x : A) → P x → U ℓ₂)
    → A → U (ℓ₁ ⊔ ℓ₂)
  Π P Q x = (u : P x) → Q x u

  ^ : {A : U ℓ} {P : A → U ℓ₁} (Q : (x : A) → P x → U ℓ₂)
    → Σ[ x ∈ A ] P x → U ℓ₂
  ^ Q w = Q (pr₁ w) (pr₂ w)

thm-2-9-5 : (P : A → U ℓ₁) (Q : (x : A) → P x → U ℓ₂) {x y : A} (p : x ≡ y) (f : (u : P x) → Q x u) (u : P y) 
  → tr (Π P Q) p f u ≡ tr (^ Q) ((pair≡ (p ⁻¹ , refl (tr P (p ⁻¹) u))) ⁻¹) (f (tr P (p ⁻¹) u)) 
thm-2-9-5 P Q (refl x) f u = refl (f u)

{-
thm-2-9-6 : (P : A → U ℓ) (Q : A → U ℓ) {x y : A} (p : x ≡ y) (f : P x → Q x) (g : P y → Q y)
  → (tr (λ z → P z → Q z) p f ≡ g) ≃ ((u : P x) → tr Q p (f u) ≡ g (tr P p u))
thm-2-9-6 P Q (refl x) f g = happly , funext , {!!} , {!!}

thm-2-9-7 :
-}

-- 2.10 Universes and the univalence axiom

idtoeqv : A ≡ B → A ≃ B
idtoeqv (refl A) = ≃refl A

postulate
  ua : {A B : U ℓ} → A ≃ B → A ≡ B

-- 2.11 Identity type

{-
thm-2-11-1 : (f : A → B) → isequiv f
  → {x y : A} → isequiv (ap f {x} {y})
thm-2-11-1 {A = A} {B = B} f f-isequiv {x} {y} = qinv→isequiv (apf⁻¹ , {!!} , {!!})
  where
  f-qinv : qinv f
  f-qinv = isequiv→qinv f-isequiv

  f⁻¹ : B → A
  f⁻¹ = pr₁ f-qinv

  α : (f ∘ f⁻¹) ~ id 
  α = pr₁ (pr₂ f-qinv)

  β : (f⁻¹ ∘ f) ~ id
  β = pr₂ (pr₂ f-qinv)
  
  apf⁻¹ : f x ≡ f y → x ≡ y
  apf⁻¹ fp =
    begin
      x
    ≡⟨ sym (β x) ⟩
      f⁻¹ (f x)
    ≡⟨ ap f⁻¹ fp ⟩
      f⁻¹ (f y)
    ≡⟨ β y ⟩
      y
    ∎
-}
  
lem-2-11-1-1 : (a : A) {x y : A} (p : x ≡ y) (q : a ≡ x)
  → tr (a ≡_) p q ≡ q ∙ p
lem-2-11-1-1 a (refl x) q = idr q

lem-2-11-1-2 : (a : A) {x y : A} (p : x ≡ y) (q : x ≡ a)
  → tr (_≡ a) p q ≡ (p ⁻¹) ∙ q
lem-2-11-1-2 a (refl x) q = idl q

lem-2-11-1-3 : (a : A) {x y : A} (p : x ≡ y) (q : x ≡ x)
  → tr (λ x → x ≡ x) p q ≡ p ⁻¹ ∙ q ∙ p
lem-2-11-1-3 a (refl x) q = idr q
  
-- 2.13 Natural numbers

code : ℕ → ℕ → U
code zero zero = 𝟙
code zero (suc n) = 𝟘
code (suc m) zero = 𝟘
code (suc m) (suc n) = code m n

dp-ℕ : (n : ℕ) → code n n
dp-ℕ zero = *
dp-ℕ (suc n) = dp-ℕ n

{-
≡≃code : {m n : ℕ} → (m ≡ n) ≃ code m n
≡≃code {m} = encode , decode , α {m} , decode , β
  where
  encode : {m n : ℕ} → m ≡ n → code m n
  encode {m} p = tr (code m) p (dp-ℕ m)

  decode : {m n : ℕ} → code m n → m ≡ n
  decode {zero} {zero} = λ _ → refl
  decode {zero} {suc n} = λ ()
  decode {suc m} {zero} = λ ()
  decode {suc m} {suc n} = ap suc ∘ decode {m} {n}

  β : {m n : ℕ} (p : m ≡ n) → decode (encode p) ≡ p
  β {zero} {.zero} refl = refl
  β {suc m} {.(suc m)} refl = ap (ap suc) (β refl)

  α : {m n : ℕ} (c : code m n) → encode {m} (decode c) ≡ c
  α {zero} {zero} * = refl
  α {suc m} {suc n} c = {!!}
-}
