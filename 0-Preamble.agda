{-# OPTIONS --without-K #-}

module 0-Preamble where

open import Agda.Primitive public
  using (Level; lzero; lsuc; _⊔_)
  renaming (Set to U)

variable
  ℓ ℓ₁ ℓ₂ ℓ₃ : Level
  A B C : U ℓ
  P Q : A → U ℓ


