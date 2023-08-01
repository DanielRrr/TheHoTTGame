module 0Trinitarianism.Quest5 where

open import 0Trinitarianism.Preambles.P5

data S₁ : Type where
  base : S₁
  loop : base ≡ base
