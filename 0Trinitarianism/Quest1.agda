module 0Trinitarianism.Quest1 where

open import 0Trinitarianism.Preambles.P1

isEven : ℕ → Type
isEven zero = ⊤
isEven (suc zero) = ⊥
isEven (suc (suc n)) = isEven n

exEven : Σ ℕ isEven
exEven = 2 , tt

_×_ : Type → Type → Type
A × C = Σ A (λ a → C)

div2 : Σ ℕ isEven → ℕ
div2 (0 , p) = 0
div2 (suc (suc n) , p) = suc (div2 (n , p))
