module 0Trinitarianism.Quest3 where

open import 0Trinitarianism.Preambles.P3

_+_ : ℕ → ℕ → ℕ
n + zero = n
n + suc m = suc (n + m)

sumOfEvens : (n m : ℕ) → (p₁ : isEven n) → (p₂ : isEven m) → isEven (n + m)
sumOfEvens n zero p₁ p₂ = p₁
sumOfEvens n (suc (suc m)) p₁ p₂ = sumOfEvens n m p₁ p₂

data _⊕_ (A : Type) (B : Type) : Type where
  left : A → A ⊕ B
  right : B → A ⊕ B

¬ : Type → Type
¬ A = A → ⊥

_↔_ : Type → Type → Type
A ↔ B = (A → B) × (B → A)

fact : {A : Type} → (A ↔ ⊥) ↔ (A → ⊥)
fact = (λ p → fst p) , (λ p → p , λ ())

evenOrNot : (n : ℕ) → isEven n ⊕ ¬ (isEven n)
evenOrNot zero = left tt
evenOrNot (suc zero) = right λ ()
evenOrNot (suc (suc n)) = evenOrNot n
