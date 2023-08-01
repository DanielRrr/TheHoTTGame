-- ignore
module 1FundamentalGroup.Quest2 where
open import 1FundamentalGroup.Preambles.P2

isSet→LoopSpace≅⊤ : {A : Type} (x : A) → isSet A → (x ≡ x) ≅ ⊤
isSet→LoopSpace≅⊤ x h = iso (λ _ → tt) inv l r where
  f : x ≡ x → ⊤
  f p = tt

  inv : ⊤ → x ≡ x
  inv tt = refl

  l : section f inv
  l tt = refl

  r : retract f inv
  r p = h x x refl p

isSet→LoopSpace≡⊤ : {A : Type} (x : A) → isSet A → (x ≡ x) ≡ ⊤
isSet→LoopSpace≡⊤ x h = isoToPath (isSet→LoopSpace≅⊤ x h)

data _⊔_ (A B : Type) : Type where

     inl : A → A ⊔ B
     inr : B → A ⊔ B

ℤ≅ℕ⊔ℕ : ℤ ≅ (ℕ ⊔ ℕ)
ℤ≅ℕ⊔ℕ = iso l r left right where
  l : ℤ → ℕ ⊔ ℕ
  l (pos n) = inl n
  l (negsuc n) = inr n

  r : ℕ ⊔ ℕ → ℤ
  r (inl x) = pos x
  r (inr x) = negsuc x

  left : section l r
  left (inl x) = refl
  left (inr x) = refl

  right : retract l r
  right (pos n) = refl
  right (negsuc n) = refl

{-

Your definition of ⊔NoConfusion goes here.

Your definition of Path≡⊔NoConfusion goes here.

Your definition of isSet⊔NoConfusion goes here.

Your definition of isSet⊔ goes here.

Your definition of isSetℤ goes here.

-}
