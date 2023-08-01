-- ignore
module 1FundamentalGroup.Quest0 where
open import 1FundamentalGroup.Preambles.P0

Refl : base ≡ base
Refl = refl

Flip : Bool → Bool
Flip false = true
Flip true = false

boolRightInv : section Flip Flip
boolRightInv false = refl
boolRightInv true = refl

boolLeftInv : retract Flip Flip
boolLeftInv false = refl
boolLeftInv true = refl

flipIso : Bool ≅ Bool
flipIso = iso Flip Flip boolRightInv boolLeftInv

flipPath : Bool ≡ Bool
flipPath = isoToPath flipIso

doubleCover : S¹ → Type
doubleCover base = Bool
doubleCover (loop i) = flipPath i

endPtOfTrue : base ≡ base → doubleCover base
endPtOfTrue p = endPt doubleCover p true

Refl≢loop : Refl ≡ loop → ⊥
Refl≢loop p = true≢false (cong endPtOfTrue p)

------------------- Side Quest - Empty -------------------------

toEmpty : (A : Type) → Type
toEmpty A = A → ⊥

pathEmpty : (A : Type) → Type₁
pathEmpty A = A ≡ ⊥

isoEmpty : (A : Type) → Type
isoEmpty A = A ≅ ⊥

outOf⊥ : (A : Type) → ⊥ → A
outOf⊥ A ()

toEmpty→isoEmpty : (A : Type) → toEmpty A → isoEmpty A
toEmpty→isoEmpty A f = iso f (outOf⊥ A) rightInv leftInv where

   rightInv : section f (outOf⊥ A)
   rightInv ()

   leftInv : retract f (outOf⊥ A)
   leftInv x = outOf⊥ (outOf⊥ A (f x) ≡ x) (f x)

isoEmpty→pathEmpty : (A : Type) → isoEmpty A → pathEmpty A
isoEmpty→pathEmpty A = isoToPath

pathEmpty→toEmpty : (A : Type) → pathEmpty A → toEmpty A
pathEmpty→toEmpty A p x = pathToFun p x


------------------- Side Quests - true≢false --------------------

-- This is a comment box,
-- remove the {- and -} to do the side quests

true≢false' : true ≡ false → ⊥
true≢false' p = pathToFun (cong {!!} p) tt where
  boolToProp : Bool → Type
  boolToProp false = ⊥
  boolToProp true = ⊥

  ⊤≡⊥ : ⊤ ≡ ⊥
  ⊤≡⊥ = {!!}
