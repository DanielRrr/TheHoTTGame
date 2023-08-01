module 0Trinitarianism.Quest4 where

open import 0Trinitarianism.Preambles.P4

data Id {A : Type} : (x y : A) → Type where
  rfl : {x : A} → Id x x

Sym : {A : Type} {x y : A} → Id x y → Id y x
Sym rfl = rfl

idTrans : {A : Type} {x y z : A} → Id x y → Id y z → Id x z
idTrans rfl p₂ = p₂

_*_ : {A : Type} {x y z : A} → Id x y → Id y z → Id x z
p₁ * p₂ = idTrans p₁ p₂

Sym* : {A : Type} {x y : A} (p : Id x y) → Id (Sym p * p) rfl
Sym* rfl = rfl

*Sym : {A : Type} {x y : A} (p : Id x y) → Id (p * Sym p) rfl
*Sym rfl = rfl

Assoc : {A : Type} {w x y z : A} (p : Id w x) (q : Id x y) (r : Id y z)
        → Id ((p * q) * r) (p * (q * r))
Assoc rfl q r = rfl

outOfId : {A : Type} {x : A} (M : (y : A) → Id x y → Type) → M x rfl
  → {y : A} (p : Id x y) → M y p
outOfId M f rfl = f

≡-to-Id : {A : Type} {x y : A} → x ≡ y → Id x y
≡-to-Id {_} {x} = J (λ y p → Id x y) rfl

≡-to-IdRefl : {A : Type} {x : A} → ≡-to-Id (refl {x = x}) ≡ rfl
≡-to-IdRefl {x = x} = JRefl (λ y p → Id x y) rfl

Id-to-≡ : {A : Type} {x y : A} → Id x y → x ≡ y
Id-to-≡ rfl = refl

rightInv : {A : Type} {x y : A} → section (≡-to-Id {A} {x} {y}) Id-to-≡
rightInv rfl = ≡-to-IdRefl 

leftInv : {A : Type} {x y : A} →
  retract (≡-to-Id {A} {x} {y}) Id-to-≡
leftInv = J (λ y p → (Id-to-≡ (≡-to-Id p)) ≡ p) (cong Id-to-≡ ≡-to-IdRefl)

Path≅Id : {A : Type} {x y : A} → (x ≡ y) ≅ (Id x y)
Path≅Id = iso ≡-to-Id Id-to-≡ rightInv leftInv

pathToFun : {A B : Type} → A ≡ B → A → B
pathToFun {A} = J (λ B p → (A → B)) λ x → x

pathToFunRefl : {A : Type} {x : A} → pathToFun (refl {x = A}) ≡ (λ x → x)
pathToFunRefl {A} = JRefl ((λ B p → (A → B))) λ x → x

endPt : {A : Type} {x y : A} → (B : A → Type) (p : x ≡ y) → B x → B y
endPt {x = x} B = J (λ y p → B x → B y) (λ x → x)

endPtRefl : {A : Type} {x : A} → (B : A → Type) → endPt B (refl {x = x}) ≡ (λ x → x)
endPtRefl {x = x} B = JRefl ((λ y p → B x → B y)) (λ x → x)

endPt' : {A : Type} {x y : A} → (B : A → Type) (p : x ≡ y) → B x → B y
endPt' B p = pathToFun (cong B p)

funExt : {A : Type} {B : A → Type} {f g : (a : A) → B a} →
   ((a : A) → f a ≡ g a) → f ≡ g
funExt p = λ i a → p a i

funExt' : {A : Type} {B : A → Type} {f g : (a : A) → B a} → f ≡ g → (a : A) → f a ≡ g a
funExt' p = λ a i → p i a

sectionFunExt : {A : Type} {B : A → Type} {f g : (a : A) → B a} →
  section (funExt' {A} {B} {f} {g}) funExt
sectionFunExt h = refl

retractFunExt : {A : Type} {B : A → Type} {f g : (a : A) → B a} →
  retract (funExt' {A} {B} {f} {g}) funExt
retractFunExt h = refl

funExtPath : {A : Type} {B : A → Type} {f g : (a : A) → B a} →
  (f ≡ g) ≡ ((a : A) → f a ≡ g a)
funExtPath = isoToPath (iso funExt' funExt sectionFunExt retractFunExt)
