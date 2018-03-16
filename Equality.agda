module Rosetta.Equality where
open import Agda.Builtin.Equality as ≡ public using (_≡_)
open import Rosetta.Equivalence

≡-sym : ∀ {𝔞} {A : Set 𝔞} {x y : A}
  → x ≡ y
  → y ≡ x
≡-sym ≡.refl = ≡.refl

≡-trans : ∀ {𝔞} {A : Set 𝔞} {x y z : A}
  → x ≡ y
  → y ≡ z
  → x ≡ z
≡-trans ≡.refl ≡.refl = ≡.refl

instance
  ≡-equiv : ∀ {𝔞} {A : Set 𝔞} → IsEquivalence λ (x y : A) → x ≡ y
  ≡-equiv = record
    { refl  = ≡.refl
    ; sym   = ≡-sym
    ; trans = ≡-trans
    }

infixl 5 _<$>_
_<$>_ : ∀ {𝔞 𝔟} {A : Set 𝔞} {B : Set 𝔟} (f : A → B) {x₁ x₂}
  → x₁ ≡ x₂
  → f x₁ ≡ f x₂
f <$> ≡.refl = ≡.refl

infixl 5 _<*>_
_<*>_ : ∀ {𝔞 𝔟} {A : Set 𝔞} {B : Set 𝔟} {f₁ f₂ : A → B} {x₁ x₂}
  → f₁ ≡ f₂
  → x₁ ≡ x₂
  → f₁ x₁ ≡ f₂ x₂
≡.refl <*> ≡.refl = ≡.refl
