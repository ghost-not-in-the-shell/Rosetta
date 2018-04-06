{-# OPTIONS --type-in-type #-}
module Rosetta.Equality where
open import Agda.Builtin.Equality public renaming (refl to ≡-refl)
open import Rosetta.Equivalence

≡-sym : ∀ {A} {x y : A} → x ≡ y → y ≡ x
≡-sym ≡-refl = ≡-refl

≡-trans : ∀ {A} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
≡-trans ≡-refl ≡-refl = ≡-refl

instance
  ≡-equiv : ∀ {A} → IsEquivalence (_≡_ {A = A})
  ≡-equiv = record
    { refl  = ≡-refl
    ; sym   = ≡-sym
    ; trans = ≡-trans
    }

cong : ∀ {A B} (f : A → B) {x₁ x₂}
  → x₁ ≡ x₂
  → f x₁ ≡ f x₂
cong f ≡-refl = ≡-refl

cong₂ : ∀ {A₁ A₂ B} (_∙_ : A₁ → A₂ → B) {x₁ x₂ y₁ y₂}
  → x₁ ≡ x₂
  → y₁ ≡ y₂
  → x₁ ∙ y₁ ≡ x₂ ∙ y₂
cong₂ _∙_ ≡-refl ≡-refl = ≡-refl
