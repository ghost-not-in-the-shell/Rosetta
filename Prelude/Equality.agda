{-# OPTIONS --type-in-type #-}
module Rosetta.Prelude.Equality where
open import Agda.Builtin.Equality public renaming (refl to ≡-refl)
open import Rosetta.Prelude.Equivalence

≡-sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
≡-sym ≡-refl = ≡-refl

≡-trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
≡-trans ≡-refl ≡-refl = ≡-refl

instance
  ≡-equiv : ∀ {A : Set} → IsEquivalence (_≡_ {A = A})
  ≡-equiv = record
    { refl  = ≡-refl
    ; sym   = ≡-sym
    ; trans = ≡-trans
    }

setoid : Set → Setoid
setoid A = record
  { ∣_∣   = A
  ; _∣_∼_ = _≡_
  }

infixl 5 _<$>_
_<$>_ : ∀ {A B : Set} (f : A → B)
  → ∀ {x₁ x₂ : A} → x₁ ≡ x₂
  → f x₁ ≡ f x₂
f <$> ≡-refl = ≡-refl

infixl 5 _<*>_
_<*>_ : ∀ {A B : Set}
  → ∀ {f₁ f₂ : A → B} → f₁ ≡ f₂
  → ∀ {x₁ x₂ : A}     → x₁ ≡ x₂
  → f₁ x₁ ≡ f₂ x₂
≡-refl <*> ≡-refl = ≡-refl

≡-cong : ∀ {A B : Set} (f : A → B)
  → ∀ {x₁ x₂ : A} → x₁ ≡ x₂
  → f x₁ ≡ f x₂
≡-cong f x₁≡x₂ = f <$> x₁≡x₂

≡-cong₂ : ∀ {A₁ A₂ B : Set} (f : A₁ → A₂ → B)
  → ∀ {x₁ x₂ : A₁} → x₁ ≡ x₂
  → ∀ {y₁ y₂ : A₂} → y₁ ≡ y₂
  → f x₁ y₁ ≡ f x₂ y₂
≡-cong₂ f x₁≡x₂ y₁≡y₂ = f <$> x₁≡x₂ <*> y₁≡y₂

infix 5 _⟦_⟫
_⟦_⟫ : ∀ {A B : Set} → A → A ≡ B → B
x ⟦ ≡-refl ⟫ = x

transport : ∀ {A : Set} (P : A → Set) {x y : A} → x ≡ y → P x → P y
transport P x≡y px = px ⟦ P <$> x≡y ⟫

module ≡-Reasoning {A} where
  open SetoidReasoning (setoid A) public
