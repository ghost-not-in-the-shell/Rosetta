module Rosetta.Equivalence where
open import Agda.Primitive

record IsEquivalence {𝔞₁ 𝔞₂} {A : Set 𝔞₁} (_∼_ : A → A → Set 𝔞₂) : Set (𝔞₁ ⊔ 𝔞₂) where
  field
    refl  : ∀ {x} → x ∼ x
    sym   : ∀ {x y} → x ∼ y → y ∼ x
    trans : ∀ {x y z} → x ∼ y → y ∼ z → x ∼ z

open IsEquivalence ⦃...⦄ public
