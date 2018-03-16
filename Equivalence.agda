module Rosetta.Equivalence where
open import Agda.Primitive
open import Agda.Builtin.Equality renaming (refl to ≡-refl)


Rel : ∀ {𝔞} → Set 𝔞 → ∀ ℓ → Set (𝔞 ⊔ lsuc ℓ)
Rel A ℓ = A → A → Set ℓ

record IsEquivalence {𝔞 ℓ} {A : Set 𝔞} (_∼_ : Rel A ℓ) : Set (𝔞 ⊔ ℓ) where
  field
    refl  : ∀ {x} → x ∼ x
    sym   : ∀ {x y} → x ∼ y → y ∼ x
    trans : ∀ {x y z} → x ∼ y → y ∼ z → x ∼ z

  inj : ∀ {x y} → x ≡ y → x ∼ y
  inj ≡-refl = refl

  module EqReasoning where
    infix  1 begin_
    infixr 2 _↓⟨_⟩_
    infixr 2 _↑⟨_⟩_
    infix  3 _∎

    begin_ : ∀ {x y}
      → x ∼ y
      → x ∼ y
    begin x∼y = x∼y

    _↓⟨_⟩_ : ∀ {y z}
      → (x : A)
      → x ∼ y
      → y ∼ z
      → x ∼ z
    x ↓⟨ x∼y ⟩ y∼z = trans x∼y y∼z

    _↑⟨_⟩_ : ∀ {y z}
      → (x : A)
      → y ∼ x
      → y ∼ z
      → x ∼ z
    x ↑⟨ y∼x ⟩ y∼z = trans (sym y∼x) y∼z

    _∎ : ∀ x → x ∼ x
    x ∎ = refl

open IsEquivalence ⦃...⦄ public
