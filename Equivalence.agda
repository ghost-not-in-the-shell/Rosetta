{-# OPTIONS --type-in-type #-}
module Rosetta.Equivalence where
open import Agda.Builtin.Equality renaming (refl to ≡-refl)

Rel : Set → Set
Rel A = A → A → Set

record IsEquivalence {A} (_∼_ : Rel A) : Set where
  field
    .refl₍_₎ : ∀ x → x ∼ x
    .sym     : ∀ {x y} → x ∼ y → y ∼ x
    .trans   : ∀ {x y z} → x ∼ y → y ∼ z → x ∼ z

  .refl : ∀ {x} → x ∼ x
  refl = refl₍ _ ₎

  .inj : ∀ {x y} → x ≡ y → x ∼ y
  inj ≡-refl = refl

open IsEquivalence ⦃...⦄ public

module EqReasoning {A} {_∼_ : Rel A} ⦃ _ : IsEquivalence _∼_ ⦄ where
  infix  1 begin_
  infixr 2 _↓⟨_⟩_
  infixr 2 _↑⟨_⟩_
  infix  3 _∎

  .begin_ : ∀ {x y} → x ∼ y → x ∼ y
  begin x∼y = x∼y

  ._↓⟨_⟩_ : ∀ x {y z} → x ∼ y → y ∼ z → x ∼ z
  x ↓⟨ x∼y ⟩ y∼z = trans x∼y y∼z

  ._↑⟨_⟩_ : ∀ x {y z} → y ∼ x → y ∼ z → x ∼ z
  x ↑⟨ y∼x ⟩ y∼z = trans (sym y∼x) y∼z

  ._∎ : ∀ x → x ∼ x
  x ∎ = refl₍ x ₎
