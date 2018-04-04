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
