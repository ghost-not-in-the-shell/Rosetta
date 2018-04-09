{-# OPTIONS --type-in-type #-}
module Rosetta.Isomorphism where
open import Rosetta.Category

record _∣_≃_ 𝓒 (A B : ob 𝓒) : Set where
  field
    to   : 𝓒 ∣ A ⟶ B
    from : 𝓒 ∣ A ⟵ B
    inverseˡ : 𝓒 ∣ from ∘ to ≈ id
    inverseʳ : 𝓒 ∣ to ∘ from ≈ id

open _∣_≃_ public
