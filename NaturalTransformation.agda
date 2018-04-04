{-# OPTIONS --type-in-type #-}
module Rosetta.NaturalTransformation where
open import Rosetta.Equivalence
open import Rosetta.Category
open import Rosetta.Functor

record NaturalTransformation {𝓒 𝓓} (𝓕 𝓖 : 𝓒 ⟶ 𝓓) : Set where
  field
    _₍_₎ : ∀ A → 𝓓 ₍ 𝓕 ₀ A , 𝓖 ₀ A ₎
    .natural : ∀ {A B} {f : 𝓒 ₍ A , B ₎} → 𝓓 ∣ _₍_₎ B ∘ 𝓕 ₁ f ∼ 𝓖 ₁ f ∘ _₍_₎ A

open NaturalTransformation public

infix 4 _⟹_
_⟹_ = NaturalTransformation

{-# DISPLAY NaturalTransformation = _⟹_ #-}
