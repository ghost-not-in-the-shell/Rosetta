{-# OPTIONS --type-in-type #-}
module Rosetta.Functor where
open import Rosetta.Equivalence
open import Rosetta.Category

record Functor (𝓒 𝓓 : Category) : Set where
  field
    _₀_ : ob 𝓒 → ob 𝓓
    _₁_ : ∀ {A B} → 𝓒 ∣ A ⟶ B → 𝓓 ∣ _₀_ A ⟶ _₀_ B
    ._₂_ : ∀ {A B} {f g : 𝓒 ∣ A ⟶ B}
      → 𝓒 ∣ f ∼ g
      → 𝓓 ∣ _₁_ f ∼ _₁_ g

    .resp-∘₀ : ∀ {A} → 𝓓 ∣ _₁_ id₍ A ₎ ∼ id₍ _₀_ A ₎
    .resp-∘₂ : ∀ {A B C} {f : 𝓒 ∣ A ⟶ B} {g : 𝓒 ∣ B ⟶ C}
      → 𝓓 ∣ _₁_ (g ∘ f) ∼ (_₁_ g) ∘ (_₁_ f)

open Functor public

infix 4 _⟶_
_⟶_ = Functor
