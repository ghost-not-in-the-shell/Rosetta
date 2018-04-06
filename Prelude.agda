{-# OPTIONS --type-in-type #-}
module Rosetta.Prelude where

Rel : Set → Set
Rel A = A → A → Set

flip : ∀ {A₁ A₂ B} → (A₁ → A₂ → B) → (A₂ → A₁ → B)
flip _∙_ = λ x₂ x₁ → x₁ ∙ x₂
