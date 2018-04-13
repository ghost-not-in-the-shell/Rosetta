{-# OPTIONS --type-in-type #-}
module Rosetta.Prelude where
open import Agda.Builtin.Equality public renaming (refl to ≡-refl)

record ⊤ : Set where
  constructor tt

infixr 4 _,_
record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    π₁ : A
    π₂ : B π₁

Rel : Set → Set
Rel A = A → A → Set

flip : ∀ {A₁ A₂ B} → (A₁ → A₂ → B) → (A₂ → A₁ → B)
flip _∙_ = λ x₂ x₁ → x₁ ∙ x₂
