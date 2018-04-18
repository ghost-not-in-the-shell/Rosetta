{-# OPTIONS --type-in-type #-}
module Rosetta.Normalization.Syntax where
open import Rosetta.Prelude

infixr 5 _⇒_
data Ty : Set where
  𝒐   : Ty
  _⇒_ : Ty → Ty → Ty

Con = List Ty

infix 4 _⊢_
data _⊢_ (Γ : Con) : Ty → Set where
  var : ∀ {A}
    → A ∈ Γ
    → Γ ⊢ A

  lam : ∀ {A B}
    → A ∷ Γ ⊢ B
    → Γ ⊢ A ⇒ B

  app : ∀ {A B}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
    → Γ ⊢ B
