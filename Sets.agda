{-# OPTIONS --type-in-type #-}
module Rosetta.Sets where
open import Rosetta.CartesianClosed
open import Rosetta.Category
open import Rosetta.Equality
open import Rosetta.Equivalence
open import Rosetta.Prelude

instance
  𝓢et-op : Op λ A B → A → B
  𝓢et-op = record
    { id  = λ x → x
    ; _∘_ = λ g f x → g (f x)
    }

𝓢et : Category
𝓢et = record
  { ob  = Set
  ; hom = λ A B → A → B
  ; _≈_ = _≡_
  ; ∘-cong₂ = cong₂ _∘_
  ; ∘-unitˡ = refl
  ; ∘-unitʳ = refl
  ; ∘-assoc = refl
  }

module 𝓢et where
  infixr 6 _×_
  infixr 7 _⇒_

  𝟙 = ⊤

  _×_ : Set → Set → Set
  A × B = Σ A λ _ → B

  _⇒_ : Set → Set → Set
  A ⇒ B = A → B

open 𝓢et

instance
  𝓢et-op✓ : Op✓ λ A B → A → B
  𝓢et-op✓ = record
    { 𝟙   = 𝟙
    ; _×_ = _×_
    ; _⇒_ = _⇒_
    ; !     = λ _ → tt
    ; π₁    = λ { (x , y) → x }
    ; π₂    = λ { (x , y) → y }
    ; ⟨_,_⟩ = λ f g x → f x , g x
    ; ε     = λ { (f , x) → f x }
    ; ƛ_    = λ f x y → f (x , y)
    }

𝓢et✓ : CartesianClosed 𝓢et
𝓢et✓ = record
  { !-universal   = refl
  ; ⟨,⟩-cong₂     = cong₂ ⟨_,_⟩
  ; ⟨,⟩-commute₁  = refl
  ; ⟨,⟩-commute₂  = refl
  ; ⟨,⟩-universal = cong₂ ⟨_,_⟩
  ; ƛ-cong        = cong ƛ_
  ; ƛ-commute     = refl
  ; ƛ-universal   = cong ƛ_
  }
