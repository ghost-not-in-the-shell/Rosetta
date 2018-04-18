{-# OPTIONS --type-in-type #-}
module Rosetta.Category.Sets where
open import Rosetta.Prelude
open import Rosetta.Category.CartesianClosed
open import Rosetta.Category.Core

Function : Set → Set → Set
Function A B = A → B

instance
  𝓢et∣op : Op Function
  𝓢et∣op = record
    { id  = λ x → x
    ; _∘_ = λ g f x → g (f x)
    }

𝓢et : Category
𝓢et = record
  { ob    = Set
  ; hom   = Function
  ; _∣_∼_ = _≡_
  ; ∘-cong₂ = λ g₁≡g₂ f₁≡f₂ → ≡-cong₂ _∘_ g₁≡g₂ f₁≡f₂
  ; ∘-unitˡ = ≡-refl
  ; ∘-unitʳ = ≡-refl
  ; ∘-assoc = ≡-refl
  }

module 𝓢et where
  infixr 6 _×_
  infixl 7 _^_

  𝟙 : Set
  𝟙 = Unit

  _×_ : Set → Set → Set
  A × B = Product A B

  _^_ : Set → Set → Set
  B ^ A = A → B

open 𝓢et

instance
  𝓢et∣op✓ : Op✓ Function
  𝓢et∣op✓ = record
    { 𝟙   = 𝟙
    ; _×_ = _×_
    ; _^_ = _^_
    ; !     = λ _ → tt
    ; π₁    = λ { (x , y) → x }
    ; π₂    = λ { (x , y) → y }
    ; ⟨_,_⟩ = λ f g x → f x , g x
    ; ε     = λ { (f , x) → f x }
    ; ƛ_    = λ f x y → f (x , y)
    }

𝓢et✓ : CartesianClosed 𝓢et
𝓢et✓ = record
  { !-universal   = ≡-refl
  ; ⟨,⟩-cong₂     = λ f₁≡f₂ g₁≡g₂ → ≡-cong₂ ⟨_,_⟩ f₁≡f₂ g₁≡g₂
  ; ⟨,⟩-commute₁  = ≡-refl
  ; ⟨,⟩-commute₂  = ≡-refl
  ; ⟨,⟩-universal = λ ⁇-commute₁ ⁇-commute₂ → ≡-cong₂ ⟨_,_⟩ ⁇-commute₁ ⁇-commute₂
  ; ƛ-cong        = λ f₁≡f₂ → ≡-cong ƛ_ f₁≡f₂
  ; ƛ-commute     = ≡-refl
  ; ƛ-universal   = λ ⁇-commute → ≡-cong ƛ_ ⁇-commute
  }
