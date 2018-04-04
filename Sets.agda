{-# OPTIONS --type-in-type #-}
module Rosetta.Sets where
open import Rosetta.Equivalence
open import Rosetta.Equality
open import Rosetta.Category        as Category
open import Rosetta.CartesianClosed as CartesianClosed

infix 0 _-𝓢et⟶_
_-𝓢et⟶_ : Set → Set → Set
A -𝓢et⟶ B = A → B

instance
  𝓢et-op : Category.Op _-𝓢et⟶_
  𝓢et-op = record
    { id  = λ x → x
    ; _∘_ = λ g f x → g (f x)
    }

𝓢et : Category
𝓢et = record
  { ob    = Set
  ; hom   = _-𝓢et⟶_
  ; _∣_∼_ = _≡_
  ; ∘-cong₂ = cong₂ _∘_
  ; ∘-unitˡ = refl
  ; ∘-unitʳ = refl
  ; ∘-assoc = refl
  }

record 𝟙 : Set where
  constructor tt

infixr 2 _×_
infixr 4 _,_
record _×_ (A B : Set) : Set where
  constructor _,_
  field
    π₁ : A
    π₂ : B

open _×_

_⇒_ : Set → Set → Set
A ⇒ B = A → B

instance
  𝓢et✓-op : CartesianClosed.Op _-𝓢et⟶_
  𝓢et✓-op = record
    { 𝟙   = 𝟙
    ; _×_ = _×_
    ; _⇒_ = _⇒_

    ; !     = λ _ → tt
    ; π₁    = π₁
    ; π₂    = π₂
    ; ⟨_,_⟩ = λ f g x → f x , g x
    ; ev    = λ { (f , x) → f x }
    ; λ₍_₎  = λ f x y → f (x , y)
    }

𝓢et✓ : CartesianClosed 𝓢et
𝓢et✓ = record
  { !-universal   = refl
  ; ⟨,⟩-cong₂     = cong₂ ⟨_,_⟩
  ; ⟨,⟩-commute₁  = refl
  ; ⟨,⟩-commute₂  = refl
  ; ⟨,⟩-universal = cong₂ ⟨_,_⟩
  ; λ-cong        = cong λ₍_₎
  ; λ-commute     = refl
  ; λ-universal   = cong λ₍_₎
  }
