{-# OPTIONS --without-K #-}
module Rosetta.Sets where
open import Agda.Primitive
open import Rosetta.Equality
open import Rosetta.Category
open import Rosetta.Terminal
open import Rosetta.Product
open import Rosetta.Equivalence

Fun : ∀ {𝔞} → Set 𝔞 → Set 𝔞 → Set 𝔞
Fun A B = A → B

instance
  𝓢𝓮𝓽-is-category : ∀ {𝔞} → IsCategory λ (A B : Set 𝔞) → Fun A B
  𝓢𝓮𝓽-is-category = record
    { id  = λ x → x
    ; _∘_ = λ g f → λ x → g (f x)
    ; ∘-unitˡ = refl
    ; ∘-unitʳ = refl
    ; ∘-assoc = refl
    }

𝓢𝓮𝓽 : ∀ 𝔞 → Category (lsuc 𝔞) 𝔞
𝓢𝓮𝓽 𝔞 = record
  { Obj = Set 𝔞
  ; Hom₍_,_₎ = Fun
  }

record 𝟙 {𝔞} : Set 𝔞 where
  constructor tt

instance
  terminal : ∀ {𝔞} → Terminal (𝓢𝓮𝓽 𝔞)
  terminal = record
    { 𝟙 = 𝟙
    ; ! = λ _ → tt
    ; !-universal = refl
    }

infixr 2 _×_
infixr 4 _,_
record _×_ {𝔞} (A B : Set 𝔞) : Set 𝔞 where
  constructor _,_
  field
    π₁ : A
    π₂ : B

open _×_

instance
  product : ∀ {𝔞} → Product (𝓢𝓮𝓽 𝔞)
  product =
    let ⟨_,_⟩ : ∀ {A B X}
          → (f : X → A)
          → (g : X → B)
          → X → A × B
        ⟨ f , g ⟩ = λ x → f x , g x
    in record
    { _×_ = _×_
    ; π₁ = π₁
    ; π₂ = π₂
    ; ⟨_,_⟩ = ⟨_,_⟩
    ; ⟨,⟩-commute₁ = refl
    ; ⟨,⟩-commute₂ = refl
    ; ⟨,⟩-universal = λ ⁇-commute₁ ⁇-commute₂ → ⟨_,_⟩ <$> ⁇-commute₁ <*> ⁇-commute₂
    }
