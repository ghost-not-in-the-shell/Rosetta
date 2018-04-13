{-# OPTIONS --type-in-type #-}
open import Rosetta.Category
module Rosetta.Yoneda (𝓒 : Category) where
open import Rosetta.Categories; open 𝓒𝓪𝓽
open import Rosetta.DiagramChasing 𝓒
open import Rosetta.Equivalence
open import Rosetta.Functor
open import Rosetta.Functors
open import Rosetta.HomFunctor 𝓒
open import Rosetta.Isomorphism
open import Rosetta.NaturalTransformation
open import Rosetta.Prelude
open import Rosetta.Setoids

module Restricted where
  𝓱₋⟹𝓱₋ : 𝓒 ᵒᵖ × 𝓒 ⟶ 𝓢𝓮𝓽
  𝓱₋⟹𝓱₋ = record
    { _₀_ = λ { (A , B) → record
      { ∣_∣   = 𝓱₍ A ₎₀ ⟹ 𝓱₍ B ₎₀
      ; _∣_∼_ = 𝓝𝓪𝓽 ∣_∼_
      } }
    ; _₁_ = λ { {A , B} {A′ , B′} (f , h) → record
      { _₀_ = λ g → record
        { _₍_₎    = {!!}
        ; natural = {!!}
        }
      ; _₁_ = {!!}
      } }
    ; _₂_ = {!!}
    ; resp-∘₀ = {!!}
    ; resp-∘₂ = {!!}
    }

  yoneda : 𝓝𝓪𝓽 ∣ 𝓱𝓸𝓶₍-,-₎ ≃ 𝓱₋⟹𝓱₋
  yoneda = record
    { to   = {!!}
    ; from = {!!}
    ; inverseˡ = {!!}
    ; inverseʳ = {!!}
    }
