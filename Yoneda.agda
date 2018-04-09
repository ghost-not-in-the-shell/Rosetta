{-# OPTIONS --type-in-type #-}
open import Rosetta.Category
module Rosetta.Yoneda (𝓒 : Category) where
open import Rosetta.DiagrammaticReasoning 𝓒
open import Rosetta.Equivalence
open import Rosetta.Functor
open import Rosetta.Functors
open import Rosetta.HomFunctor 𝓒
open import Rosetta.Isomorphism
open import Rosetta.NaturalTransformation
open import Rosetta.Prelude
open import Rosetta.Setoids

𝓱₋⟹_ : ∀ (𝓕 : 𝓒 ᵒᵖ ⟶ 𝓢𝓮𝓽) → 𝓒 ᵒᵖ ⟶ 𝓢𝓮𝓽
𝓱₋⟹ 𝓕 = record
  { _₀_ = λ A → record
    { ∣_∣ = 𝓱₍ A ₎₀ ⟹ 𝓕
    ; _∼_ = 𝓝𝓪𝓽∣_≈_
    }
  ; _₁_ = λ {A A′} (f : 𝓒 ᵒᵖ ∣ A ⟶ A′) → record
    { _₀_ = λ (θ : 𝓱₍ A ₎₀ ⟹ 𝓕) → θ ⋆ 𝓱₍ f ₎₁
    ; _₁_ = let open 𝓝𝓪𝓽-Reasoning 𝓱₍ A′ ₎₀ 𝓱₍ A  ₎₀ 𝓕
            in _⟩⋆⟨ 𝓝𝓪𝓽≈-refl₍ 𝓱₍ f ₎₁ ₎

    }
  ; _₂_ = {!!}
  ; resp-∘₀ = {!!}
  ; resp-∘₂ = {!!}
  }

{-
𝓱₋⟹_ : ∀ (𝓕 : 𝓒 ᵒᵖ ⟶ 𝓢𝓮𝓽) → 𝓒 ᵒᵖ ⟶ 𝓢𝓮𝓽
𝓱₋⟹ 𝓕 = record
  { _₀_ = λ A → record
    { ∣_∣ = 𝓱₍ A ₎₀ ⟹ 𝓕
    ; _∼_ = 𝓝𝓪𝓽∣_≈_
    }
  ; _₁_ = λ {A A′}
            (f : 𝓒 ᵒᵖ ∣ A ⟶ A′)
            → record
    { _₀_ = λ (θ : 𝓱₍ A ₎₀ ⟹ 𝓕) → θ ⋆ 𝓱₍ f ₎₁
    ; _₁_ = λ {θ₁ θ₂ : 𝓱₍ A ₎₀ ⟹ 𝓕}
              θ₁≈θ₂ B
              {g₁ : 𝓒 ∣ B ⟶ A′}
              g₁≈g₂ → {!!}
    }
  ; _₂_ = {!!}
  ; resp-∘₀ = {!!}
  ; resp-∘₂ = {!!}
  }

yoneda : ∀ (𝓕 : 𝓒 ᵒᵖ ⟶ 𝓢𝓮𝓽) → [ 𝓒 ᵒᵖ , 𝓢𝓮𝓽 ] ∣ 𝓕 ≃ (𝓱₋⟹ 𝓕)
yoneda 𝓕 = {!!}

-}
