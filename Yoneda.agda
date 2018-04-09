{-# OPTIONS --type-in-type #-}
open import Rosetta.Category
module Rosetta.Yoneda (𝓒 : Category) where
open import Rosetta.Equivalence
open import Rosetta.Functor
open import Rosetta.Functors
open import Rosetta.HomFunctor 𝓒
open import Rosetta.Isomorphism
open import Rosetta.NaturalTransformation
open import Rosetta.Prelude
open import Rosetta.Setoids
open import Rosetta.DiagrammaticReasoning [ 𝓒 ᵒᵖ , 𝓢𝓮𝓽 ]

𝓱₋⟹_ : ∀ (𝓕 : 𝓒 ᵒᵖ ⟶ 𝓢𝓮𝓽) → 𝓒 ᵒᵖ ⟶ 𝓢𝓮𝓽
𝓱₋⟹ 𝓕 = record
  { _₀_ = λ A → record
    { ∣_∣ = 𝓱₍ A ₎₀ ⟹ 𝓕
    ; _∼_ = 𝓝𝓪𝓽∣_≈_
    }
  ; _₁_ = λ {A B} (f : 𝓒 ᵒᵖ ∣ A ⟶ B) → record
    { _₀_ = λ (α : 𝓱₍ A ₎₀ ⟹ 𝓕) → α ⋆ 𝓱₍ f ₎₁
    ; _₁_ = λ {α β : 𝓱₍ A ₎₀ ⟹ 𝓕} α≈β → begin
      α ⋆ 𝓱₍ f ₎₁  ↓⟨ ∘-cong₂ [ 𝓒 ᵒᵖ , 𝓢𝓮𝓽 ] {f₁ = 𝓱₍ f ₎₁} {𝓱₍ f ₎₁} {α} {β} α≈β refl₍ 𝓱₍ f ₎₁ ₎ ⟩
      β ⋆ 𝓱₍ f ₎₁  ∎
    }
  ; _₂_ = λ {A B}
            {f g : 𝓒 ᵒᵖ ∣ A ⟶ B}
            f≈g
            {α β : 𝓱₍ A ₎₀ ⟹ 𝓕}
            α≈β → begin
    α ⋆ 𝓱₍ f ₎₁  ↓⟨ ∘-cong₂ [ 𝓒 ᵒᵖ , 𝓢𝓮𝓽 ] {f₁ = 𝓱₍ f ₎₁} {𝓱₍ g ₎₁} {α} {β} α≈β (𝓱₋ ₂ f≈g) ⟩
    β ⋆ 𝓱₍ g ₎₁  ∎
  ; resp-∘₀ = λ {A}
                {α β : 𝓱₍ A ₎₀ ⟹ 𝓕}
                α≈β → begin
    α ⋆ 𝓱₍ id₍ A ₎ ₎₁  ↓⟨ ∘-cong₂ [ 𝓒 ᵒᵖ , 𝓢𝓮𝓽 ] {f₁ = 𝓱₍ id₍ A ₎ ₎₁} {id} {α} {β} α≈β (resp-∘₀ 𝓱₋) ⟩
    β ⋆ id             ↓⟨ ∘-unitʳ [ 𝓒 ᵒᵖ , 𝓢𝓮𝓽 ] {f = β} ⟩
    β                  ∎
  ; resp-∘₂ = λ {A B C}
                {f : 𝓒 ᵒᵖ ∣ A ⟶ B}
                {g : 𝓒 ᵒᵖ ∣ B ⟶ C}
                {α β : 𝓱₍ A ₎₀ ⟹ 𝓕}
                α≈β → begin
    α ⋆ 𝓱₍ g ∘̅ f ₎₁          ↓⟨ ∘-cong₂ [ 𝓒 ᵒᵖ , 𝓢𝓮𝓽 ] {f₁ = 𝓱₍ g ∘̅ f ₎₁} {𝓱₍ f ₎₁ ⋆ 𝓱₍ g ₎₁} {α} {β} α≈β (resp-∘₂ 𝓱₋) ⟩
    β ⋆ (𝓱₍ f ₎₁ ⋆ 𝓱₍ g ₎₁)  ∎
  }

yoneda : ∀ (𝓕 : 𝓒 ᵒᵖ ⟶ 𝓢𝓮𝓽) → [ 𝓒 ᵒᵖ , 𝓢𝓮𝓽 ] ∣ (𝓱₋⟹ 𝓕) ≃ 𝓕
yoneda 𝓕 = record
  { to   = record
    { _₍_₎    = λ C → record
      { _₀_ = λ (η : 𝓱₍ C ₎₀ ⟹ 𝓕) → (η ₍ C ₎) ₀ id
      ; _₁_ = λ {η₁ η₂ : 𝓱₍ C ₎₀ ⟹ 𝓕} η₁≈η₂ → η₁≈η₂ C refl
      }
    ; natural = {!!}
    }
  ; from = record
    { _₍_₎    = λ C → record
      { _₀_ = λ (c : ∣ 𝓕 ₀ C ∣) → record
        { _₍_₎    = λ D → record
          { _₀_ = λ (f : 𝓒 ᵒᵖ ∣ C ⟶ D) → (𝓕 ₁ f) ₀ c
          ; _₁_ = λ {f₁ f₂ : 𝓒 ᵒᵖ ∣ C ⟶ D} f₁≈f₂ → (𝓕 ₂ f₁≈f₂) (IsEquivalence.refl (Setoid.∼-equiv (𝓕 ₀ C)))
          }
        ; natural = λ {D₁ D₂}
                      {d     : 𝓒 ᵒᵖ ∣ D₁ ⟶ D₂}
                      {f₁ f₂ : 𝓒 ᵒᵖ ∣ C  ⟶ D₁}
                      f₁≈f₂ → {!!}
        }
      ; _₁_ = {!!}
      }
    ; natural = {!!}
    }
  ; inverseˡ = {!!}
  ; inverseʳ = {!!}
  }
