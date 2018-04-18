{-# OPTIONS --type-in-type        #-}
{-# OPTIONS --allow-unsolved-meta #-}
module Rosetta.Category.Presheaves where
open import Rosetta.Prelude
open import Rosetta.Category.CartesianClosed
open import Rosetta.Category.Core
open import Rosetta.Category.HomFunctor
open import Rosetta.Category.Functors
open import Rosetta.Category.Setoids
open import Rosetta.Category.Sets

PSh : Category → Set
PSh 𝓒 = 𝓒 ᵒᵖ ⟶ 𝓢𝓮𝓽

𝓟𝓢𝓱 : Category → Category
𝓟𝓢𝓱 𝓒 = [ 𝓒 ᵒᵖ , 𝓢𝓮𝓽 ]

module 𝓟𝓢𝓱 𝓒 where
  infixr 6 _×_
  infixl 7 _^_

  𝟙 : PSh 𝓒
  𝟙 = record
    { _₀_      = λ _ → 𝓢𝓮𝓽.𝟙
    ; _₁_      = λ _ → !
    ; _₁-cong_ = λ _ _ → tt
    ; _resp-∘₀ = λ _ → tt
    ; _resp-∘₂ = λ _ → tt
    }

  _×_ : PSh 𝓒 → PSh 𝓒 → PSh 𝓒
  𝓕 × 𝓖 = record
    { _₀_      = λ A → (𝓕 ₀ A)  𝓢𝓮𝓽.×  (𝓖 ₀ A)
    ; _₁_      = λ f → (𝓕 ₁ f)      ×₁ (𝓖 ₁ f)
    ; _₁-cong_ = λ p → (𝓕 ₁-cong p) ×₁ (𝓖 ₁-cong p)
    ; _resp-∘₀ = (𝓕 resp-∘₀) ×₁ (𝓖 resp-∘₀)
    ; _resp-∘₂ = (𝓕 resp-∘₂) ×₁ (𝓖 resp-∘₂)
    }

  _^_ : PSh 𝓒 → PSh 𝓒 → PSh 𝓒
  𝓖 ^ 𝓕 = record
    { _₀_      = λ A → 𝒉𝒐𝒎 𝓝𝓪𝓽 (𝓒 ₍-, A ₎ × 𝓕) 𝓖
    ; _₁_      = λ f → {!!}
    ; _₁-cong_ = {!!}
    ; _resp-∘₀ = {!!}
    ; _resp-∘₂ = {!!}
    }

  !ᴾ : ∀ {𝓕} → 𝓟𝓢𝓱 𝓒 ∣ 𝓕 ⟶ 𝟙
  !ᴾ {𝓕} = record
    { _at_    = λ A → !₍ 𝓕 ₀ A ₎
    ; natural = {!!}
    }

  π₁ᴾ : ∀ {𝓕 𝓖} → 𝓟𝓢𝓱 𝓒 ∣ 𝓕 × 𝓖 ⟶ 𝓕
  π₁ᴾ {𝓕} {𝓖} = record
    { _at_    = λ A → π₁₍ 𝓕 ₀ A , 𝓖 ₀ A ₎
    ; natural = {!!}
    }

  π₂ᴾ : ∀ {𝓕 𝓖} → 𝓟𝓢𝓱 𝓒 ∣ 𝓕 × 𝓖 ⟶ 𝓖
  π₂ᴾ {𝓕} {𝓖} = record
    { _at_    = λ A → π₂₍ 𝓕 ₀ A , 𝓖 ₀ A ₎
    ; natural = {!!}
    }

  ⟨_,_⟩ᴾ : ∀ {𝓕 𝓖 𝓧} → 𝓟𝓢𝓱 𝓒 ∣ 𝓧 ⟶ 𝓕 → 𝓟𝓢𝓱 𝓒 ∣ 𝓧 ⟶ 𝓖 → 𝓟𝓢𝓱 𝓒 ∣ 𝓧 ⟶ 𝓕 × 𝓖
  ⟨ α , β ⟩ᴾ = record
    { _at_    = λ A → ⟨ α at A , β at A ⟩
    ; natural = {!!}
    }

  εᴾ : ∀ {𝓕 𝓖} → 𝓟𝓢𝓱 𝓒 ∣ 𝓖 ^ 𝓕 × 𝓕 ⟶ 𝓖
  εᴾ = {!!}

  ƛᴾ_ : ∀ {𝓕 𝓖 𝓧} → 𝓟𝓢𝓱 𝓒 ∣ 𝓧 × 𝓕 ⟶ 𝓖 → 𝓟𝓢𝓱 𝓒 ∣ 𝓧 ⟶ 𝓖 ^ 𝓕
  ƛᴾ_ = {!!}



instance
  𝓟𝓢𝓱_∣op✓ : ∀ 𝓒 → Op✓ (𝓟𝓢𝓱 𝓒 ∣_⟶_)
  𝓟𝓢𝓱 𝓒 ∣op✓ =
    let open 𝓟𝓢𝓱 𝓒

        ! : ∀ {𝓕} → 𝓟𝓢𝓱 𝓒 ∣ 𝓕 ⟶ 𝟙
        ! {𝓕} = record
          { _at_    = λ A → !₍ 𝓕 ₀ A ₎
          ; natural = {!!}
          }

        π₁ : ∀ {𝓕 𝓖} → 𝓟𝓢𝓱 𝓒 ∣ 𝓕 × 𝓖 ⟶ 𝓕
        π₁ {𝓕} {𝓖} = record
          { _at_    = λ A → π₁₍ 𝓕 ₀ A , 𝓖 ₀ A ₎
          ; natural = {!!}
          }

        π₂ : ∀ {𝓕 𝓖} → 𝓟𝓢𝓱 𝓒 ∣ 𝓕 × 𝓖 ⟶ 𝓖
        π₂ {𝓕} {𝓖} = record
          { _at_    = λ A → π₂₍ 𝓕 ₀ A , 𝓖 ₀ A ₎
          ; natural = {!!}
          }

        ⟨_,_⟩ : ∀ {𝓕 𝓖 𝓧} → 𝓟𝓢𝓱 𝓒 ∣ 𝓧 ⟶ 𝓕 → 𝓟𝓢𝓱 𝓒 ∣ 𝓧 ⟶ 𝓖 → 𝓟𝓢𝓱 𝓒 ∣ 𝓧 ⟶ 𝓕 × 𝓖
        ⟨ α , β ⟩ = record
          { _at_    = λ A → ⟨ α at A , β at A ⟩
          ; natural = {!!}
          }
    in record
    { 𝟙   = 𝟙
    ; _×_ = _×_
    ; _^_ = _^_
    ; !     = !
    ; π₁    = λ {𝓕 𝓖} → π₁ {𝓕} {𝓖}
    ; π₂    = λ {𝓕 𝓖} → π₂ {𝓕} {𝓖}
    ; ⟨_,_⟩ = ⟨_,_⟩
    ; ε     = εᴾ
    ; ƛ_    = ƛᴾ_
    }
