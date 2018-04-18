{-# OPTIONS --type-in-type #-}
open import Rosetta.Category.Core
module Rosetta.Category.Yoneda (𝓒 : Category) where
open import Rosetta.Prelude
open import Rosetta.Category.Categories; open 𝓒𝓪𝓽
open import Rosetta.Category.DiagramChasing 𝓒
open import Rosetta.Category.Functors
open import Rosetta.Category.HomFunctor 𝓒
open import Rosetta.Category.Setoids
open CategoryReasoning 𝓒

module Restricted where
  𝓱₋⟹𝓱₋ : 𝓒 ᵒᵖ × 𝓒 ⟶ 𝓢𝓮𝓽
  𝓱₋⟹𝓱₋ = record
    { _₀_      = λ { (A , B) → record
      { ∣_∣   = 𝓱₍ A ₎₀ ⟹ 𝓱₍ B ₎₀
      ; _∣_∼_ = 𝓝𝓪𝓽 ∣_∼_
      } }
    ; _₁_      = λ { {A , B} {A′ , B′} (f , h) → record
      { _$_    = {!!}
      ; _cong_ = {!!}
      } }
    ; _₁-cong_ = {!!}
    ; _resp-∘₀ = {!!}
    ; _resp-∘₂ = {!!}
    }

  θ : 𝓝𝓪𝓽 ∣ 𝓱𝓸𝓶₍-,-₎ ⟶ 𝓱₋⟹𝓱₋
  θ = record
    { _at_    = λ { (A , B) → record
      { _$_    = 𝓱₍_₎₁
      ; _cong_ = λ h₁∼h₂ g₁∼g₂ → h₁∼h₂ ⟩∘⟨ g₁∼g₂
      } }
    ; natural = {!!}
    }

  θ⁻¹ : 𝓝𝓪𝓽 ∣ 𝓱₋⟹𝓱₋ ⟶ 𝓱𝓸𝓶₍-,-₎
  θ⁻¹ = record
    { _at_    = λ { (A , B) → record
      { _$_    = λ (η : 𝓱₍ A ₎₀ ⟹ 𝓱₍ B ₎₀) → (η at A) $ id
      ; _cong_ = λ {η₁ η₂ : 𝓱₍ A ₎₀ ⟹ 𝓱₍ B ₎₀} η₁∼η₂ → begin
      (η₁ at A) $ id  ↓⟨ η₁∼η₂ refl ⟩
      (η₂ at A) $ id  ∎
      } }
    ; natural = {!!}
    }

  yoneda : [ 𝓒 ᵒᵖ × 𝓒 , 𝓢𝓮𝓽 ] ∣ 𝓱𝓸𝓶₍-,-₎ ≃ 𝓱₋⟹𝓱₋
  yoneda = record
    { to   = θ
    ; from = θ⁻¹
    ; inverseˡ = λ { {A , B}
                     {f₁} {f₂} -- f₁ f₂ : 𝓒 ∣ A ⟶ B
                     f₁∼f₂ → begin
      f₁ ∘ id  ↓⟨ ∘-unitʳ 𝓒 ⟩
      f₁       ↓⟨ f₁∼f₂ ⟩
      f₂       ∎ }
    ; inverseʳ = λ { {A , B}
                     {η₁} {η₂} -- η₁ η₂ : 𝓝𝓪𝓽 ∣ 𝓱₍ A ₎₀ ⟶ 𝓱₍ B ₎₀
                     η₁∼η₂
                     {X}
                     {f₁} {f₂} -- f₁ f₂ : 𝓒   ∣ X ⟶ A
                     f₁∼f₂ → begin
      ((η₁ at A) $ id) ∘ f₁  ↓⟨ η₁∼η₂ refl ⟩∘⟨ f₁∼f₂ ⟩
      ((η₂ at A) $ id) ∘ f₂  ↑⟨ natural η₂ refl ⟩
      (η₂ at X) $ (id ∘ f₂)  ↓⟨ (η₂ at X) cong (∘-unitˡ 𝓒) ⟩
      (η₂ at X) $ f₂         ∎ }
    }

module RestrictedWithoutNaturality where
  θ : ∀ {B B′} → 𝓢𝓮𝓽 ∣ 𝒉𝒐𝒎 𝓒 B B′ ⟶ 𝒉𝒐𝒎 𝓝𝓪𝓽 𝓱₍ B ₎₀ 𝓱₍ B′ ₎₀
  θ = record
    { _$_    = 𝓱₍_₎₁
    ; _cong_ = λ h₁∼h₂ g₁∼g₂ → h₁∼h₂ ⟩∘⟨ g₁∼g₂
    }

  θ⁻¹ : ∀ {B B′} → 𝓢𝓮𝓽 ∣ 𝒉𝒐𝒎 𝓝𝓪𝓽 𝓱₍ B ₎₀ 𝓱₍ B′ ₎₀ ⟶ 𝒉𝒐𝒎 𝓒 B B′
  θ⁻¹ {B} {B′} = record
    { _$_    = λ (η : 𝓱₍ B ₎₀ ⟹ 𝓱₍ B′ ₎₀) → (η at B) $ id
    ; _cong_ = λ {η₁ η₂ : 𝓱₍ B ₎₀ ⟹ 𝓱₍ B′ ₎₀} η₁∼η₂ → begin
      (η₁ at B) $ id  ↓⟨ η₁∼η₂ refl ⟩
      (η₂ at B) $ id  ∎
    }

  yoneda : ∀ {B B′} → 𝓢𝓮𝓽 ∣ 𝒉𝒐𝒎 𝓒 B B′ ≃ 𝒉𝒐𝒎 𝓝𝓪𝓽 𝓱₍ B ₎₀ 𝓱₍ B′ ₎₀
  yoneda {B} {B′} = record
    { to   = θ
    ; from = θ⁻¹
    ; inverseˡ = λ {h₁ h₂ : 𝓒 ∣ B ⟶ B′} h₁∼h₂ → begin
        h₁ ∘ id  ↓⟨ ∘-unitʳ 𝓒 ⟩
        h₁       ↓⟨ h₁∼h₂ ⟩
        h₂       ∎
    ; inverseʳ = λ {η₁ η₂ : 𝓝𝓪𝓽 ∣ 𝓱₍ B ₎₀ ⟶ 𝓱₍ B′ ₎₀}
                   η₁∼η₂
                   {A}
                   {g₁ g₂ : 𝓒   ∣ A ⟶ B}
                   g₁∼g₂ → begin
      ((η₁ at B) $ id) ∘ g₁  ↓⟨ η₁∼η₂ refl ⟩∘⟨ g₁∼g₂ ⟩
      ((η₂ at B) $ id) ∘ g₂  ↑⟨ natural η₂ refl ⟩
      (η₂ at A) $ (id ∘ g₂)  ↓⟨ (η₂ at A) cong (∘-unitˡ 𝓒) ⟩
      (η₂ at A) $ g₂         ∎
    }
