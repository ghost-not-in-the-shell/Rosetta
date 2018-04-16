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
open CategoryReasoning 𝓒

module Restricted where
  θ : ∀ {B B′} → 𝓢𝓮𝓽 ∣ 𝒉𝒐𝒎 𝓒 B B′ ⟶ 𝒉𝒐𝒎 𝓝𝓪𝓽 𝓱₍ B ₎₀ 𝓱₍ B′ ₎₀
  θ = record
    { _$_  = 𝓱₍_₎₁
    ; 𝒄𝒐𝒏𝒈 = λ h₁∼h₂ g₁∼g₂ → h₁∼h₂ ⟩∘⟨ g₁∼g₂
    }

  θ⁻¹ : ∀ {B B′} → 𝓢𝓮𝓽 ∣ 𝒉𝒐𝒎 𝓝𝓪𝓽 𝓱₍ B ₎₀ 𝓱₍ B′ ₎₀ ⟶ 𝒉𝒐𝒎 𝓒 B B′
  θ⁻¹ {B} {B′} = record
    { _$_  = λ (η : 𝓱₍ B ₎₀ ⟹ 𝓱₍ B′ ₎₀) → η ₍ B ₎ $ id
    ; 𝒄𝒐𝒏𝒈 = λ {η₁ η₂ : 𝓱₍ B ₎₀ ⟹ 𝓱₍ B′ ₎₀} η₁∼η₂ → begin
      η₁ ₍ B ₎ $ id  ↓⟨ η₁∼η₂ refl ⟩
      η₂ ₍ B ₎ $ id  ∎
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
      (η₁ ₍ B ₎ $ id) ∘ g₁  ↓⟨ η₁∼η₂ refl ⟩∘⟨ g₁∼g₂ ⟩
      (η₂ ₍ B ₎ $ id) ∘ g₂  ↑⟨ natural η₂ refl ⟩
      η₂ ₍ A ₎ $ (id ∘ g₂)  ↓⟨ 𝒄𝒐𝒏𝒈 (η₂ ₍ A ₎) (∘-unitˡ 𝓒) ⟩
      η₂ ₍ A ₎ $ g₂         ∎
    }
