{-# OPTIONS --type-in-type #-}
module Rosetta.HomFunctor where
open import Rosetta.Equivalence
open import Rosetta.Category
open import Rosetta.Functor
open import Rosetta.Setoids
open import Rosetta.DiagrammaticReasoning

_₍_,-₎ : ∀ 𝓒 → ob 𝓒 → 𝓒 ⟶ 𝓢𝓮𝓽
𝓒 ₍ A ,-₎ =
  let 𝓒₍A,_₎₀ : ob 𝓒 → Setoid
      𝓒₍A,_₎₀ X = record
        { ∣_∣   = 𝓒 ₍ A , X ₎
        ; _∣_∼_ = 𝓒 ∣_∼_
        }

      𝓒₍A,_₎₁ : ∀ {X Y} → 𝓒 ₍ X , Y ₎ → 𝓒₍A, X ₎₀ -𝓢𝓮𝓽⟶ 𝓒₍A, Y ₎₀
      𝓒₍A,_₎₁ f = record
        { _₀_ = f ∘_
        ; _₁_ = whiskerʳ 𝓒
        }
  in record
  { _₀_ = 𝓒₍A,_₎₀
  ; _₁_ = 𝓒₍A,_₎₁
  ; _₁-cong_ = λ f₁∼f₂ x₁∼x₂ → ∘-cong₂ 𝓒 f₁∼f₂ x₁∼x₂
  ; _-resp-∘₀ = λ { {x = x₁} {x₂} x₁∼x₂ → begin
    id ∘ x₁  ↓⟨ ∘-unitˡ 𝓒 ⟩
    x₁       ↓⟨ x₁∼x₂ ⟩
    x₂       ∎ }
  ; _-resp-∘₂ = λ { {f = f} {g} {x₁} {x₂} x₁∼x₂ → begin
    (g ∘ f) ∘ x₁  ↓⟨ whiskerʳ 𝓒 x₁∼x₂ ⟩
    (g ∘ f) ∘ x₂  ↓⟨ ∘-assoc 𝓒 ⟩
    g ∘ (f ∘ x₂)  ∎ }
  }

_₍-,_₎ : ∀ 𝓒 → ob 𝓒 → 𝓒 ᵒᵖ ⟶ 𝓢𝓮𝓽
𝓒 ₍-, B ₎ =
  record
  { _₀_ = {!!}
  ; _₁_ = {!!}
  ; _₁-cong_ = {!!}
  ; _-resp-∘₀ = {!!}
  ; _-resp-∘₂ = {!!}
  }
