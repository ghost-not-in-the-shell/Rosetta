module Rosetta.Functor where
open import Agda.Primitive
open import Rosetta.Equality
open import Rosetta.Category

record Functor {𝔠₁ 𝔠₂} (𝓒 : Category 𝔠₁ 𝔠₂)
               {𝔡₁ 𝔡₂} (𝓓 : Category 𝔡₁ 𝔡₂)
               : Set (𝔠₁ ⊔ 𝔠₂ ⊔ 𝔡₁ ⊔ 𝔡₂) where
  field
    𝓕₀ : Obj 𝓒 → Obj 𝓓
    𝓕₁ : ∀ {A B} → 𝓒 ₍ A , B ₎ → 𝓓 ₍ 𝓕₀(A) , 𝓕₀(B) ₎
    _resp-∘₀ : ∀ {A} → 𝓕₁(id₍ A ₎) ≡ id₍ 𝓕₀(A) ₎
    _resp-∘₂ : ∀ {A B C} {f : 𝓒 ₍ A , B ₎} {g : 𝓒 ₍ B , C ₎}
      → 𝓕₁(g ∘ f) ≡ 𝓕₁(g) ∘ 𝓕₁(f)

infix 0 _⟶_
_⟶_ = Functor

open Functor hiding (𝓕₀; 𝓕₁) public

_₀_ : ∀ {𝔠₁ 𝔠₂} {𝓒 : Category 𝔠₁ 𝔠₂}
        {𝔡₁ 𝔡₂} {𝓓 : Category 𝔡₁ 𝔡₂}
      → (𝓕 : 𝓒 ⟶ 𝓓)
      → Obj 𝓒 → Obj 𝓓
𝓕 ₀(A) = let open Functor 𝓕 in 𝓕₀(A)

_₁_ : ∀ {𝔠₁ 𝔠₂} {𝓒 : Category 𝔠₁ 𝔠₂}
        {𝔡₁ 𝔡₂} {𝓓 : Category 𝔡₁ 𝔡₂}
      → (𝓕 : 𝓒 ⟶ 𝓓)
      → ∀ {A B} → 𝓒 ₍ A , B ₎ → 𝓓 ₍ 𝓕 ₀(A) , 𝓕 ₀(B) ₎
𝓕 ₁(f) = let open Functor 𝓕 in 𝓕₁(f)
