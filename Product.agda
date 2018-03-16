module Rosetta.Product where
open import Agda.Primitive
open import Rosetta.Equality
open import Rosetta.Category

record Product {𝔠₁ 𝔠₂} (𝓒 : Category 𝔠₁ 𝔠₂) : Set (𝔠₁ ⊔ 𝔠₂) where
  field
    _×_ : Obj 𝓒 → Obj 𝓒 → Obj 𝓒
    π₁ : ∀ {A B} → 𝓒 ₍ A × B , A ₎
    π₂ : ∀ {A B} → 𝓒 ₍ A × B , B ₎
    ⟨_,_⟩ : ∀ {A B X} → 𝓒 ₍ X , A ₎ → 𝓒 ₍ X , B ₎ → 𝓒 ₍ X , A × B ₎

    ⟨,⟩-commute₁ : ∀ {A B X} {f : 𝓒 ₍ X , A ₎} {g : 𝓒 ₍ X , B ₎}
      → π₁ ∘ ⟨ f , g ⟩ ≡ f
    ⟨,⟩-commute₂ : ∀ {A B X} {f : 𝓒 ₍ X , A ₎} {g : 𝓒 ₍ X , B ₎}
      → π₂ ∘ ⟨ f , g ⟩ ≡ g
    ⟨,⟩-universal : ∀ {A B X} {f : 𝓒 ₍ X , A ₎} {g : 𝓒 ₍ X , B ₎} {⁇ : 𝓒 ₍ X , A × B ₎}
      → (⁇-commute₁ : π₁ ∘ ⁇ ≡ f)
      → (⁇-commute₂ : π₂ ∘ ⁇ ≡ g)
      → ⁇ ≡ ⟨ f , g ⟩

open Product public hiding (_×_)
