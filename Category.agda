module Rosetta.Category where
open import Agda.Primitive
open import Rosetta.Equivalence
open import Rosetta.Setoid

record Structure {𝔠₁ 𝔠₂} {Obj : Set 𝔠₁} (Hom₍_,_₎ : Obj → Obj → Set 𝔠₂) : Set (𝔠₁ ⊔ 𝔠₂) where
  infixr 5 _∘_
  field
    id  : ∀ {A} → Hom₍ A , A ₎
    _∘_ : ∀ {A B C} → Hom₍ B , C ₎ → Hom₍ A , B ₎ → Hom₍ A , C ₎

open Structure ⦃...⦄ public

record Coherence {𝔠₁ 𝔠₂ 𝔠₃} {Obj : Set 𝔠₁} {Hom₍_,_₎ : Obj → Obj → Set 𝔠₂} ⦃ _ : Structure Hom₍_,_₎ ⦄ (_∼_ : ∀ {A B} → Hom₍ A , B ₎ → Hom₍ A , B ₎ → Set 𝔠₃) : Set (𝔠₁ ⊔ 𝔠₂ ⊔ 𝔠₃) where
  field
    ∘-unitˡ : ∀ {A B} {f : Hom₍ A , B ₎} → (id ∘ f) ∼ f
    ∘-unitʳ : ∀ {A B} {f : Hom₍ A , B ₎} → (f ∘ id) ∼ f
    ∘-assoc : ∀ {A B C D} {f : Hom₍ A , B ₎} {g : Hom₍ B , C ₎} {h : Hom₍ C , D ₎}
      → ((h ∘ g) ∘ f) ∼ (h ∘ (g ∘ f))

open Coherence ⦃...⦄ public

record Category 𝔠₁ 𝔠₂ 𝔠₃ : Set (lsuc (𝔠₁ ⊔ 𝔠₂ ⊔ 𝔠₃)) where
  field
    Obj : Set 𝔠₁
    Hom₍_,_₎ : Obj → Obj → Set 𝔠₂
    _∼_ : ∀ {A B} → Hom₍ A , B ₎ → Hom₍ A , B ₎ → Set 𝔠₃

--    ⦃ ∼‿
