module Rosetta.Category where
open import Agda.Primitive
open import Rosetta.Equality

record IsCategory {𝔠₁ 𝔠₂} {Obj : Set 𝔠₁} (Hom₍_,_₎ : Obj → Obj → Set 𝔠₂) : Set (𝔠₁ ⊔ 𝔠₂) where
  infixr 5 _∘_
  field
    id  : ∀ {A} → Hom₍ A , A ₎
    _∘_ : ∀ {A B C} → Hom₍ B , C ₎ → Hom₍ A , B ₎ → Hom₍ A , C ₎

    ∘-unitˡ : ∀ {A B} {f : Hom₍ A , B ₎} → id ∘ f ≡ f
    ∘-unitʳ : ∀ {A B} {f : Hom₍ A , B ₎} → f ∘ id ≡ f
    ∘-assoc : ∀ {A B C D} {f : Hom₍ A , B ₎} {g : Hom₍ B , C ₎} {h : Hom₍ C , D ₎}
      → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)

  id₍_₎ : ∀ A → Hom₍ A , A ₎
  id₍ A ₎ = id

open IsCategory ⦃...⦄ public

{-# DISPLAY IsCategory.id    _ = id    #-}
{-# DISPLAY IsCategory.id₍_₎ _ = id₍_₎ #-}
{-# DISPLAY IsCategory._∘_   _ = _∘_   #-}

record Category 𝔠₁ 𝔠₂ : Set (lsuc (𝔠₁ ⊔ 𝔠₂)) where
  field
    Obj : Set 𝔠₁
    Hom₍_,_₎ : Obj → Obj → Set 𝔠₂
    ⦃ category✓ ⦄ : IsCategory Hom₍_,_₎

open Category public using (Obj)

_₍_,_₎ : ∀ {𝔠₁ 𝔠₂} (𝓒 : Category 𝔠₁ 𝔠₂) → Obj 𝓒 → Obj 𝓒 → Set 𝔠₂
𝓒 ₍ A , B ₎ = let open Category 𝓒 in Hom₍ A , B ₎

