{-# OPTIONS --type-in-type #-}
module Rosetta.Category.CartesianClosed where
open import Rosetta.Category.Core

record Op✓ {ob : Set} (hom : ob → ob → Set) : Set where
  infixr 6 _×_
  infixl 7 _^_
  infix  7 ƛ_
  field
    𝟙   : ob
    _×_ : ob → ob → ob
    _^_ : ob → ob → ob

    !     : ∀ {X} → hom X 𝟙
    π₁    : ∀ {A B} → hom (A × B) A
    π₂    : ∀ {A B} → hom (A × B) B
    ⟨_,_⟩ : ∀ {A B X} → hom X A → hom X B → hom X (A × B)
    ε     : ∀ {A B} → hom (B ^ A × A) B
    ƛ_    : ∀ {A B X} → hom (X × A) B → hom X (B ^ A)

  !₍_₎ : ∀ X → hom X 𝟙
  !₍ X ₎ = !

  π₁₍_,_₎ : ∀ A B → hom (A × B) A
  π₁₍ A , B ₎ = π₁

  π₂₍_,_₎ : ∀ A B → hom (A × B) B
  π₂₍ A , B ₎ = π₂

  ε₍_,_₎ : ∀ A B → hom (B ^ A × A) B
  ε₍ A , B ₎ = ε

  module Functorial ⦃ _ : Op hom ⦄ where
    infixr 6 _×₁_
    _×₁_ : ∀ {A₁ A₂ B₁ B₂} → hom A₁ B₁ → hom A₂ B₂ → hom (A₁ × A₂) (B₁ × B₂)
    f₁ ×₁ f₂ = ⟨ f₁ ∘ π₁ , f₂ ∘ π₂ ⟩

    _^₁_ : ∀ B {A₁ A₂} → hom A₂ A₁ → hom (B ^ A₁) (B ^ A₂)
    B ^₁ f = ƛ (ε ∘ id ×₁ f)

  open Functorial public

open Op✓ ⦃...⦄ public hiding (𝟙; _×_; _^_)

{-# DISPLAY Op✓.!     _ = !     #-}
{-# DISPLAY Op✓.π₁    _ = π₁    #-}
{-# DISPLAY Op✓.π₂    _ = π₂    #-}
{-# DISPLAY Op✓.⟨_,_⟩ _ = ⟨_,_⟩ #-}
{-# DISPLAY Op✓.ε     _ = ε     #-}
{-# DISPLAY Op✓.ƛ_    _ = ƛ_    #-}
{-# DISPLAY Op✓._×₁_  _ = _×₁_  #-}
{-# DISPLAY Op✓._^₁_  _ = _^₁_  #-}

record CartesianClosed (𝓒 : Category) : Set where
  field
    ⦃ op✓ ⦄ : Op✓ (𝓒 ∣_⟶_)

  open Op✓ op✓ using (𝟙; _×_; _^_)

  field
    .!-universal   : ∀ {X} {⁇ : 𝓒 ∣ X ⟶ 𝟙}
      → 𝓒 ∣ ⁇ ∼ !
    .⟨,⟩-cong₂     : ∀ {A B X} {f₁ f₂ : 𝓒 ∣ X ⟶ A} {g₁ g₂ : 𝓒 ∣ X ⟶ B}
      → 𝓒 ∣ f₁ ∼ f₂
      → 𝓒 ∣ g₁ ∼ g₂
      → 𝓒 ∣ ⟨ f₁ , g₁ ⟩ ∼ ⟨ f₂ , g₂ ⟩
    .⟨,⟩-commute₁  : ∀ {A B X} {f : 𝓒 ∣ X ⟶ A} {g : 𝓒 ∣ X ⟶ B}
      → 𝓒 ∣ π₁ ∘ ⟨ f , g ⟩ ∼ f
    .⟨,⟩-commute₂  : ∀ {A B X} {f : 𝓒 ∣ X ⟶ A} {g : 𝓒 ∣ X ⟶ B}
      → 𝓒 ∣ π₂ ∘ ⟨ f , g ⟩ ∼ g
    .⟨,⟩-universal : ∀ {A B X} {f : 𝓒 ∣ X ⟶ A} {g : 𝓒 ∣ X ⟶ B} {⁇ : 𝓒 ∣ X ⟶ A × B}
      → 𝓒 ∣ π₁ ∘ ⁇ ∼ f
      → 𝓒 ∣ π₂ ∘ ⁇ ∼ g
      → 𝓒 ∣ ⁇ ∼ ⟨ f , g ⟩
    .ƛ-cong        : ∀ {A B X} {f₁ f₂ : 𝓒 ∣ X × A ⟶ B}
      → 𝓒 ∣ f₁ ∼ f₂
      → 𝓒 ∣ ƛ f₁ ∼ ƛ f₂
    .ƛ-commute     : ∀ {A B X} {f : 𝓒 ∣ X × A ⟶ B}
      → 𝓒 ∣ ε ∘ ƛ f ×₁ id ∼ f
    .ƛ-universal   : ∀ {A B X} {f : 𝓒 ∣ X × A ⟶ B} {⁇ : 𝓒 ∣ X ⟶ B ^ A}
      → 𝓒 ∣ ε ∘ ⁇ ×₁ id ∼ f
      → 𝓒 ∣ ⁇ ∼ ƛ f

open CartesianClosed public
