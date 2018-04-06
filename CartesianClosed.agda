{-# OPTIONS --type-in-type #-}
module Rosetta.CartesianClosed where
open import Rosetta.Category hiding (Op)

record Op {ob : Set} (_⟶_ : ob → ob → Set) : Set where
  infixr 6 _×_
  infixr 7 _⇒_
  field
    𝟙   : ob
    _×_ : ob → ob → ob
    _⇒_ : ob → ob → ob

    !     : ∀ {X} → X ⟶ 𝟙
    π₁    : ∀ {A B} → (A × B) ⟶ A
    π₂    : ∀ {A B} → (A × B) ⟶ B
    ⟨_,_⟩ : ∀ {A B X} → X ⟶ A → X ⟶ B → X ⟶ (A × B)
    ε     : ∀ {A B} → (A ⇒ B × A) ⟶ B
    λ₍_₎  : ∀ {A B X} → (X × A) ⟶ B → X ⟶ (A ⇒ B)

  π₁₍_,_₎ : ∀ A B → (A × B) ⟶ A
  π₁₍ A , B ₎ = π₁

  π₂₍_,_₎ : ∀ A B → (A × B) ⟶ B
  π₂₍ A , B ₎ = π₂

open Op ⦃...⦄ public hiding (𝟙; _×_; _⇒_)

record CartesianClosed (𝓒 : Category) : Set where
  field
    ⦃ op ⦄ : Op (𝓒 ∣_⟶_)

  open Op op using (𝟙; _×_; _⇒_)

  field
    .!-universal   : ∀ {X} {⁇ : 𝓒 ∣ X ⟶ 𝟙} → 𝓒 ∣ ⁇ ∼ !
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
    .λ-cong        : ∀ {A B X} {f₁ f₂ : 𝓒 ∣ X × A ⟶ B}
      → 𝓒 ∣ f₁ ∼ f₂
      → 𝓒 ∣ λ₍ f₁ ₎ ∼ λ₍ f₂ ₎
    .λ-commute     : ∀ {A B X} {f : 𝓒 ∣ X × A ⟶ B}
      → 𝓒 ∣ ε ∘ ⟨ λ₍ f ₎ ∘ π₁ , id ∘ π₂ ⟩ ∼ f
    .λ-universal   : ∀ {A B X} {f : 𝓒 ∣ X × A ⟶ B} {⁇ : 𝓒 ∣ X ⟶ A ⇒ B}
      → 𝓒 ∣ ε ∘ ⟨ ⁇ ∘ π₁ , id ∘ π₂ ⟩ ∼ f
      → 𝓒 ∣ ⁇ ∼ λ₍ f ₎

open CartesianClosed public hiding (op)
