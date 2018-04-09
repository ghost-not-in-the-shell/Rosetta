{-# OPTIONS --type-in-type #-}
open import Rosetta.Category
module Rosetta.DiagrammaticReasoning (𝓒 : Category) where
open import Rosetta.Equivalence
open EqReasoning public

infixr 5 _⟩∘⟨_
._⟩∘⟨_ : ∀ {A B C}
           {f₁ f₂ : 𝓒 ∣ A ⟶ B}
           {g₁ g₂ : 𝓒 ∣ B ⟶ C}
         → 𝓒 ∣ g₁ ≈ g₂
         → 𝓒 ∣ f₁ ≈ f₂
         → 𝓒 ∣ g₁ ∘ f₁ ≈ g₂ ∘ f₂
_⟩∘⟨_ = ∘-cong₂ 𝓒

.◁→▷ : ∀ {A B₁ B₂ C}
         {f₁ : 𝓒 ∣ A ⟶ B₁} {g₁ : 𝓒 ∣ B₁ ⟶ C}
         {f₂ : 𝓒 ∣ A ⟶ B₂} {g₂ : 𝓒 ∣ B₂ ⟶ C}
         {g∘f : 𝓒 ∣ A ⟶ C}
       → 𝓒 ∣ g₁ ∘ f₁ ≈ g∘f
       → 𝓒 ∣ g₂ ∘ f₂ ≈ g∘f
       → 𝓒 ∣ g₁ ∘ f₁ ≈ g₂ ∘ f₂
◁→▷ {f₁ = f₁} {g₁} {f₂} {g₂} {g∘f} ◁ ▷ = begin
  g₁ ∘ f₁  ↓⟨ ◁ ⟩
  g∘f      ↑⟨ ▷ ⟩
  g₂ ∘ f₂  ∎

.□↓□ : ∀ {A₁ A₂ B₁ B₂ C₁ C₂}
         {f₁ : 𝓒 ∣ A₁ ⟶ B₁} {g₁ : 𝓒 ∣ B₁ ⟶ C₁}
         {f₂ : 𝓒 ∣ A₂ ⟶ B₂} {g₂ : 𝓒 ∣ B₂ ⟶ C₂}
         {a : 𝓒 ∣ A₁ ⟶ A₂} {b : 𝓒 ∣ B₁ ⟶ B₂} {c : 𝓒 ∣ C₁ ⟶ C₂}
       → 𝓒 ∣ f₂ ∘ a ≈ b ∘ f₁
       → 𝓒 ∣ g₂ ∘ b ≈ c ∘ g₁
       → 𝓒 ∣ (g₂ ∘ f₂) ∘ a ≈ c ∘ (g₁ ∘ f₁)
□↓□ {f₁ = f₁} {g₁} {f₂} {g₂} {a} {b} {c} □₁ □₂ = begin
  (g₂ ∘ f₂) ∘ a  ↓⟨ ∘-assoc 𝓒 ⟩
  g₂ ∘ (f₂ ∘ a)  ↓⟨ refl ⟩∘⟨ □₁ ⟩
  g₂ ∘ (b ∘ f₁)  ↑⟨ ∘-assoc 𝓒 ⟩
  (g₂ ∘ b) ∘ f₁  ↓⟨ □₂ ⟩∘⟨ refl ⟩
  (c ∘ g₁) ∘ f₁  ↓⟨ ∘-assoc 𝓒 ⟩
  c ∘ (g₁ ∘ f₁)  ∎

