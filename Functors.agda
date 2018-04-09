{-# OPTIONS --type-in-type #-}
module Rosetta.Functors where
open import Rosetta.CartesianClosed
open import Rosetta.Category
open import Rosetta.Equivalence
open import Rosetta.Functor
open import Rosetta.NaturalTransformation
open import Rosetta.Prelude
open import Rosetta.Setoids
import Rosetta.DiagrammaticReasoning as DiagrammaticReasoning

module _ {𝓒 𝓓 : Category} where
  open DiagrammaticReasoning 𝓓

  infixr 5 _⋆_
  _⋆_ : ∀ {𝓕 𝓖 𝓗 : 𝓒 ⟶ 𝓓} → 𝓖 ⟹ 𝓗 → 𝓕 ⟹ 𝓖 → 𝓕 ⟹ 𝓗
  β ⋆ α = record
    { _₍_₎    = λ A → β ₍ A ₎ ∘ α ₍ A ₎
    ; natural = □↓□ (natural  α) (natural β)
    }

  instance
    𝓝𝓪𝓽-op : Op (_⟹_ {𝓒} {𝓓})
    𝓝𝓪𝓽-op = record
      { id  = record
        { _₍_₎    = λ A → id
        ; natural = ◁→▷ (∘-unitˡ 𝓓) (∘-unitʳ 𝓓) }
      ; _∘_ = _⋆_
      }

module _ {𝓒 𝓓 : Category} {𝓕 𝓖 : 𝓒 ⟶ 𝓓} where
  infix 4 𝓝𝓪𝓽∣_≈_
  𝓝𝓪𝓽∣_≈_ : Rel (𝓕 ⟹ 𝓖)
  𝓝𝓪𝓽∣ α ≈ β = ∀ A → 𝓓 ∣ α ₍ A ₎ ≈ β ₍ A ₎

  .𝓝𝓪𝓽≈-refl  : ∀ {α : 𝓕 ⟹ 𝓖} → 𝓝𝓪𝓽∣ α ≈ α
  .𝓝𝓪𝓽≈-sym   : ∀ {α β : 𝓕 ⟹ 𝓖} → 𝓝𝓪𝓽∣ α ≈ β → 𝓝𝓪𝓽∣ β ≈ α
  .𝓝𝓪𝓽≈-trans : ∀ {α β γ : 𝓕 ⟹ 𝓖} → 𝓝𝓪𝓽∣ α ≈ β → 𝓝𝓪𝓽∣ β ≈ γ → 𝓝𝓪𝓽∣ α ≈ γ
  𝓝𝓪𝓽≈-refl          = λ A → refl
  𝓝𝓪𝓽≈-sym   α≈β     = λ A → sym   (α≈β A)
  𝓝𝓪𝓽≈-trans α≈β β≈γ = λ A → trans (α≈β A) (β≈γ A)

  instance
    𝓝𝓪𝓽≈-equiv : IsEquivalence 𝓝𝓪𝓽∣_≈_
    𝓝𝓪𝓽≈-equiv = record
      { refl  = λ {α}     → 𝓝𝓪𝓽≈-refl  {α}
      ; sym   = λ {α β}   → 𝓝𝓪𝓽≈-sym   {α} {β}
      ; trans = λ {α β γ} → 𝓝𝓪𝓽≈-trans {α} {β} {γ}
      }

[_,_] : Category → Category → Category
[ 𝓒 , 𝓓 ] = record
  { ob  = 𝓒 ⟶ 𝓓
  ; hom = NaturalTransformation
  ; _≈_ = 𝓝𝓪𝓽∣_≈_
  ; ∘-cong₂ = λ β₁≈β₂ α₁≈α₂ A → ∘-cong₂ 𝓓 (β₁≈β₂ A) (α₁≈α₂ A)
  ; ∘-unitˡ = λ A → ∘-unitˡ 𝓓
  ; ∘-unitʳ = λ A → ∘-unitʳ 𝓓
  ; ∘-assoc = λ A → ∘-assoc 𝓓
  }

{-# DISPLAY 𝓝𝓪𝓽∣_≈_ {𝓒} {𝓓} α β = [ 𝓒 , 𝓓 ] ∣ α ≈ β #-}
