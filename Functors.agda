{-# OPTIONS --type-in-type #-}
module Rosetta.Functors where
open import Rosetta.CartesianClosed
open import Rosetta.Category
open import Rosetta.DiagramChasing
open import Rosetta.Equivalence
open import Rosetta.Functor
open import Rosetta.NaturalTransformation
open import Rosetta.Prelude

module _ {𝓒 𝓓 : Category} where
  id₁ : ∀ {𝓕 : 𝓒 ⟶ 𝓓} → 𝓕 ⟹ 𝓕
  id₁ = record
    { _₍_₎    = λ A → id
    ; natural = ◁→▷ 𝓓 (∘-unitˡ 𝓓) (∘-unitʳ 𝓓)
    }

  infixr 5 _∘₁_
  _∘₁_ : ∀ {𝓕 𝓖 𝓗 : 𝓒 ⟶ 𝓓} → 𝓖 ⟹ 𝓗 → 𝓕 ⟹ 𝓖 → 𝓕 ⟹ 𝓗
  β ∘₁ α = record
    { _₍_₎    = λ A → β ₍ A ₎ ∘ α ₍ A ₎
    ; natural = □↓□ 𝓓 (natural α) (natural β)
    }

  instance
    𝓝𝓪𝓽∣op : Op NaturalTransformation
    𝓝𝓪𝓽∣op = record
      { id  = id₁
      ; _∘_ = _∘₁_
      }

module _ {𝓒 𝓓 : Category} {𝓕 𝓖 : 𝓒 ⟶ 𝓓} where
  infix 4 𝓝𝓪𝓽∣_∼_
  𝓝𝓪𝓽∣_∼_ : Rel (𝓕 ⟹ 𝓖)
  𝓝𝓪𝓽∣ α ∼ β = ∀ {A} → 𝓓 ∣ α ₍ A ₎ ∼ β ₍ A ₎

  .𝓝𝓪𝓽∣∼-refl  : ∀ {α : 𝓕 ⟹ 𝓖} → 𝓝𝓪𝓽∣ α ∼ α
  .𝓝𝓪𝓽∣∼-sym   : ∀ {α β : 𝓕 ⟹ 𝓖} → 𝓝𝓪𝓽∣ α ∼ β → 𝓝𝓪𝓽∣ β ∼ α
  .𝓝𝓪𝓽∣∼-trans : ∀ {α β γ : 𝓕 ⟹ 𝓖} → 𝓝𝓪𝓽∣ α ∼ β → 𝓝𝓪𝓽∣ β ∼ γ → 𝓝𝓪𝓽∣ α ∼ γ
  𝓝𝓪𝓽∣∼-refl          = refl
  𝓝𝓪𝓽∣∼-sym   α∼β     = sym   α∼β
  𝓝𝓪𝓽∣∼-trans α∼β β∼γ = trans α∼β β∼γ

  instance
    𝓝𝓪𝓽∣∼-equiv : IsEquivalence 𝓝𝓪𝓽∣_∼_
    𝓝𝓪𝓽∣∼-equiv = record
      { refl  = λ {α}     → 𝓝𝓪𝓽∣∼-refl  {α}
      ; sym   = λ {α β}   → 𝓝𝓪𝓽∣∼-sym   {α} {β}
      ; trans = λ {α β γ} → 𝓝𝓪𝓽∣∼-trans {α} {β} {γ}
      }

[_,_] : Category → Category → Category
[ 𝓒 , 𝓓 ] = record
  { ob = 𝓒 ⟶ 𝓓
  ; _∣_⟶_ = NaturalTransformation
  ; _∣_∼_ = 𝓝𝓪𝓽∣_∼_
  ; ∘-cong₂ = λ β₁∼β₂ α₁∼α₂ → ∘-cong₂ 𝓓 β₁∼β₂ α₁∼α₂
  ; ∘-unitˡ = ∘-unitˡ 𝓓
  ; ∘-unitʳ = ∘-unitʳ 𝓓
  ; ∘-assoc = ∘-assoc 𝓓
  }

𝓝𝓪𝓽 : ∀ {𝓒 𝓓} → Category
𝓝𝓪𝓽 {𝓒} {𝓓} = [ 𝓒 , 𝓓 ]

{-# DISPLAY 𝓝𝓪𝓽∣_∼_ {𝓒} {𝓓} α β = 𝓝𝓪𝓽 ∣ α ∼ β #-}
