{-# OPTIONS --type-in-type #-}
module Rosetta.Functors where
open import Rosetta.Equivalence
open import Rosetta.Category
open import Rosetta.Functor
open import Rosetta.NaturalTransformation
open import Rosetta.DiagrammaticReasoning

instance
  [_,_]-op : ∀ 𝓒 𝓓 → Op (NaturalTransformation {𝓒} {𝓓})
  [ 𝓒 , 𝓓 ]-op = record
    { id  = record
      { _₍_₎    = λ A → id
      ; natural = ◁→▷ 𝓓 (∘-unitˡ 𝓓) (∘-unitʳ 𝓓)
      }
    ; _∘_ = λ β α → record
      { _₍_₎    = λ A → β ₍ A ₎ ∘ α ₍ A ₎
      ; natural = □↓□ 𝓓 (natural α) (natural β)
      }
    }

_∼_ : ∀ {𝓒 𝓓} {𝓕 𝓖 : 𝓒 ⟶ 𝓓} → Rel (𝓕 ⟹ 𝓖)
_∼_ {𝓓 = 𝓓} α β = ∀ A → 𝓓 ∣ α ₍ A ₎ ∼ β ₍ A ₎

instance
  ∼‿equiv : ∀ {𝓒 𝓓} {𝓕 𝓖 : 𝓒 ⟶ 𝓓} → IsEquivalence (_∼_ {𝓕 = 𝓕} {𝓖})
  ∼‿equiv = record
    { refl₍_₎ = λ α A → refl₍ α ₍ A ₎ ₎
    ; sym     = λ α∼β A → sym (α∼β A)
    ; trans   = λ α∼β β∼γ A → trans (α∼β A) (β∼γ A)
    }

[_,_] : Category → Category → Category
[ 𝓒 , 𝓓 ] = record
  { ob    = 𝓒 ⟶ 𝓓
  ; hom   = _⟹_
  ; _∣_∼_ = _∼_
  ; ∘-cong₂ = λ β₁∼β₂ α₁∼α₂ A → ∘-cong₂ 𝓓 (β₁∼β₂ A) (α₁∼α₂ A)
  ; ∘-unitˡ = λ A → ∘-unitˡ 𝓓
  ; ∘-unitʳ = λ A → ∘-unitʳ 𝓓
  ; ∘-assoc = λ A → ∘-assoc 𝓓
  }
