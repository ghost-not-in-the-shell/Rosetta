{-# OPTIONS --type-in-type #-}
module Rosetta.Functors where
open import Rosetta.Prelude
open import Rosetta.Equivalence
open import Rosetta.Category
open import Rosetta.Functor
open import Rosetta.NaturalTransformation
import Rosetta.DiagrammaticReasoning as DiagrammaticReasoning

instance
  [_,_]-op : ∀ 𝓒 𝓓 → Op (_⟹_ {𝓒} {𝓓})
  [ 𝓒 , 𝓓 ]-op = record
    { id  = record
      { _₍_₎    = λ A → id
      ; natural = ◁→▷ (∘-unitˡ 𝓓) (∘-unitʳ 𝓓)
      }
    ; _∘_ = λ β α → record
      { _₍_₎    = λ A → β ₍ A ₎ ∘ α ₍ A ₎
      ; natural = □↓□ (natural α) (natural β)
      }
    } where open DiagrammaticReasoning 𝓓

module _ {𝓒 𝓓} {𝓕 𝓖 : 𝓒 ⟶ 𝓓} where
  infix 4 _∼_
  _∼_ : Rel (𝓕 ⟹ 𝓖)
  α ∼ β = ∀ {A} → 𝓓 ∣ α ₍ A ₎ ∼ β ₍ A ₎

  instance
    ∼‿equiv : IsEquivalence _∼_
    ∼‿equiv = record
      { refl  =             refl
      ; sym   = λ α∼β     → sym   α∼β
      ; trans = λ α∼β β∼γ → trans α∼β β∼γ
      }

[_,_] : Category → Category → Category
[ 𝓒 , 𝓓 ] = record
  { ob = 𝓒 ⟶ 𝓓
  ; _∣_⟶_ = NaturalTransformation
  ; _∣_∼_ = _∼_
  ; ∘-cong₂ = λ β₁∼β₂ α₁∼α₂ → ∘-cong₂ 𝓓 β₁∼β₂ α₁∼α₂
  ; ∘-unitˡ = ∘-unitˡ 𝓓
  ; ∘-unitʳ = ∘-unitʳ 𝓓
  ; ∘-assoc = ∘-assoc 𝓓
  }

{-# DISPLAY _∼_ {𝓒} {𝓓} α β = [ 𝓒 , 𝓓 ] ∣ α ∼ β #-}
