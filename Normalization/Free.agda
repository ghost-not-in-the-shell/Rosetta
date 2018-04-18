{-# OPTIONS --type-in-type         #-}
{-# OPTIONS --allow-unsolved-metas #-}
module Rosetta.Normalization.Free where
open import Rosetta.Prelude
open import Rosetta.Category.Core
open import Rosetta.Category.Sets
open import Rosetta.Normalization.βη-Equivalence
open import Rosetta.Normalization.Substitution
open import Rosetta.Normalization.Syntax
open import Rosetta.Normalization.Weakening

instance
  𝓣𝓶∣op : Op _⊢⋆_
  𝓣𝓶∣op = record
    { id  = ⌜ id ⌝
    ; _∘_ = _[_]
    }

𝓣𝓶 : Category
𝓣𝓶 = record
  { ob    = Con
  ; hom   = _⊢⋆_
  ; _∣_∼_ = _∼⋆_
  ; ∘-cong₂ = {!!}
  ; ∘-unitˡ = {!!}
  ; ∘-unitʳ = {!!}
  ; ∘-assoc = {!!}
  }

⌜-⌝ : 𝓦 ⟶ 𝓣𝓶
⌜-⌝ = record
  { _₀_      = id
  ; _₁_      = ⌜_⌝
  ; _₁-cong_ = λ { ≡-refl → refl }
  ; _resp-∘₀ = refl
  ; _resp-∘₂ = {!!}
  }
