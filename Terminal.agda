module Rosetta.Terminal where
open import Agda.Primitive
open import Rosetta.Equality
open import Rosetta.Category

record Terminal {𝔠₁ 𝔠₂} (𝓒 : Category 𝔠₁ 𝔠₂) : Set (𝔠₁ ⊔ 𝔠₂) where
  field
    𝟙 : Obj 𝓒
    ! : ∀ {X} → 𝓒 ₍ X , 𝟙 ₎

    !-universal : ∀ {X} {⁇ : 𝓒 ₍ X , 𝟙 ₎} → ⁇ ≡ !

open Terminal public hiding (𝟙)
