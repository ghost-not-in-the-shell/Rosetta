module Rosetta.Setoid where
open import Agda.Primitive
open import Rosetta.Equivalence

record Setoid 𝔞₁ 𝔞₂ : Set (lsuc (𝔞₁ ⊔ 𝔞₂)) where
  constructor _,_
  field
    ⌜𝑨⌝ : Set 𝔞₁
    _∼_ : ⌜𝑨⌝ → ⌜𝑨⌝ → Set 𝔞₂
    ⦃ ∼‿equiv ⦄ : IsEquivalence _∼_

⌜_⌝ : ∀ {𝔞₁ 𝔞₂} → Setoid 𝔞₁ 𝔞₂ → Set 𝔞₁
⌜ 𝑨 ⌝ = let open Setoid 𝑨 in ⌜𝑨⌝

infix 4 ∼₍₎-syntax
∼₍₎-syntax : ∀ {𝔞₁ 𝔞₂} (𝑨 : Setoid 𝔞₁ 𝔞₂) → ⌜ 𝑨 ⌝ → ⌜ 𝑨 ⌝ → Set 𝔞₂
∼₍₎-syntax 𝑨 = let open Setoid 𝑨 in _∼_

syntax ∼₍₎-syntax 𝑨 x y = x ∼₍ 𝑨 ₎ y

{-# DISPLAY Setoid.⌜𝑨⌝ 𝑨     = ⌜ 𝑨 ⌝      #-}
{-# DISPLAY Setoid._∼_ 𝑨 x y = x ∼₍ 𝑨 ₎ y #-}

record _-Setoid⟶_ {𝔞₁ 𝔞₂} (𝑨 : Setoid 𝔞₁ 𝔞₂)
                  {𝔟₁ 𝔟₂} (𝑩 : Setoid 𝔟₁ 𝔟₂)
                  : Set (𝔞₁ ⊔ 𝔞₂ ⊔ 𝔟₁ ⊔ 𝔟₂) where
  field
    ⌈𝒇⌉ : ⌜ 𝑨 ⌝ → ⌜ 𝑩 ⌝
    cong : ∀ {x₁ x₂}
      →     x₁ ∼₍ 𝑨 ₎     x₂
      → ⌈𝒇⌉ x₁ ∼₍ 𝑩 ₎ ⌈𝒇⌉ x₂

open _-Setoid⟶_ public using (cong)

⌈_⌉ : ∀ {𝔞₁ 𝔞₂} {𝑨 : Setoid 𝔞₁ 𝔞₂}
        {𝔟₁ 𝔟₂} {𝑩 : Setoid 𝔟₁ 𝔟₂}
      → 𝑨 -Setoid⟶ 𝑩
      → ⌜ 𝑨 ⌝ → ⌜ 𝑩 ⌝
⌈ 𝒇 ⌉ = let open _-Setoid⟶_ 𝒇 in ⌈𝒇⌉

{-# DISPLAY _-Setoid⟶_.⌈𝒇⌉ 𝒇 = ⌈ 𝒇 ⌉ #-}
