{-# OPTIONS --type-in-type #-}
module Rosetta.Category where
open import Rosetta.Equivalence
open import Rosetta.Prelude

record Op {ob : Set} (hom : ob → ob → Set) : Set where
  infixr 5 _∘_
  infixl 5 _∘̅_
  field
    id  : ∀ {A} → hom A A
    _∘_ : ∀ {A B C} → hom B C → hom A B → hom A C

  id₍_₎ : ∀ A → hom A A
  id₍ A ₎ = id

  _∘̅_ : ∀ {A B C} → hom C B → hom B A → hom C A
  _∘̅_ = flip _∘_

open Op ⦃...⦄ public

{-# DISPLAY Op.id    _ = id    #-}
{-# DISPLAY Op.id₍_₎ _ = id₍_₎ #-}
{-# DISPLAY Op._∘_   _ = _∘_   #-}
{-# DISPLAY Op._∘̅_   _ = _∘̅_   #-}

record Category : Set where
  infix 4 _≈_
  field
    ob  : Set
    hom : ob → ob → Set
    _≈_ : ∀ {A B} → Rel (hom A B)

    ⦃ op       ⦄ : Op hom
    ⦃ .≈-equiv ⦄ : ∀ {A B} → IsEquivalence (_≈_ {A} {B})
    .∘-cong₂ : ∀ {A B C} {f₁ f₂ : hom A B} {g₁ g₂ : hom B C}
      → g₁ ≈ g₂
      → f₁ ≈ f₂
      → g₁ ∘ f₁ ≈ g₂ ∘ f₂
    .∘-unitˡ : ∀ {A B} {f : hom A B} → id ∘ f ≈ f
    .∘-unitʳ : ∀ {A B} {f : hom A B} → f ∘ id ≈ f
    .∘-assoc : ∀ {A B C D} {f : hom A B} {g : hom B C} {h : hom C D}
      → (h ∘ g) ∘ f ≈ h ∘ (g ∘ f)

  𝒉𝒐𝒎 : ob → ob → Setoid
  𝒉𝒐𝒎 A B = record
    { ∣_∣ = hom A B
    ; _∼_ = _≈_
    }

  _ᵒᵖ : Category
  _ᵒᵖ = record
    { ob  = ob
    ; hom = flip hom
    ; _≈_ = _≈_
    ; op = record
      { id  = id
      ; _∘_ = _∘̅_
      }
    ; ∘-cong₂ = flip ∘-cong₂
    ; ∘-unitˡ = ∘-unitʳ
    ; ∘-unitʳ = ∘-unitˡ
    ; ∘-assoc = sym ∘-assoc
    }

open Category public hiding (_≈_)

infix 4 _∣_⟶_
infix 4 _∣_⟵_
_∣_⟶_ : ∀ 𝓒 → ob 𝓒 → ob 𝓒 → Set
_∣_⟵_ : ∀ 𝓒 → ob 𝓒 → ob 𝓒 → Set
𝓒 ∣ A ⟶ B = hom 𝓒      A B
𝓒 ∣ A ⟵ B = hom (𝓒 ᵒᵖ) A B

infix 4 _∣_≈_
_∣_≈_ : ∀ 𝓒 {A B} → Rel (𝓒 ∣ A ⟶ B)
𝓒 ∣ f ≈ g = let open Category 𝓒 in f ≈ g

{-# DISPLAY Category.hom = _∣_⟶_ #-}
{-# DISPLAY Category._≈_ = _∣_≈_ #-}
