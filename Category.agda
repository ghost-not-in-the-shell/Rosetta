{-# OPTIONS --type-in-type #-}
module Rosetta.Category where
open import Rosetta.Prelude
open import Rosetta.Equivalence

record Op {ob : Set} (_⟶_ : ob → ob → Set) : Set where
  infixr 5 _∘_
  field
    id  : ∀ {A} → A ⟶ A
    _∘_ : ∀ {A B C} → B ⟶ C → A ⟶ B → A ⟶ C

  id₍_₎ : ∀ A → A ⟶ A
  id₍ A ₎ = id

  private
    _⟵_ = flip _⟶_

  infixl 5 _∘̅_
  _∘̅_ : ∀ {A B C} → B ⟵ C → A ⟵ B → A ⟵ C
  _∘̅_ = flip _∘_

open Op ⦃...⦄ public

{-# DISPLAY Op.id    _ = id    #-}
{-# DISPLAY Op.id₍_₎ _ = id₍_₎ #-}
{-# DISPLAY Op._∘_   _ = _∘_   #-}
{-# DISPLAY Op._∘̅_   _ = _∘̅_   #-}

record Category : Set where
  infix 4 _∣_⟶_
  infix 4 _∣_∼_
  field
    ob : Set
    _∣_⟶_ : ob → ob → Set
    _∣_∼_ : ∀ {A B} → Rel (_∣_⟶_ A B)

  private
    _∼_ = _∣_∼_
    _⟶_ = _∣_⟶_

  field
    ⦃ op       ⦄ : Op _⟶_
    ⦃ .∼‿equiv ⦄ : ∀ {A B} → IsEquivalence (_∼_ {A} {B})
    .∘-cong₂ : ∀ {A B C} {f₁ f₂ : A ⟶ B} {g₁ g₂ : B ⟶ C}
      → g₁ ∼ g₂
      → f₁ ∼ f₂
      → (g₁ ∘ f₁) ∼ (g₂ ∘ f₂)
    .∘-unitˡ : ∀ {A B} {f : A ⟶ B} → (id ∘ f) ∼ f
    .∘-unitʳ : ∀ {A B} {f : A ⟶ B} → (f ∘ id) ∼ f
    .∘-assoc : ∀ {A B C D} {f : A ⟶ B} {g : B ⟶ C} {h : C ⟶ D}
      → ((h ∘ g) ∘ f) ∼ (h ∘ (g ∘ f))

  _∣_⟵_ = flip _∣_⟶_

  _ᵒᵖ : Category
  _ᵒᵖ = record
    { ob = ob
    ; _∣_⟶_ = _∣_⟵_
    ; _∣_∼_ = _∣_∼_
    ; op = record
      { id  = id
      ; _∘_ = _∘̅_
      }
    ; ∘-cong₂ = flip ∘-cong₂
    ; ∘-unitˡ = ∘-unitʳ
    ; ∘-unitʳ = ∘-unitˡ
    ; ∘-assoc = sym ∘-assoc
    }

open Category public hiding (op; ∼‿equiv)
