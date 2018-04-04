{-# OPTIONS --type-in-type #-}
module Rosetta.Category where
open import Rosetta.Equivalence

record Op {ob} (hom : ob → ob → Set) : Set where
  infixr 5 _∘_
  field
    id  : ∀ {A} → hom A A
    _∘_ : ∀ {A B C} → hom B C → hom A B → hom A C

  id₍_₎ : ∀ A → hom A A
  id₍ A ₎ = id

open Op ⦃...⦄ public

record Category : Set where
  infix 4 _∣_∼_
  field
    ob : Set
    hom : ob → ob → Set
    _∣_∼_ : ∀ {A B} → Rel (hom A B)

    ⦃ op       ⦄ : Op hom
    ⦃ .∼‿equiv ⦄ : ∀ {A B} → IsEquivalence (_∣_∼_ {A} {B})

  private
    _∼_ = _∣_∼_

  field
    .∘-cong₂ : ∀ {A B C} {f₁ f₂ : hom A B} {g₁ g₂ : hom B C}
      → g₁ ∼ g₂
      → f₁ ∼ f₂
      → (g₁ ∘ f₁) ∼ (g₂ ∘ f₂)
    .∘-unitˡ : ∀ {A B} {f : hom A B} → (id ∘ f) ∼ f
    .∘-unitʳ : ∀ {A B} {f : hom A B} → (f ∘ id) ∼ f
    .∘-assoc : ∀ {A B C D} {f : hom A B} {g : hom B C} {h : hom C D}
      → ((h ∘ g) ∘ f) ∼ (h ∘ (g ∘ f))

open Category public hiding (op; ∼‿equiv)

_₍_,_₎ = hom
