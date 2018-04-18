{-# OPTIONS --type-in-type #-}
module Rosetta.Category.Core where
open import Rosetta.Prelude hiding (_∣_∼_)

record Op {ob : Set} (hom : ob → ob → Set) : Set where
  infixr 5 _∘_
  infixl 5 _∘̅_
  field
    id  : ∀ {A} → hom A A
    _∘_ : ∀ {A B C} → hom B C → hom A B → hom A C

  id₍_₎ : ∀ A → hom A A
  id₍ A ₎ = id

  _∘̅_ : ∀ {A B C} → hom A B → hom B C → hom A C
  f ∘̅ g = g ∘ f

open Op ⦃...⦄ public

{-# DISPLAY Op.id    _ = id    #-}
{-# DISPLAY Op.id₍_₎ _ = id₍_₎ #-}
{-# DISPLAY Op._∘_   _ = _∘_   #-}
{-# DISPLAY Op._∘̅_   _ = _∘̅_   #-}

record Category : Set where
  infix 4 _∣_∼_
  field
    ob     : Set
    hom    : ob → ob → Set
    ⦃ op ⦄ : Op hom
    _∣_∼_  : ∀ {A B} → hom A B → hom A B → Set
  private _∼_ = _∣_∼_
  field
    ⦃ .∼‿equiv ⦄ : ∀ {A B} → IsEquivalence (_∼_ {A} {B})
    .∘-cong₂ : ∀ {A B C} {f₁ f₂ : hom A B} {g₁ g₂ : hom B C}
      → g₁ ∼ g₂
      → f₁ ∼ f₂
      → (g₁ ∘ f₁) ∼ (g₂ ∘ f₂)
    .∘-unitˡ : ∀ {A B} {f : hom A B} → (id ∘ f) ∼ f
    .∘-unitʳ : ∀ {A B} {f : hom A B} → (f ∘ id) ∼ f
    .∘-assoc : ∀ {A B C D} {f : hom A B} {g : hom B C} {h : hom C D}
      → ((h ∘ g) ∘ f) ∼ (h ∘ (g ∘ f))

  𝒉𝒐𝒎 : ob → ob → Setoid
  𝒉𝒐𝒎 A B = record
    { ∣_∣   = hom A B
    ; _∣_∼_ = _∼_
    }

  _ᵒᵖ : Category
  _ᵒᵖ = record
    { ob    = ob
    ; hom   = λ B A → hom A B
    ; op    = record
      { id  = id
      ; _∘_ = _∘̅_
      }
    ; _∣_∼_ = _∼_
    ; ∘-cong₂ = λ f₁∼f₂ g₁∼g₂ → ∘-cong₂ g₁∼g₂ f₁∼f₂
    ; ∘-unitˡ = ∘-unitʳ
    ; ∘-unitʳ = ∘-unitˡ
    ; ∘-assoc = sym ∘-assoc
    }

open Category public

infix 4 _∣_⟶_
_∣_⟶_ : ∀ (𝓒 : Category) → ob 𝓒 → ob 𝓒 → Set
𝓒 ∣ A ⟶ B = hom 𝓒 A B

{-# DISPLAY hom 𝓒 A B = 𝓒 ∣ A ⟶ B #-}

module CategoryReasoning (𝓒 : Category) where
  module _ {A B} where open SetoidReasoning (𝒉𝒐𝒎 𝓒 A B) public

  infixr 5 _⟩∘⟨_
  ._⟩∘⟨_ : ∀ {A B C}
             {f₁ f₂ : 𝓒 ∣ A ⟶ B}
             {g₁ g₂ : 𝓒 ∣ B ⟶ C}
           → 𝓒 ∣ g₁ ∼ g₂
           → 𝓒 ∣ f₁ ∼ f₂
           → 𝓒 ∣ g₁ ∘ f₁ ∼ g₂ ∘ f₂
  _⟩∘⟨_ = ∘-cong₂ 𝓒

infix 4 _∣_≃_
record _∣_≃_ (𝓒 : Category) (A B : ob 𝓒) : Set where
  field
    to   : 𝓒 ∣ A ⟶ B
    from : 𝓒 ∣ B ⟶ A
    .inverseˡ : 𝓒 ∣ from ∘ to ∼ id
    .inverseʳ : 𝓒 ∣ to ∘ from ∼ id

record Functor (𝓒 𝓓 : Category) : Set where
  infix 6 _₀_
  infix 6 _₁_
  infix 6 _₁-cong_
  field
    _₀_ : ob 𝓒 → ob 𝓓
    _₁_ : ∀ {A B} → 𝓒 ∣ A ⟶ B → 𝓓 ∣ _₀_ A ⟶ _₀_ B
    ._₁-cong_ : ∀ {A B} {f g : 𝓒 ∣ A ⟶ B}
      → 𝓒 ∣ f ∼ g
      → 𝓓 ∣ _₁_ f ∼ _₁_ g

    ._resp-∘₀ : ∀ {A} → 𝓓 ∣ _₁_ id₍ A ₎ ∼ id₍ _₀_ A ₎
    ._resp-∘₂ : ∀ {A B C} {f : 𝓒 ∣ A ⟶ B} {g : 𝓒 ∣ B ⟶ C}
      → 𝓓 ∣ _₁_ (g ∘ f) ∼ (_₁_ g) ∘ (_₁_ f)

open Functor public

infix 4 _⟶_
_⟶_ = Functor

_ᵒᵖ→ : ∀ {𝓒 𝓓} → 𝓒 ⟶ 𝓓 → 𝓒 ᵒᵖ ⟶ 𝓓 ᵒᵖ
𝓕 ᵒᵖ→ = record
  { _₀_      = 𝓕 ₀_
  ; _₁_      = 𝓕 ₁_
  ; _₁-cong_ = 𝓕 ₁-cong_
  ; _resp-∘₀ = 𝓕 resp-∘₀
  ; _resp-∘₂ = 𝓕 resp-∘₂
  }

{-# DISPLAY Functor = _⟶_ #-}

record NaturalTransformation {𝓒 𝓓} (𝓕 𝓖 : 𝓒 ⟶ 𝓓) : Set where
  infix 6 _at_
  field
    _at_ : ∀ A → 𝓓 ∣ 𝓕 ₀ A ⟶ 𝓖 ₀ A
    .natural : ∀ {A B} {f : 𝓒 ∣ A ⟶ B}
      → 𝓓 ∣ _at_ B ∘ 𝓕 ₁ f ∼ 𝓖 ₁ f ∘ _at_ A

  open CategoryReasoning 𝓓

  .natural∼ : ∀ {A B} {f g : 𝓒 ∣ A ⟶ B}
    → 𝓒 ∣ f ∼ g
    → 𝓓 ∣ _at_ B ∘ 𝓕 ₁ f ∼ 𝓖 ₁ g ∘ _at_ A
  natural∼ {A} {B} {f} {g} f∼g = begin
    _at_ B ∘ 𝓕 ₁ f  ↓⟨ refl ⟩∘⟨ 𝓕 ₁-cong f∼g ⟩
    _at_ B ∘ 𝓕 ₁ g  ↓⟨ natural ⟩
    𝓖 ₁ g ∘ _at_ A  ∎

open NaturalTransformation public

infix 4 _⟹_
_⟹_ = NaturalTransformation
