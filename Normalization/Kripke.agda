{-# OPTIONS --type-in-type #-}
module Rosetta.Normalization.Kripke where
open import Rosetta.Prelude
open import Rosetta.Category.Core
open import Rosetta.Normalization.Syntax
open import Rosetta.Normalization.Weakening

record Kripke : Set where
  field
    𝑾 : Set
    _≤_ : 𝑾 → 𝑾 → Set
    ≤-refl  : ∀ {w} → w ≤ w
    ≤-trans : ∀ {w w′ w″} → w ≤ w′ → w′ ≤ w″ → w ≤ w″
    _⊩𝒐 : 𝑾 → Set
    ⊩𝒐-mono : ∀ {w w′} → w ≤ w′ → w ⊩𝒐 → w′ ⊩𝒐

  infix 4 _⊩_
  _⊩_ : 𝑾 → Ty → Set
  w ⊩ 𝒐     = w ⊩𝒐
  w ⊩ A ⇒ B = ∀ {w′} → w ≤ w′ → w′ ⊩ A → w′ ⊩ B

  ⊩‿mono : ∀ {A w w′} → w ≤ w′ → w ⊩ A → w′ ⊩ A
  ⊩‿mono {𝒐} = ⊩𝒐-mono
  ⊩‿mono {A ⇒ B} w≤w′ w⊩A⇒B w′≤w″ w″⊩A = w⊩A⇒B (≤-trans w≤w′ w′≤w″) w″⊩A

  infix 4 _⊩⋆_
  _⊩⋆_ : 𝑾 → Con → Set
  w ⊩⋆ As = All (w ⊩_) As

  ⊩⋆-mono : ∀ {As w w′} → w ≤ w′ → w ⊩⋆ As → w′ ⊩⋆ As
  ⊩⋆-mono w≤w′ w⊩⋆As = map (λ {A} → ⊩‿mono {A} w≤w′) w⊩⋆As

  infix 4 _⊨_
  _⊨_ : Con → Ty → Set
  Γ ⊨ A = ∀ {w} → w ⊩⋆ Γ → w ⊩ A

  sound : ∀ {Γ A} → Γ ⊢ A → Γ ⊨ A
  sound (var x)   w⊩⋆Γ           = lookup w⊩⋆Γ x
  sound (lam t)   w⊩⋆Γ w≤w′ w′⊩A = sound t (w′⊩A ∷ ⊩⋆-mono w≤w′ w⊩⋆Γ)
  sound (app t u) w⊩⋆Γ           = sound t w⊩⋆Γ ≤-refl (sound u w⊩⋆Γ)

universal : Kripke
universal = record
  { 𝑾   = Con
  ; _≤_ = λ Δ Γ → Γ ≽ Δ
  ; ≤-refl  = id
  ; ≤-trans = _∘_
  ; _⊩𝒐     = {!!}
  ; ⊩𝒐-mono = {!!}
  }
