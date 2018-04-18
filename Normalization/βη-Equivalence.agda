{-# OPTIONS --type-in-type #-}
module Rosetta.Normalization.βη-Equivalence where
open import Rosetta.Prelude
open import Rosetta.Category.Core
open import Rosetta.Normalization.Substitution
open import Rosetta.Normalization.Syntax
open import Rosetta.Normalization.Weakening

infix 4 _∼_
data _∼_ {Γ} : ∀ {A} → Γ ⊢ A → Γ ⊢ A → Set where
  ∼‿refl  : ∀ {A} {t : Γ ⊢ A}
    → t ∼ t
  ∼‿sym   : ∀ {A} {t₁ t₂ : Γ ⊢ A}
    → t₁ ∼ t₂
    → t₂ ∼ t₁
  ∼‿trans : ∀ {A} {t₁ t₂ t₃ : Γ ⊢ A}
    → t₁ ∼ t₂
    → t₂ ∼ t₃
    → t₁ ∼ t₃

  lam : ∀ {A B} {t₁ t₂ : A ∷ Γ ⊢ B}
    → t₁ ∼ t₂
    → lam t₁ ∼ lam t₂
  app : ∀ {A B} {t₁ t₂ : Γ ⊢ A ⇒ B} {u₁ u₂ : Γ ⊢ A}
    → t₁ ∼ t₂
    → u₁ ∼ u₂
    → app t₁ u₁ ∼ app t₂ u₂

  β : ∀ {A B} (t : A ∷ Γ ⊢ B) (u : Γ ⊢ A)
    → app (lam t) u ∼ subst⊢ (u ∷ ⌜ id ⌝) t
  η : ∀ {A B} (t : Γ ⊢ A ⇒ B)
    → lam (app (rename⊢ (skip id) t) (var ze)) ∼ t

infix  4 _∼⋆_
infixr 5 _∷_
data _∼⋆_ {Γ} : ∀ {As} → Γ ⊢⋆ As → Γ ⊢⋆ As → Set where
  []  : [] ∼⋆ []
  _∷_ : ∀ {A As} {t₁ t₂ : Γ ⊢ A} {ts₁ ts₂ : Γ ⊢⋆ As}
    → t₁ ∼ t₂
    → ts₁ ∼⋆ ts₂
    → t₁ ∷ ts₁ ∼⋆ t₂ ∷ ts₂

∼⋆-refl : ∀ {Γ As} {ts : Γ ⊢⋆ As}
  → ts ∼⋆ ts
∼⋆-refl {ts = []}     = []
∼⋆-refl {ts = t ∷ ts} = ∼‿refl ∷ ∼⋆-refl

∼⋆-sym : ∀ {Γ As} {ts₁ ts₂ : Γ ⊢⋆ As}
  → ts₁ ∼⋆ ts₂
  → ts₂ ∼⋆ ts₁
∼⋆-sym []       = []
∼⋆-sym (p ∷ ps) = ∼‿sym p ∷ ∼⋆-sym ps

∼⋆-trans : ∀ {Γ As} {ts₁ ts₂ ts₃ : Γ ⊢⋆ As}
  → ts₁ ∼⋆ ts₂
  → ts₂ ∼⋆ ts₃
  → ts₁ ∼⋆ ts₃
∼⋆-trans []       []       = []
∼⋆-trans (p ∷ ps) (q ∷ qs) = ∼‿trans p q ∷ ∼⋆-trans ps qs

instance
  ∼⋆-equiv : ∀ {Γ As} → IsEquivalence (_∼⋆_ {Γ} {As})
  ∼⋆-equiv = record
    { refl  = ∼⋆-refl
    ; sym   = ∼⋆-sym
    ; trans = ∼⋆-trans
    }
