{-# OPTIONS --type-in-type         #-}
{-# OPTIONS --allow-unsolved-metas #-}
module Rosetta.Normalization.Substitution where
open import Rosetta.Prelude
open import Rosetta.Category.Core
open import Rosetta.Normalization.Syntax
open import Rosetta.Normalization.Weakening

infix 4 _⊢⋆_
_⊢⋆_ : Con → Con → Set
Γ ⊢⋆ As = All (Γ ⊢_) As

infixr 5 _◑_
_◑_ : ∀ {Γ Δ Σ} → Δ ⊢⋆ Σ → Γ ≽ Δ → Γ ⊢⋆ Σ
[]       ◑ w = []
(t ∷ ts) ◑ w = rename⊢ w t ∷ (ts ◑ w)

infixr 5 _◐_
_◐_ : ∀ {Γ Δ Σ} → Δ ≽ Σ → Γ ⊢⋆ Δ → Γ ⊢⋆ Σ
done   ◐ []       = []
skip w ◐ (t ∷ ts) =      w ◐ ts
keep w ◐ (t ∷ ts) = t ∷ (w ◐ ts)

⌜skip⌝ : ∀ {Γ Δ A} → Γ ⊢⋆ Δ → A ∷ Γ ⊢⋆     Δ
⌜keep⌝ : ∀ {Γ Δ A} → Γ ⊢⋆ Δ → A ∷ Γ ⊢⋆ A ∷ Δ
⌜skip⌝ ts = ts ◑ skip id
⌜keep⌝ ts = var ze ∷ ⌜skip⌝ ts

⌜_⌝ : ∀ {Γ Δ} → Γ ≽ Δ → Γ ⊢⋆ Δ
⌜ done   ⌝ = []
⌜ skip w ⌝ = ⌜skip⌝ ⌜ w ⌝
⌜ keep w ⌝ = ⌜keep⌝ ⌜ w ⌝

subst∈ : ∀ {A Γ Δ} → Γ ⊢⋆ Δ → A ∈ Δ → Γ ⊢ A
subst∈ ρ x = lookup ρ x

subst⊢ : ∀ {A Γ Δ} → Γ ⊢⋆ Δ → Δ ⊢ A → Γ ⊢ A
subst⊢ ρ (var x)   = subst∈ ρ x
subst⊢ ρ (lam t)   = lam (subst⊢ (⌜keep⌝ ρ) t)
subst⊢ ρ (app t u) = app (subst⊢ ρ t) (subst⊢ ρ u)

_[_] : ∀ {Γ Δ As} → Δ ⊢⋆ As → Γ ⊢⋆ Δ → Γ ⊢⋆ As
ts [ ρ ] = map (subst⊢ ρ) ts
