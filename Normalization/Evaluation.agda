{-# OPTIONS --type-in-type #-}
module Rosetta.Normalization.Evaluation where
open import Rosetta.Prelude
open import Rosetta.Category.CartesianClosed
open import Rosetta.Category.Categories
open import Rosetta.Category.Core
open import Rosetta.Category.HomFunctor
open import Rosetta.Category.Functors
open import Rosetta.Category.Presheaves
open import Rosetta.Category.Setoids
open import Rosetta.Normalization.Free
open import Rosetta.Normalization.Substitution
open import Rosetta.Normalization.Syntax
open import Rosetta.Normalization.Weakening
open 𝓟𝓢𝓱 𝓦

𝓨𝔀 : 𝓣𝓶 ⟶ 𝓟𝓢𝓱 𝓦
𝓨𝔀 = 𝓢𝓮𝓽 ^₁ (⌜-⌝ ᵒᵖ→) ∘ 𝓨 𝓣𝓶

⟦_⟧ : Ty → PSh 𝓦
⟦ 𝒐     ⟧ = 𝓨𝔀 ₀ (𝒐 ∷ [])
⟦ A ⇒ B ⟧ = ⟦ B ⟧ ^ ⟦ A ⟧

⟦_⟧⋆₀ : Con → PSh 𝓦
⟦ [] ⟧⋆₀    = 𝟙
⟦ A ∷ Γ ⟧⋆₀ = ⟦ Γ ⟧⋆₀ × ⟦ A ⟧

π₍_₎ : ∀ {Γ A} → A ∈ Γ → 𝓟𝓢𝓱 𝓦 ∣ ⟦ Γ ⟧⋆₀ ⟶ ⟦ A ⟧
π₍_₎ {(.A ∷ Γ)} {A} ze = π₂ᴾ {⟦ Γ ⟧⋆₀} {⟦ A ⟧}
π₍_₎ {(B ∷ Γ)} {A} (su x) = π₍ x ₎ ∘ π₁ᴾ {⟦ Γ ⟧⋆₀} {⟦ B ⟧}

⟦_⟧₁ : ∀ {Γ A} → Γ ⊢ A → 𝓟𝓢𝓱 𝓦 ∣ ⟦ Γ ⟧⋆₀ ⟶ ⟦ A ⟧
⟦ var x ⟧₁ = π₍ x ₎
⟦ lam t ⟧₁ = ƛᴾ ⟦ t ⟧₁
⟦ app t u ⟧₁ = εᴾ ∘ ⟨ ⟦ t ⟧₁ , ⟦ u ⟧₁ ⟩ᴾ

⟦_⟧⋆₁ : ∀ {Γ Δ} → Γ ⊢⋆ Δ → 𝓟𝓢𝓱 𝓦 ∣ ⟦ Γ ⟧⋆₀ ⟶ ⟦ Δ ⟧⋆₀
⟦ [] ⟧⋆₁ = !ᴾ
⟦_⟧⋆₁ {Γ} {A ∷ Δ} (t ∷ ts) = ⟨ ⟦ ts ⟧⋆₁ , ⟦ t ⟧₁ ⟩ᴾ

⟦-⟧ : 𝓣𝓶 ⟶ 𝓟𝓢𝓱 𝓦
⟦-⟧ = record
  { _₀_      = ⟦_⟧⋆₀
  ; _₁_      = ⟦_⟧⋆₁
  ; _₁-cong_ = {!!}
  ; _resp-∘₀ = {!!}
  ; _resp-∘₂ = {!!}
  }

mutual
  𝓺 : ∀ {A Γ} → ∣ ⟦ A ⟧ ₀ Γ ∣ → ∣ (𝓨𝔀 ₀ (A ∷ [])) ₀ Γ ∣
  𝓺 {𝒐}     {Γ} t = t
  𝓺 {A ⇒ B} {Γ} f = lam (fst (𝓺 {B} {A ∷ Γ} ((f at (A ∷ Γ)) $ (skip id , 𝓾 {A} {A ∷ Γ} (var ze ∷ []))))) ∷ []

  𝓾 : ∀ {A Γ} → ∣ (𝓨𝔀 ₀ (A ∷ [])) ₀ Γ ∣ → ∣ ⟦ A ⟧ ₀ Γ ∣
  𝓾 {𝒐}     {Γ} t = t
  𝓾 {A ⇒ B} {Γ} f = record
    { _at_    = λ Δ → record
      { _$_    = λ { (w , x) → 𝓾 {B} {Δ} (app (fst (((𝓨𝔀 ₁ f) at Δ) $ ⌜ w ⌝)) (fst (𝓺 {A} {Δ} x)) ∷ []) }
      ; _cong_ = {!!}
      }
    ; natural = {!!}
    }

q : 𝓝𝓪𝓽 ∣ ⟦-⟧ ⟶ 𝓨𝔀
q = record
  { _at_    = λ Δ → record
    { _at_    = λ Γ → record
      { _$_    = λ x → {!!}
      ; _cong_ = {!!}
      }
    ; natural = {!!}
    }
  ; natural = {!!}
  }

u : 𝓝𝓪𝓽 ∣ 𝓨𝔀 ⟶ ⟦-⟧
u = record
  { _at_    = λ Δ → record
    { _at_    = λ Γ → record
      { _$_    = λ M → {!!}
      ; _cong_ = {!!}
      }
    ; natural = {!!}
    }
  ; natural = {!!}
  }

nf : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A
nf {Γ} {A} t = fst (𝓺 ((⟦ t ⟧₁ at Γ) $ (𝓾 id)))

ex1 : (𝒐 ⇒ 𝒐) ∷ [] ⊢ 𝒐 ⇒ 𝒐
ex1 = nf (var ze)

ex2 : (𝒐 ⇒ 𝒐) ∷ 𝒐 ∷ [] ⊢ 𝒐 ⇒ 𝒐
ex2 = nf (app (lam (var ze))
              (lam (var ze)))
