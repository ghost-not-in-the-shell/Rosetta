{-# OPTIONS --type-in-type #-}
module Rosetta.Normalization.Weakening where
open import Rosetta.Prelude
open import Rosetta.Category.Core hiding (id; _∘_; ∘-unitˡ; ∘-unitʳ; ∘-assoc)
open import Rosetta.Category.Setoids
open import Rosetta.Normalization.Syntax

infix 4 _≽_
data _≽_ : Con → Con → Set where
  done : [] ≽ []
  skip : ∀ {Γ Δ A} → Γ ≽ Δ → A ∷ Γ ≽     Δ
  keep : ∀ {Γ Δ A} → Γ ≽ Δ → A ∷ Γ ≽ A ∷ Δ

private
  id : ∀ {Γ} → Γ ≽ Γ
  id {[]}    = done
  id {A ∷ Γ} = keep id

infixr 5 _∙_
_∙_ : ∀ {Γ Δ Σ} → Δ ≽ Σ → Γ ≽ Δ → Γ ≽ Σ
w      ∙ done    = w
w      ∙ skip w′ = skip (w ∙ w′)
skip w ∙ keep w′ = skip (w ∙ w′)
keep w ∙ keep w′ = keep (w ∙ w′)

instance
  𝓦∣op : Op _≽_
  𝓦∣op = record
    { id  = id
    ; _∘_ = _∙_
    }

.∙-unitˡ : ∀ {Γ Δ} (w : Γ ≽ Δ) → id ∙ w ≡ w
∙-unitˡ done     = ≡-refl
∙-unitˡ (skip w) = skip <$> ∙-unitˡ w
∙-unitˡ (keep w) = keep <$> ∙-unitˡ w

.∙-unitʳ : ∀ {Γ Δ} (w : Γ ≽ Δ) → w ∙ id ≡ w
∙-unitʳ done     = ≡-refl
∙-unitʳ (skip w) = skip <$> ∙-unitʳ w
∙-unitʳ (keep w) = keep <$> ∙-unitʳ w

.∙-assoc : ∀ {Γ Δ Σ Ξ} (w″ : Γ ≽ Δ) (w′ : Δ ≽ Σ) (w : Σ ≽ Ξ)
  → (w ∙ w′) ∙ w″ ≡ w ∙ (w′ ∙ w″)
∙-assoc done      w′        w        = ≡-refl
∙-assoc (skip w″) w′        w        = skip <$> ∙-assoc w″ w′ w
∙-assoc (keep w″) (skip w′) w        = skip <$> ∙-assoc w″ w′ w
∙-assoc (keep w″) (keep w′) (skip w) = skip <$> ∙-assoc w″ w′ w
∙-assoc (keep w″) (keep w′) (keep w) = keep <$> ∙-assoc w″ w′ w

𝓦 : Category
𝓦 = record
  { ob    = Con
  ; hom   = _≽_
  ; _∣_∼_ = _≡_
  ; ∘-cong₂ = λ w₁≡w₂ w′₁≡w′₂ → ≡-cong₂ _∙_ w₁≡w₂ w′₁≡w′₂
  ; ∘-unitˡ = ∙-unitˡ _
  ; ∘-unitʳ = ∙-unitʳ _
  ; ∘-assoc = λ { {f = w″} {w′} {w} → ∙-assoc w″ w′ w }
  }

rename∈ : ∀ {A Γ Δ} → Γ ≽ Δ → A ∈ Δ → A ∈ Γ
rename∈ done ()
rename∈ (skip w) x      = su (rename∈ w x)
rename∈ (keep w) ze     = ze
rename∈ (keep w) (su x) = su (rename∈ w x)

rename∈-resp-∙₀ : ∀ {A Γ} (x : A ∈ Γ) → rename∈ id x ≡ x
rename∈-resp-∙₀ ze     = ≡-refl
rename∈-resp-∙₀ (su x) = su <$> rename∈-resp-∙₀ x

rename∈-resp-∙₂ : ∀ {A Γ Δ Σ} (w′ : Γ ≽ Δ) (w : Δ ≽ Σ) (x : A ∈ Σ) → rename∈ (w ∙ w′) x ≡ rename∈ w′ (rename∈ w x)
rename∈-resp-∙₂ done done ()
rename∈-resp-∙₂ (skip w′) w        x      = su <$> rename∈-resp-∙₂ w′ w x
rename∈-resp-∙₂ (keep w′) (skip w) x      = su <$> rename∈-resp-∙₂ w′ w x
rename∈-resp-∙₂ (keep w′) (keep w) ze     = ≡-refl
rename∈-resp-∙₂ (keep w′) (keep w) (su x) = su <$> rename∈-resp-∙₂ w′ w x

𝓦₍-,_₎ : ∀ A → 𝓦 ᵒᵖ ⟶ 𝓢𝓮𝓽
𝓦₍-, A ₎ = record
  { _₀_      = λ Γ → setoid (A ∈ Γ)
  ; _₁_      = λ w → record
    { _$_    = rename∈ w
    ; _cong_ = ≡-cong (rename∈ w)
    }
  ; _₁-cong_ = λ w₁≡w₂ x₁≡x₂ → ≡-cong₂ rename∈ w₁≡w₂ x₁≡x₂
  ; _resp-∘₀ = λ { ≡-refl → rename∈-resp-∙₀ _ }
  ; _resp-∘₂ = λ { {f = w} {w′} ≡-refl → rename∈-resp-∙₂ w′ w _ }
  }

rename⊢ : ∀ {A Γ Δ} → Γ ≽ Δ → Δ ⊢ A → Γ ⊢ A
rename⊢ w (var x)   = var (rename∈ w x)
rename⊢ w (lam t)   = lam (rename⊢ (keep w) t)
rename⊢ w (app t u) = app (rename⊢ w t) (rename⊢ w u)
