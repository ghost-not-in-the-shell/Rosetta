{-# OPTIONS --type-in-type #-}
module Rosetta.Setoids where
open import Rosetta.CartesianClosed
open import Rosetta.Category
open import Rosetta.Equivalence
open import Rosetta.Prelude
open import Rosetta.Sets

record 𝓢𝓮𝓽∣_⟶_ (𝑨 𝑩 : Setoid) : Set where
  infixr 6 _₀_
  infixr 6 _₁_
  field
    _₀_ : ∣ 𝑨 ∣ → ∣ 𝑩 ∣
    ._₁_ : ∀ {x y} → 𝑨 ∣ x ∼ y → 𝑩 ∣ _₀_ x ∼ _₀_ y

open 𝓢𝓮𝓽∣_⟶_ public

instance
  𝓢𝓮𝓽-op : Op 𝓢𝓮𝓽∣_⟶_
  𝓢𝓮𝓽-op = record
    { id  = record
      { _₀_ = id
      ; _₁_ = id
      }
    ; _∘_ = λ 𝒈 𝒇 → record
      { _₀_ = 𝒈 ₀_ ∘ 𝒇 ₀_
      ; _₁_ = 𝒈 ₁_ ∘ 𝒇 ₁_
      }
    }

module _ {𝑨 𝑩 : Setoid} where
  infix 4 𝓢𝓮𝓽∣_≈_
  𝓢𝓮𝓽∣_≈_ : Rel (𝓢𝓮𝓽∣ 𝑨 ⟶ 𝑩)
  𝓢𝓮𝓽∣ 𝒇 ≈ 𝒈 = ∀ {x y}
    → 𝑨 ∣ x ∼ y
    → 𝑩 ∣ 𝒇 ₀ x ∼ 𝒈 ₀ y

  .𝓢𝓮𝓽≈-refl  : ∀ {𝒇 : 𝓢𝓮𝓽∣ 𝑨 ⟶ 𝑩} → 𝓢𝓮𝓽∣ 𝒇 ≈ 𝒇
  .𝓢𝓮𝓽≈-sym   : ∀ {𝒇 𝒈 : 𝓢𝓮𝓽∣ 𝑨 ⟶ 𝑩} → 𝓢𝓮𝓽∣ 𝒇 ≈ 𝒈 → 𝓢𝓮𝓽∣ 𝒈 ≈ 𝒇
  .𝓢𝓮𝓽≈-trans : ∀ {𝒇 𝒈 𝒉 : 𝓢𝓮𝓽∣ 𝑨 ⟶ 𝑩} → 𝓢𝓮𝓽∣ 𝒇 ≈ 𝒈 → 𝓢𝓮𝓽∣ 𝒈 ≈ 𝒉 → 𝓢𝓮𝓽∣ 𝒇 ≈ 𝒉
  𝓢𝓮𝓽≈-refl  {𝒇}     = λ x∼y → 𝒇 ₁ x∼y
  𝓢𝓮𝓽≈-sym   𝒇≈𝒈     = λ x∼y → sym (𝒇≈𝒈 (sym x∼y))
  𝓢𝓮𝓽≈-trans 𝒇≈𝒈 𝒈≈𝒉 = λ x∼y → trans (𝒇≈𝒈 x∼y) (𝒈≈𝒉 refl)

  instance
    𝓢𝓮𝓽≈-equiv : IsEquivalence 𝓢𝓮𝓽∣_≈_
    𝓢𝓮𝓽≈-equiv = record
      { refl   = λ {𝒇}     → 𝓢𝓮𝓽≈-refl  {𝒇}
      ; sym    = λ {𝒇 𝒈}   → 𝓢𝓮𝓽≈-sym   {𝒇} {𝒈}
      ; trans  = λ {𝒇 𝒈 𝒉} → 𝓢𝓮𝓽≈-trans {𝒇} {𝒈} {𝒉}
      }

  .𝓢𝓮𝓽≈-refl₍_₎ : ∀ (𝒇 : 𝓢𝓮𝓽∣ 𝑨 ⟶ 𝑩) → 𝓢𝓮𝓽∣ 𝒇 ≈ 𝒇
  𝓢𝓮𝓽≈-refl₍ 𝒇 ₎ = 𝓢𝓮𝓽≈-refl {𝒇}

𝓢𝓮𝓽 : Category
𝓢𝓮𝓽 = record
  { ob  = Setoid
  ; hom = 𝓢𝓮𝓽∣_⟶_
  ; _≈_ = 𝓢𝓮𝓽∣_≈_
  ; ∘-cong₂ = λ 𝒈₁≈𝒈₂ 𝒇₁≈𝒇₂ x∼y → 𝒈₁≈𝒈₂ (𝒇₁≈𝒇₂ x∼y)
  ; ∘-unitˡ = λ { {f = 𝒇} → 𝓢𝓮𝓽≈-refl₍ 𝒇 ₎ }
  ; ∘-unitʳ = λ { {f = 𝒇} → 𝓢𝓮𝓽≈-refl₍ 𝒇 ₎ }
  ; ∘-assoc = λ { {f = 𝒇} {𝒈} {𝒉} → 𝓢𝓮𝓽≈-refl₍ 𝒉 ∘ 𝒈 ∘ 𝒇 ₎ }
  }

{-# DISPLAY 𝓢𝓮𝓽∣_⟶_ 𝑨 𝑩 = 𝓢𝓮𝓽 ∣ 𝑨 ⟶ 𝑩 #-}
{-# DISPLAY 𝓢𝓮𝓽∣_≈_ 𝒇 𝒈 = 𝓢𝓮𝓽 ∣ 𝒇 ≈ 𝒈 #-}

module 𝓢𝓮𝓽 where
  infixr 6 _×_
  infixr 7 _⇒_

  𝟙 : Setoid
  𝟙 = record
    { ∣_∣ = 𝓢et.𝟙
    ; _∼_ = λ _ _ → 𝓢et.𝟙
    ; ∼-equiv = record
      { refl  =         tt
      ; sym   = λ _   → tt
      ; trans = λ _ _ → tt
      }
    }

  _×_ : Setoid → Setoid → Setoid
  𝑨 × 𝑩 = record
    { ∣_∣ = ∣ 𝑨 ∣ 𝓢et.× ∣ 𝑩 ∣
    ; _∼_ = λ { (x₁ , x₂) (y₁ , y₂) → (𝑨 ∣ x₁ ∼ y₁) 𝓢et.× (𝑩 ∣ x₂ ∼ y₂) }
    ; ∼-equiv = record
      { refl  = refl , refl
      ; sym   = λ { (x₁∼y₁ , x₂∼y₂) → sym x₁∼y₁ , sym x₂∼y₂ }
      ; trans = λ { (x₁∼y₁ , x₂∼y₂) (y₁∼z₁ , y₂∼z₂) → trans x₁∼y₁ y₁∼z₁ , trans x₂∼y₂ y₂∼z₂ }
      }
    }

  _⇒_ : Setoid → Setoid → Setoid
  𝑨 ⇒ 𝑩 = record
    { ∣_∣ = 𝓢𝓮𝓽∣ 𝑨 ⟶ 𝑩
    ; _∼_ = 𝓢𝓮𝓽∣_≈_
    }

open 𝓢𝓮𝓽

instance
  𝓢𝓮𝓽-op✓ : Op✓ 𝓢𝓮𝓽∣_⟶_
  𝓢𝓮𝓽-op✓ = record
    { 𝟙   = 𝟙
    ; _×_ = _×_
    ; _⇒_ = _⇒_
    ; !     = record
      { _₀_ = !
      ; _₁_ = !
      }
    ; π₁    = record
      { _₀_ = π₁
      ; _₁_ = π₁
      }
    ; π₂    = record
      { _₀_ = π₂
      ; _₁_ = π₂
      }
    ; ⟨_,_⟩ = λ 𝒇 𝒈 → record
      { _₀_ = ⟨ 𝒇 ₀_ , 𝒈 ₀_ ⟩
      ; _₁_ = ⟨ 𝒇 ₁_ , 𝒈 ₁_ ⟩
      }
    ; ε     = record
      { _₀_ = λ { (𝒇     , x)     → 𝒇 ₀   x }
      ; _₁_ = λ { (𝒇₁≈𝒇₂ , x₁∼x₂) → 𝒇₁≈𝒇₂ x₁∼x₂ }
      }
    ; ƛ_    = λ 𝒇 → record
      { _₀_ = λ x → record
        { _₀_ = λ y     → 𝒇 ₀ (      x   , y)
        ; _₁_ = λ y₁∼y₂ → 𝒇 ₁ (refl₍ x ₎ , y₁∼y₂)
        }
      ; _₁_ = λ x₁∼x₂ y₁∼y₂ → 𝒇 ₁ (x₁∼x₂ , y₁∼y₂)
      }
    }

𝓢𝓮𝓽✓ : CartesianClosed 𝓢𝓮𝓽
𝓢𝓮𝓽✓ = record
  { !-universal   = λ { {⁇ = ⁇} → 𝓢𝓮𝓽≈-refl₍ ⁇ ₎ }
  ; ⟨,⟩-cong₂     = λ 𝒇₁≈𝒇₂ 𝒈₁≈𝒈₂ x∼y → 𝒇₁≈𝒇₂ x∼y , 𝒈₁≈𝒈₂ x∼y
  ; ⟨,⟩-commute₁  = λ { {f = 𝒇} → 𝓢𝓮𝓽≈-refl₍ 𝒇 ₎ }
  ; ⟨,⟩-commute₂  = λ { {g = 𝒈} → 𝓢𝓮𝓽≈-refl₍ 𝒈 ₎ }
  ; ⟨,⟩-universal = λ ⁇-commute₁ ⁇-commute₂ x∼y → ⁇-commute₁ x∼y , ⁇-commute₂ x∼y
  ; ƛ-cong        = λ 𝒇₁≈𝒇₂ x₁∼x₂ y₁∼y₂ → 𝒇₁≈𝒇₂ (x₁∼x₂ , y₁∼y₂)
  ; ƛ-commute     = λ { {f = 𝒇} → 𝓢𝓮𝓽≈-refl₍ 𝒇 ₎ }
  ; ƛ-universal   = λ ⁇-commute x₁∼x₂ y₁∼y₂ → ⁇-commute (x₁∼x₂ , y₁∼y₂)
  }
