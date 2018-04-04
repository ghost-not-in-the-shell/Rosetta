{-# OPTIONS --type-in-type #-}
module Rosetta.Setoids where
open import Rosetta.Equivalence
open import Rosetta.Equality
open import Rosetta.Category        as Category
open import Rosetta.CartesianClosed as CartesianClosed
open import Rosetta.Sets            as 𝓢et hiding (𝟙; _×_; _⇒_)

record Setoid : Set where
  infix 4 _∣_∼_
  field
    ∣_∣ : Set
    _∣_∼_ : Rel ∣_∣
    ⦃ .∼‿equiv ⦄ : IsEquivalence _∣_∼_

open Setoid public hiding (∼‿equiv)

infix 0 _-𝓢𝓮𝓽⟶_
record _-𝓢𝓮𝓽⟶_ (𝑨 𝑩 : Setoid) : Set where
  field
    _₀_  : ∣ 𝑨 ∣ → ∣ 𝑩 ∣
    ._₁_ : ∀ {x y} → 𝑨 ∣ x ∼ y → 𝑩 ∣ _₀_ x ∼ _₀_ y

open _-𝓢𝓮𝓽⟶_ public

instance
  𝓢𝓮𝓽-op : Category.Op _-𝓢𝓮𝓽⟶_
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

infix 4 _∼_
_∼_ : ∀ {𝑨 𝑩 : Setoid} → Rel (𝑨 -𝓢𝓮𝓽⟶ 𝑩)
_∼_ {𝑨} {𝑩} 𝒇 𝒈 = ∀ {x y} → 𝑨 ∣ x ∼ y → 𝑩 ∣ 𝒇 ₀ x ∼ 𝒈 ₀ y

.∼‿refl₍_₎ : ∀ {𝑨 𝑩} (𝒇 : 𝑨 -𝓢𝓮𝓽⟶ 𝑩) → 𝒇 ∼ 𝒇
.∼‿sym     : ∀ {𝑨 𝑩} {𝒇 𝒈 : 𝑨 -𝓢𝓮𝓽⟶ 𝑩} → 𝒇 ∼ 𝒈 → 𝒈 ∼ 𝒇
.∼‿trans   : ∀ {𝑨 𝑩} {𝒇 𝒈 𝒉 : 𝑨 -𝓢𝓮𝓽⟶ 𝑩} → 𝒇 ∼ 𝒈 → 𝒈 ∼ 𝒉 → 𝒇 ∼ 𝒉
∼‿refl₍ 𝒇 ₎     = λ x∼y → 𝒇 ₁ x∼y
∼‿sym   𝒇∼𝒈     = λ x∼y → sym (𝒇∼𝒈 (sym x∼y))
∼‿trans 𝒇∼𝒈 𝒈∼𝒉 = λ x∼y → trans (𝒇∼𝒈 x∼y) (𝒈∼𝒉 refl)

.∼‿inj₍_₎ : ∀ {𝑨 𝑩} (𝒇 {𝒈} : 𝑨 -𝓢𝓮𝓽⟶ 𝑩) → 𝒇 ≡ 𝒈 → 𝒇 ∼ 𝒈
∼‿inj₍ 𝒇 ₎ ≡-refl = ∼‿refl₍ 𝒇 ₎

instance
  ∼‿equiv : ∀ {𝑨 𝑩 : Setoid} → IsEquivalence (_∼_ {𝑨} {𝑩})
  ∼‿equiv = record
    { refl₍_₎ = ∼‿refl₍_₎
    ; sym     = λ {𝒇} {𝒈} → ∼‿sym {𝒇 = 𝒇} {𝒈}
    ; trans   = λ {𝒇} {𝒈} {𝒉} → ∼‿trans {𝒇 = 𝒇} {𝒈} {𝒉}
    }

𝓢𝓮𝓽 : Category
𝓢𝓮𝓽 = record
  { ob    = Setoid
  ; hom   = _-𝓢𝓮𝓽⟶_
  ; _∣_∼_ = _∼_
  ; ∘-cong₂ = λ 𝒈₁∼𝒈₂ 𝒇₁∼𝒇₂ x∼y → 𝒈₁∼𝒈₂ (𝒇₁∼𝒇₂ x∼y)
  ; ∘-unitˡ = λ { {f = 𝒇} → ∼‿refl₍ 𝒇 ₎ }
  ; ∘-unitʳ = λ { {f = 𝒇} → ∼‿refl₍ 𝒇 ₎ }
  ; ∘-assoc = λ { {f = 𝒇} {𝒈} {𝒉} → ∼‿refl₍ 𝒉 ∘ 𝒈 ∘ 𝒇 ₎ }
  }

𝟙 : Setoid
𝟙 = record
  { ∣_∣   = 𝓢et.𝟙
  ; _∣_∼_ = λ _ _ → 𝓢et.𝟙
  ; ∼‿equiv = record
    { refl₍_₎ = λ _   → tt
    ; sym     = λ _   → tt
    ; trans   = λ _ _ → tt
    }
  }

infixr 6 _×_
_×_ : Setoid → Setoid → Setoid
𝑨 × 𝑩 = record
  { ∣_∣   = ∣ 𝑨 ∣ 𝓢et.× ∣ 𝑩 ∣
  ; _∣_∼_ = λ { (x₁ , x₂) (y₁ , y₂) → (𝑨 ∣ x₁ ∼ y₁) 𝓢et.× (𝑩 ∣ x₂ ∼ y₂) }
  ; ∼‿equiv = record
    { refl₍_₎ = λ { (x₁ , x₂) → refl₍ x₁ ₎ , refl₍ x₂ ₎ }
    ; sym     = λ { (x₁∼y₁ , x₂∼y₂) → sym x₁∼y₁ , sym x₂∼y₂ }
    ; trans   = λ { (x₁∼y₁ , x₂∼y₂) (y₁∼z₁ , y₂∼z₂) → trans x₁∼y₁ y₁∼z₁ , trans x₂∼y₂ y₂∼z₂ }
    }
  }

infixr 7 _⇒_
_⇒_ : Setoid → Setoid → Setoid
𝑨 ⇒ 𝑩 = record
  { ∣_∣   = 𝑨 -𝓢𝓮𝓽⟶ 𝑩
  ; _∣_∼_ = _∼_
  }

instance
  𝓢𝓮𝓽✓-op : CartesianClosed.Op _-𝓢𝓮𝓽⟶_
  𝓢𝓮𝓽✓-op = record
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
    ; ev    = record
      { _₀_ = λ { (𝒇   , x)   → 𝒇 ₀ x }
      ; _₁_ = λ { (𝒇∼𝒈 , x∼y) → 𝒇∼𝒈 x∼y }
      }
    ; λ₍_₎  = λ 𝒇 → record
      { _₀_ = λ x → record
        { _₀_ = λ y     → 𝒇 ₀ (x    , y)
        ; _₁_ = λ y₁∼y₂ → 𝒇 ₁ (refl , y₁∼y₂)
        }
      ; _₁_ = λ x₁∼x₂ y₁∼y₂ → 𝒇 ₁ (x₁∼x₂ , y₁∼y₂)
      }
    }

𝓢𝓮𝓽✓ : CartesianClosed 𝓢𝓮𝓽
𝓢𝓮𝓽✓ = record
  { !-universal   = λ { {⁇ = ⁇} → ∼‿refl₍ ⁇ ₎ }
  ; ⟨,⟩-cong₂     = λ 𝒇₁∼𝒇₂ 𝒈₁∼𝒈₂ x∼y → 𝒇₁∼𝒇₂ x∼y , 𝒈₁∼𝒈₂ x∼y
  ; ⟨,⟩-commute₁  = λ { {f = 𝒇} → ∼‿refl₍ 𝒇 ₎ }
  ; ⟨,⟩-commute₂  = λ { {g = 𝒈} → ∼‿refl₍ 𝒈 ₎ }
  ; ⟨,⟩-universal = λ ⁇-commute₁ ⁇-commute₂ x∼y → ⁇-commute₁ x∼y , ⁇-commute₂ x∼y
  ; λ-cong        = λ 𝒇₁∼𝒇₂ x₁∼x₂ y₁∼y₂ → 𝒇₁∼𝒇₂ (x₁∼x₂ , y₁∼y₂)
  ; λ-commute     = λ { {f = 𝒇} → ∼‿refl₍ 𝒇 ₎ }
  ; λ-universal   = λ ⁇-commute x₁∼x₂ y₁∼y₂ → ⁇-commute (x₁∼x₂ , y₁∼y₂)
  }
