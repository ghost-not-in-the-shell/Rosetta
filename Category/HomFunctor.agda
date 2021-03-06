{-# OPTIONS --type-in-type #-}
open import Rosetta.Category.Core
module Rosetta.Category.HomFunctor (𝓒 : Category) where
open import Rosetta.Prelude
open import Rosetta.Category.Categories; open 𝓒𝓪𝓽
open import Rosetta.Category.DiagramChasing 𝓒
open import Rosetta.Category.Functors
open import Rosetta.Category.Setoids
open CategoryReasoning 𝓒

𝓱𝓸𝓶₍_,_₎ : ∀ {A A′}
  → 𝓒 ᵒᵖ ∣       A   ⟶       A′
  → ∀ B
  → 𝓢𝓮𝓽  ∣ 𝒉𝒐𝒎 𝓒 A B ⟶ 𝒉𝒐𝒎 𝓒 A′ B
𝓱𝓸𝓶₍ f , B ₎ = record
  { _$_    =  _∘        f
  ; _cong_ = _⟩∘⟨ refl₍ f ₎
  }

𝓱𝓸𝓶₍-,_₎ : ∀ B → 𝓒 ᵒᵖ ⟶ 𝓢𝓮𝓽
𝓱𝓸𝓶₍-, B ₎ = record
  { _₀_      = λ - → 𝒉𝒐𝒎 𝓒 - B
  ; _₁_      = 𝓱𝓸𝓶₍_, B ₎
  ; _₁-cong_ = λ f₁∼f₂ g₁∼g₂ → g₁∼g₂ ⟩∘⟨ f₁∼f₂
  ; _resp-∘₀ = λ {A}
                 {g₁ g₂ : 𝓒 ∣ A ⟶ B}
                 g₁∼g₂ → begin
    g₁ ∘ id  ↓⟨ ∘-unitʳ 𝓒 ⟩
    g₁       ↓⟨ g₁∼g₂ ⟩
    g₂       ∎
  ; _resp-∘₂ = λ {A A′ A″}
                 {f     : 𝓒 ᵒᵖ ∣ A  ⟶ A′}
                 {f′    : 𝓒 ᵒᵖ ∣ A′ ⟶ A″}
                 {g₁ g₂ : 𝓒    ∣ A  ⟶ B }
                 g₁∼g₂ → begin
    g₁ ∘ (f′ ∘̅ f)  ↓⟨ g₁∼g₂ ⟩∘⟨ refl ⟩
    g₂ ∘ (f ∘ f′)  ↑⟨ ∘-assoc 𝓒 ⟩
    (g₂ ∘ f) ∘ f′  ∎
  }

𝓱₍_₎₀ = 𝓱𝓸𝓶₍-,_₎

𝓱𝓸𝓶⁽_,_⁾ : ∀ A {B B′}
  → 𝓒   ∣         B ⟶         B′
  → 𝓢𝓮𝓽 ∣ 𝒉𝒐𝒎 𝓒 A B ⟶ 𝒉𝒐𝒎 𝓒 A B′
𝓱𝓸𝓶⁽ A , h ⁾ = record
  { _$_    =       h    ∘_
  ; _cong_ = refl₍ h ₎ ⟩∘⟨_
  }

𝓱𝓸𝓶⁽_,-⁾ : ∀ A → 𝓒 ⟶ 𝓢𝓮𝓽
𝓱𝓸𝓶⁽ A ,-⁾ = record
  { _₀_      = λ - → 𝒉𝒐𝒎 𝓒 A -
  ; _₁_      = 𝓱𝓸𝓶⁽ A ,_⁾
  ; _₁-cong_ = λ h₁∼h₂ g₁∼g₂ → h₁∼h₂ ⟩∘⟨ g₁∼g₂
  ; _resp-∘₀ = λ {B}
                 {g₁ g₂ : 𝓒 ∣ A ⟶ B}
                 g₁∼g₂ → begin
    id ∘ g₁  ↓⟨ ∘-unitˡ 𝓒 ⟩
    g₁       ↓⟨ g₁∼g₂ ⟩
    g₂       ∎
  ; _resp-∘₂ = λ {B B′ B″}
                 {h     : 𝓒 ∣ B  ⟶ B′}
                 {h′    : 𝓒 ∣ B′ ⟶ B″}
                 {g₁ g₂ : 𝓒 ∣ A  ⟶ B }
                 g₁∼g₂ → begin
    (h′ ∘ h) ∘ g₁  ↓⟨ refl ⟩∘⟨ g₁∼g₂ ⟩
    (h′ ∘ h) ∘ g₂  ↓⟨ ∘-assoc 𝓒 ⟩
    h′ ∘ (h ∘ g₂)  ∎
  }

𝓱⁽_⁾⁰ = 𝓱𝓸𝓶⁽_,-⁾

𝓱𝓸𝓶₍-,-₎ : 𝓒 ᵒᵖ × 𝓒 ⟶ 𝓢𝓮𝓽
𝓱𝓸𝓶₍-,-₎ = record
  { _₀_      = λ { (A , B) → 𝒉𝒐𝒎 𝓒 A B }
  ; _₁_      = λ { {A , B} {A′ , B′} (f , h) → record
    { _$_    = λ g     →       h    ∘  g      ∘        f
    ; _cong_ = λ g₁∼g₂ → refl₍ h ₎ ⟩∘⟨ g₁∼g₂ ⟩∘⟨ refl₍ f ₎
    } }
  ; _₁-cong_ = λ { (f₁∼f₂ , h₁∼h₂) g₁∼g₂ → h₁∼h₂ ⟩∘⟨ g₁∼g₂ ⟩∘⟨ f₁∼f₂ }
  ; _resp-∘₀ = λ { {A , B} {g₁} {g₂} g₁∼g₂ → begin
    id ∘ g₁ ∘ id  ↓⟨ ∘-unitˡ 𝓒 ⟩
    g₁ ∘ id       ↓⟨ ∘-unitʳ 𝓒 ⟩
    g₁            ↓⟨ g₁∼g₂ ⟩
    g₂            ∎ }
  ; _resp-∘₂ = λ { {A , B} {A′ , B′} {A″ , B″}
                   {f  , h } -- f     : 𝓒 ᵒᵖ ∣ A  ⟶ A′
                             -- h     : 𝓒    ∣ B  ⟶ B′
                   {f′ , h′} -- f′    : 𝓒 ᵒᵖ ∣ A′ ⟶ A″
                             -- h′    : 𝓒    ∣ B′ ⟶ B″
                   {g₁} {g₂} -- g₁ g₂ : 𝓒    ∣ A  ⟶ B
                   g₁∼g₂ → begin
    (h′ ∘ h) ∘ g₁ ∘ (f′ ∘̅ f)  ↓⟨ refl ⟩∘⟨ g₁∼g₂ ⟩∘⟨ refl ⟩
    (h′ ∘ h) ∘ g₂ ∘ (f ∘ f′)  ↓⟨ ∘-assoc 𝓒 ⟩
    h′ ∘ h ∘ g₂ ∘ f ∘ f′      ↑⟨ refl ⟩∘⟨ ∘-assoc 𝓒 ⟩
    h′ ∘ (h ∘ g₂) ∘ f ∘ f′    ↑⟨ refl ⟩∘⟨ ∘-assoc 𝓒 ⟩
    h′ ∘ ((h ∘ g₂) ∘ f) ∘ f′  ↓⟨ refl ⟩∘⟨ ∘-assoc 𝓒 ⟩∘⟨ refl ⟩
    h′ ∘ (h ∘ g₂ ∘ f) ∘ f′    ∎ }
  }

𝓱₍_₎₁ : ∀ {B B′}
  → 𝓒   ∣    B    ⟶    B′
  → 𝓝𝓪𝓽 ∣ 𝓱₍ B ₎₀ ⟶ 𝓱₍ B′ ₎₀
𝓱₍_₎₁ {B} {B′} h = record
  { _at_    = λ A → 𝓱𝓸𝓶⁽ A , h ⁾
  ; natural = λ {A A′}
                {f     : 𝓒 ᵒᵖ ∣ A ⟶ A′}
                {g₁ g₂ : 𝓒    ∣ A ⟶ B }
                g₁∼g₂ → begin
    h ∘ (g₁ ∘ f)  ↓⟨ refl ⟩∘⟨ g₁∼g₂ ⟩∘⟨ refl ⟩
    h ∘ (g₂ ∘ f)  ↑⟨ ∘-assoc 𝓒 ⟩
    (h ∘ g₂) ∘ f  ∎
  }

𝓱⁽_⁾¹ : ∀ {A A′}
  → 𝓒 ᵒᵖ ∣    A    ⟶    A′
  → 𝓝𝓪𝓽  ∣ 𝓱⁽ A ⁾⁰ ⟶ 𝓱⁽ A′ ⁾⁰
𝓱⁽_⁾¹ {A} {A′} f = record
  { _at_    = λ B → 𝓱𝓸𝓶₍ f , B ₎
  ; natural = λ {B B′}
                {h     : 𝓒 ∣ B ⟶ B′}
                {g₁ g₂ : 𝓒 ∣ A ⟶ B }
                g₁∼g₂ → begin
    (h ∘ g₁) ∘ f  ↓⟨ (refl ⟩∘⟨ g₁∼g₂) ⟩∘⟨ refl ⟩
    (h ∘ g₂) ∘ f  ↓⟨ ∘-assoc 𝓒 ⟩
    h ∘ (g₂ ∘ f)  ∎
  }

𝓱₋ : 𝓒 ⟶ [ 𝓒 ᵒᵖ , 𝓢𝓮𝓽 ]
𝓱₋ = record
  { _₀_      = 𝓱₍_₎₀
  ; _₁_      = 𝓱₍_₎₁
  ; _₁-cong_ = λ h₁∼h₂ g₁∼g₂ → h₁∼h₂ ⟩∘⟨ g₁∼g₂
  ; _resp-∘₀ = λ {B A}
                 {g₁ g₂ : 𝓒 ∣ A ⟶ B}
                 g₁∼g₂ → begin
    id ∘ g₁  ↓⟨ ∘-unitˡ 𝓒 ⟩
    g₁       ↓⟨ g₁∼g₂ ⟩
    g₂       ∎
  ; _resp-∘₂ = λ {B B′ B″}
                 {h     : 𝓒 ∣ B  ⟶ B′}
                 {h′    : 𝓒 ∣ B′ ⟶ B″}
                 {A}
                 {g₁ g₂ : 𝓒 ∣ A  ⟶ B }
                 g₁∼g₂ → begin
    (h′ ∘ h) ∘ g₁  ↓⟨ refl ⟩∘⟨ g₁∼g₂ ⟩
    (h′ ∘ h) ∘ g₂  ↓⟨ ∘-assoc 𝓒 ⟩
    h′ ∘ (h ∘ g₂)  ∎
  }

𝓱⁻ : 𝓒 ᵒᵖ ⟶ [ 𝓒 , 𝓢𝓮𝓽 ]
𝓱⁻ = record
  { _₀_      = 𝓱⁽_⁾⁰
  ; _₁_      = 𝓱⁽_⁾¹
  ; _₁-cong_ = λ f₁∼f₂ g₁∼g₂ → g₁∼g₂ ⟩∘⟨ f₁∼f₂
  ; _resp-∘₀ = λ {A B}
                 {g₁ g₂ : 𝓒 ∣ A ⟶ B}
                 g₁∼g₂ → begin
    g₁ ∘ id  ↓⟨ ∘-unitʳ 𝓒 ⟩
    g₁       ↓⟨ g₁∼g₂ ⟩
    g₂       ∎
  ; _resp-∘₂ = λ {A A′ A″}
                 {f     : 𝓒 ᵒᵖ ∣ A  ⟶ A′}
                 {f′    : 𝓒 ᵒᵖ ∣ A′ ⟶ A″}
                 {B}
                 {g₁ g₂ : 𝓒    ∣ A  ⟶ B }
                 g₁∼g₂ → begin
    g₁ ∘ (f′ ∘̅ f)  ↓⟨ g₁∼g₂ ⟩∘⟨ refl ⟩
    g₂ ∘ (f ∘ f′)  ↑⟨ ∘-assoc 𝓒 ⟩
    (g₂ ∘ f) ∘ f′  ∎
  }

_₍-,_₎ = 𝓱𝓸𝓶₍-,_₎
_⁽_,-⁾ = 𝓱𝓸𝓶⁽_,-⁾

𝓨 = 𝓱₋
