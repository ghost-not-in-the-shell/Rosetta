{-# OPTIONS --type-in-type #-}
open import Rosetta.Category
module Rosetta.HomFunctor (𝓒 : Category) where
open import Rosetta.DiagrammaticReasoning 𝓒
open import Rosetta.Equivalence
open import Rosetta.Functor
open import Rosetta.Functors
open import Rosetta.Prelude
open import Rosetta.Setoids

module Covariant (B : ob 𝓒) where
  𝓱𝓸𝓶₍_,B₎₀ : ob (𝓒 ᵒᵖ) → Setoid
  𝓱𝓸𝓶₍ A ,B₎₀ = 𝒉𝒐𝒎 𝓒 A B

  𝓱𝓸𝓶₍_,B₎₁ : ∀ {A A′}
    → 𝓒 ᵒᵖ ∣      A      ⟶      A′
    → 𝓢𝓮𝓽  ∣ 𝓱𝓸𝓶₍ A ,B₎₀ ⟶ 𝓱𝓸𝓶₍ A′ ,B₎₀
  𝓱𝓸𝓶₍ f ,B₎₁ = record
    { _₀_ =  _∘        f
    ; _₁_ = _⟩∘⟨ refl₍ f ₎
    }

  𝓱𝓸𝓶₍-,B₎ : 𝓒 ᵒᵖ ⟶ 𝓢𝓮𝓽
  𝓱𝓸𝓶₍-,B₎ = record
    { _₀_ = 𝓱𝓸𝓶₍_,B₎₀
    ; _₁_ = 𝓱𝓸𝓶₍_,B₎₁
    ; _₂_ = λ {A A′}
              {f₁ f₂ : 𝓒 ᵒᵖ ∣ A ⟶ A′}
              f₁≈f₂
              {g₁ g₂ : 𝓒    ∣ A ⟶ B }
              g₁≈g₂ → ∘-cong₂ 𝓒 g₁≈g₂ f₁≈f₂
    ; resp-∘₀ = λ {A}
                  {g₁ g₂ : 𝓒 ∣ A ⟶ B}
                  g₁≈g₂ → begin
      g₁ ∘ id  ↓⟨ ∘-unitʳ 𝓒 ⟩
      g₁       ↓⟨ g₁≈g₂ ⟩
      g₂       ∎
    ; resp-∘₂ = λ {A A′ A″}
                  {f     : 𝓒 ᵒᵖ ∣ A  ⟶ A′}
                  {f′    : 𝓒 ᵒᵖ ∣ A′ ⟶ A″}
                  {g₁ g₂ : 𝓒    ∣ A  ⟶ B }
                  g₁≈g₂ → begin
      g₁ ∘ (f′ ∘̅ f)  ↓⟨ g₁≈g₂ ⟩∘⟨ refl ⟩
      g₂ ∘ (f ∘ f′)  ↑⟨ ∘-assoc 𝓒 ⟩
      (g₂ ∘ f) ∘ f′  ∎
    }

open Covariant

𝓱𝓸𝓶₍_,_₎₀ : ob (𝓒 ᵒᵖ) → ∀ B → Setoid
𝓱𝓸𝓶₍ A , B ₎₀ = 𝓱𝓸𝓶₍_,B₎₀ B A

𝓱𝓸𝓶₍_,_₎₁ : ∀ {A A′}
  → 𝓒 ᵒᵖ ∣      A        ⟶      A′
  → ∀ B
  → 𝓢𝓮𝓽  ∣ 𝓱𝓸𝓶₍ A , B ₎₀ ⟶ 𝓱𝓸𝓶₍ A′ , B ₎₀
𝓱𝓸𝓶₍ f , B ₎₁ = 𝓱𝓸𝓶₍_,B₎₁ B f

𝓱𝓸𝓶₍-,_₎ : ob 𝓒 → 𝓒 ᵒᵖ ⟶ 𝓢𝓮𝓽
𝓱𝓸𝓶₍-, B ₎ = 𝓱𝓸𝓶₍-,B₎ B

𝓱₍_₎₀ = 𝓱𝓸𝓶₍-,_₎

module Contravariant (A : ob (𝓒 ᵒᵖ)) where
  𝓱𝓸𝓶⁽A,_⁾⁰ : ob 𝓒 → Setoid
  𝓱𝓸𝓶⁽A, B ⁾⁰ = 𝒉𝒐𝒎 𝓒 A B

  𝓱𝓸𝓶⁽A,_⁾¹ : ∀ {B B′}
    → 𝓒   ∣        B    ⟶        B′
    → 𝓢𝓮𝓽 ∣ 𝓱𝓸𝓶⁽A, B ⁾⁰ ⟶ 𝓱𝓸𝓶⁽A, B′ ⁾⁰
  𝓱𝓸𝓶⁽A, h ⁾¹ = record
    { _₀_ =       h    ∘_
    ; _₁_ = refl₍ h ₎ ⟩∘⟨_
    }

  𝓱𝓸𝓶⁽A,-⁾ : 𝓒 ⟶ 𝓢𝓮𝓽
  𝓱𝓸𝓶⁽A,-⁾ = record
    { _₀_ = 𝓱𝓸𝓶⁽A,_⁾⁰
    ; _₁_ = 𝓱𝓸𝓶⁽A,_⁾¹
    ; _₂_ = λ {B B′}
              {h₁ h₂ : 𝓒 ∣ B ⟶ B′}
              h₁≈h₂
              {g₁ g₂ : 𝓒 ∣ A ⟶ B }
              g₁≈g₂ → ∘-cong₂ 𝓒 h₁≈h₂ g₁≈g₂
    ; resp-∘₀ = λ {B}
                  {g₁ g₂ : 𝓒 ∣ A ⟶ B}
                  g₁≈g₂ → begin
      id ∘ g₁  ↓⟨ ∘-unitˡ 𝓒 ⟩
      g₁       ↓⟨ g₁≈g₂ ⟩
      g₂       ∎
    ; resp-∘₂ = λ {B B′ B″}
                  {h     : 𝓒 ∣ B  ⟶ B′}
                  {h′    : 𝓒 ∣ B′ ⟶ B″}
                  {g₁ g₂ : 𝓒 ∣ A  ⟶ B }
                  g₁≈g₂ → begin
      (h′ ∘ h) ∘ g₁  ↓⟨ refl ⟩∘⟨ g₁≈g₂ ⟩
      (h′ ∘ h) ∘ g₂  ↓⟨ ∘-assoc 𝓒 ⟩
      h′ ∘ (h ∘ g₂)  ∎
    }

open Contravariant public renaming
  ( 𝓱𝓸𝓶⁽A,_⁾⁰ to 𝓱𝓸𝓶⁽_,_⁾⁰
  ; 𝓱𝓸𝓶⁽A,_⁾¹ to 𝓱𝓸𝓶⁽_,_⁾¹
  ; 𝓱𝓸𝓶⁽A,-⁾  to 𝓱𝓸𝓶⁽_,-⁾
  )

𝓱⁽_⁾⁰ = 𝓱𝓸𝓶⁽_,-⁾

module Naturality where
  𝓱₍_₎₁ : ∀ {B B′}
    → 𝓒              ∣    B    ⟶    B′
    → [ 𝓒 ᵒᵖ , 𝓢𝓮𝓽 ] ∣ 𝓱₍ B ₎₀ ⟶ 𝓱₍ B′ ₎₀
  𝓱₍_₎₁ {B} {B′} h = record
    { _₍_₎    = λ A → 𝓱𝓸𝓶⁽ A , h ⁾¹
    ; natural = λ {A A′}
                  {f     : 𝓒 ᵒᵖ ∣ A ⟶ A′}
                  {g₁ g₂ : 𝓒    ∣ A ⟶ B }
                  g₁≈g₂ → begin
      h ∘ (g₁ ∘ f)  ↓⟨ refl ⟩∘⟨ g₁≈g₂ ⟩∘⟨ refl ⟩
      h ∘ (g₂ ∘ f)  ↑⟨ ∘-assoc 𝓒 ⟩
      (h ∘ g₂) ∘ f  ∎
    }

  𝓱⁽_⁾¹ : ∀ {A A′}
    → 𝓒 ᵒᵖ        ∣    A    ⟶    A′
    → [ 𝓒 , 𝓢𝓮𝓽 ] ∣ 𝓱⁽ A ⁾⁰ ⟶ 𝓱⁽ A′ ⁾⁰
  𝓱⁽_⁾¹ {A} {A′} f = record
    { _₍_₎    = λ B → 𝓱𝓸𝓶₍ f , B ₎₁
    ; natural = λ {B B′}
                  {h     : 𝓒 ∣ B ⟶ B′}
                  {g₁ g₂ : 𝓒 ∣ A ⟶ B }
                  g₁≈g₂ → begin
      (h ∘ g₁) ∘ f  ↓⟨ ∘-assoc 𝓒 ⟩
      h ∘ (g₁ ∘ f)  ↓⟨ refl ⟩∘⟨ g₁≈g₂ ⟩∘⟨ refl ⟩
      h ∘ (g₂ ∘ f)  ∎
    }

open Naturality public

module Yoneda where
  𝓱₋ : 𝓒 ⟶ [ 𝓒 ᵒᵖ , 𝓢𝓮𝓽 ]
  𝓱₋ = record
    { _₀_ = 𝓱₍_₎₀
    ; _₁_ = 𝓱₍_₎₁
    ; _₂_ = λ {B B′}
              {h₁ h₂ : 𝓒 ∣ B ⟶ B′}
              h₁≈h₂ A
              {g₁ g₂ : 𝓒 ∣ A ⟶ B }
              g₁≈g₂ → ∘-cong₂ 𝓒 h₁≈h₂ g₁≈g₂
    ; resp-∘₀ = λ {B} A
                  {g₁ g₂ : 𝓒 ∣ A ⟶ B}
                  g₁≈g₂ → begin
      id ∘ g₁  ↓⟨ ∘-unitˡ 𝓒 ⟩
      g₁       ↓⟨ g₁≈g₂ ⟩
      g₂       ∎
    ; resp-∘₂ = λ {B B′ B″}
                  {h     : 𝓒 ∣ B  ⟶ B′}
                  {h′    : 𝓒 ∣ B′ ⟶ B″}
                  A
                  {g₁ g₂ : 𝓒 ∣ A  ⟶ B }
                  g₁≈g₂ → begin
      (h′ ∘ h) ∘ g₁  ↓⟨ refl ⟩∘⟨ g₁≈g₂ ⟩
      (h′ ∘ h) ∘ g₂  ↓⟨ ∘-assoc 𝓒 ⟩
      h′ ∘ (h ∘ g₂)  ∎
    }

open Yoneda public

module Yoda where
  𝓱⁻ : 𝓒 ᵒᵖ ⟶ [ 𝓒 , 𝓢𝓮𝓽 ]
  𝓱⁻ = record
    { _₀_ = 𝓱⁽_⁾⁰
    ; _₁_ = 𝓱⁽_⁾¹
    ; _₂_ = λ {A A′}
              {f₁ f₂ : 𝓒 ᵒᵖ ∣ A ⟶ A′}
              f₁≈f₂ B
              {g₁ g₂ : 𝓒    ∣ A ⟶ B }
              g₁≈g₂ → ∘-cong₂ 𝓒 g₁≈g₂ f₁≈f₂
    ; resp-∘₀ = λ {A} B
                  {g₁ g₂ : 𝓒 ∣ A ⟶ B}
                  g₁≈g₂ → begin
      g₁ ∘ id  ↓⟨ ∘-unitʳ 𝓒 ⟩
      g₁       ↓⟨ g₁≈g₂ ⟩
      g₂       ∎
    ; resp-∘₂ = λ {A A′ A″}
                  {f     : 𝓒 ᵒᵖ ∣ A  ⟶ A′}
                  {f′    : 𝓒 ᵒᵖ ∣ A′ ⟶ A″}
                  B
                  {g₁ g₂ : 𝓒    ∣ A  ⟶ B }
                  g₁≈g₂ → begin
      g₁ ∘ (f′ ∘̅ f)  ↓⟨ g₁≈g₂ ⟩∘⟨ refl ⟩
      g₂ ∘ (f ∘ f′)  ↑⟨ ∘-assoc 𝓒 ⟩
      (g₂ ∘ f) ∘ f′  ∎
    }

open Yoda public
