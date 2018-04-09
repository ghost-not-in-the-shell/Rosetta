{-# OPTIONS --type-in-type #-}
module Rosetta.Categories where
open import Rosetta.CartesianClosed
open import Rosetta.Category
open import Rosetta.Equality
open import Rosetta.Equivalence
open import Rosetta.Functor
open import Rosetta.Functors
open import Rosetta.NaturalTransformation
open import Rosetta.Prelude
open import Rosetta.Sets
import Rosetta.DiagrammaticReasoning as DiagrammaticReasoning

instance
  𝓒𝓪𝓽-op : Op _⟶_
  𝓒𝓪𝓽-op =
    let open EqReasoning

        id : ∀ {𝓒} → 𝓒 ⟶ 𝓒
        id = record
          { _₀_ = id
          ; _₁_ = id
          ; _₂_ = id
          ; resp-∘₀ = refl
          ; resp-∘₂ = refl
          }

        _∘_ : ∀ {𝓒 𝓓 𝓔} → 𝓓 ⟶ 𝓔 → 𝓒 ⟶ 𝓓 → 𝓒 ⟶ 𝓔
        _∘_ {𝓒} 𝓖 𝓕 = record
          { _₀_ = 𝓖 ₀_ ∘ 𝓕 ₀_
          ; _₁_ = 𝓖 ₁_ ∘ 𝓕 ₁_
          ; _₂_ = 𝓖 ₂_ ∘ 𝓕 ₂_
          ; resp-∘₀ = λ {A} → begin
            𝓖 ₁ 𝓕 ₁ id₍ A ₎  ↓⟨ 𝓖 ₂ (resp-∘₀ 𝓕) ⟩
            𝓖 ₁ id₍ 𝓕 ₀ A ₎  ↓⟨ resp-∘₀ 𝓖 ⟩
            id₍ 𝓖 ₀ 𝓕 ₀ A ₎  ∎
          ; resp-∘₂ = λ {A B C}
                        {f : 𝓒 ∣ A ⟶ B}
                        {g : 𝓒 ∣ B ⟶ C}
                        → begin
            𝓖 ₁ 𝓕 ₁ (g ∘ f)        ↓⟨ 𝓖 ₂ (resp-∘₂ 𝓕) ⟩
            𝓖 ₁ (𝓕 ₁ g ∘ 𝓕 ₁ f)    ↓⟨ resp-∘₂ 𝓖 ⟩
            𝓖 ₁ 𝓕 ₁ g ∘ 𝓖 ₁ 𝓕 ₁ f  ∎
          }
    in record
      { id  = id
      ; _∘_ = _∘_
      }

module _ {𝓒 𝓓} where
  record 𝓒𝓪𝓽∣_≈_ (𝓕 𝓖 : 𝓒 ⟶ 𝓓) : Set where
    constructor _,_
    field
      𝓕₀≡𝓖₀ : 𝓕 ₀_ ≡ 𝓖 ₀_
      𝓕₁≈𝓖₁ : ∀ {A B} {f g : 𝓒 ∣ A ⟶ B}
        → 𝓒 ∣ f ≈ g
        → 𝓓 ∣ transport (λ 𝓕₀ → 𝓓 ∣ 𝓕₀ A ⟶ 𝓕₀ B) 𝓕₀≡𝓖₀ (𝓕 ₁ f) ≈ 𝓖 ₁ g

  .𝓒𝓪𝓽≈-refl  : ∀ {𝓕} → 𝓒𝓪𝓽∣ 𝓕 ≈ 𝓕
  .𝓒𝓪𝓽≈-sym   : ∀ {𝓕 𝓖} → 𝓒𝓪𝓽∣ 𝓕 ≈ 𝓖 → 𝓒𝓪𝓽∣ 𝓖 ≈ 𝓕
  .𝓒𝓪𝓽≈-trans : ∀ {𝓕 𝓖 𝓗} → 𝓒𝓪𝓽∣ 𝓕 ≈ 𝓖 → 𝓒𝓪𝓽∣ 𝓖 ≈ 𝓗 → 𝓒𝓪𝓽∣ 𝓕 ≈ 𝓗
  𝓒𝓪𝓽≈-refl  {𝓕}                               = ≡-refl , λ f≈g → 𝓕 ₂ f≈g
  𝓒𝓪𝓽≈-sym   (≡-refl , 𝓕₁≈𝓖₁)                  = ≡-refl , λ f≈g → sym (𝓕₁≈𝓖₁ (sym f≈g))
  𝓒𝓪𝓽≈-trans (≡-refl , 𝓕₁≈𝓖₁) (≡-refl , 𝓖₁≈𝓗₁) = ≡-refl , λ f≈g → trans (𝓕₁≈𝓖₁ f≈g) (𝓖₁≈𝓗₁ refl)

  instance
    𝓒𝓪𝓽≈-equiv : IsEquivalence 𝓒𝓪𝓽∣_≈_
    𝓒𝓪𝓽≈-equiv = record
      { refl  = 𝓒𝓪𝓽≈-refl
      ; sym   = 𝓒𝓪𝓽≈-sym
      ; trans = 𝓒𝓪𝓽≈-trans
      }

𝓒𝓪𝓽 : Category
𝓒𝓪𝓽 = record
  { ob  = Category
  ; hom = Functor
  ; _≈_ = 𝓒𝓪𝓽∣_≈_
  ; ∘-cong₂ = λ { (≡-refl , 𝓖₁≈𝓖′₁) (≡-refl , 𝓕₁≈𝓕′₁) → ≡-refl , λ f≈f′ → 𝓖₁≈𝓖′₁ (𝓕₁≈𝓕′₁ f≈f′) }
  ; ∘-unitˡ = refl
  ; ∘-unitʳ = refl
  ; ∘-assoc = refl
  }

{-# DISPLAY 𝓒𝓪𝓽∣_≈_ 𝓕 𝓖 = 𝓒𝓪𝓽 ∣ 𝓕 ≈ 𝓖 #-}

module 𝓒𝓪𝓽 where
  infixr 6 _×_
  infixr 7 _⇒_

  𝟙 : Category
  𝟙 = record
    { ob  = 𝓢et.𝟙
    ; hom = λ _ _ → 𝓢et.𝟙
    ; _≈_ = λ _ _ → 𝓢et.𝟙
    ; op  = record
      { id  =         tt
      ; _∘_ = λ _ _ → tt
      }
    ; ≈-equiv = record
      { refl  =         tt
      ; sym   = λ _   → tt
      ; trans = λ _ _ → tt
      }
    ; ∘-cong₂ = λ _ _ → tt
    ; ∘-unitˡ = tt
    ; ∘-unitʳ = tt
    ; ∘-assoc = tt
    }

  _×_ : Category → Category → Category
  𝓒 × 𝓓 = record
    { ob  = ob 𝓒 𝓢et.× ob 𝓓
    ; hom = λ { (A₁ , A₂) (B₁ , B₂) → (𝓒 ∣ A₁ ⟶ B₁) 𝓢et.× (𝓓 ∣ A₂ ⟶ B₂) }
    ; _≈_ = λ { (f₁ , f₂) (g₁ , g₂) → (𝓒 ∣ f₁ ≈ g₁) 𝓢et.× (𝓓 ∣ f₂ ≈ g₂) }
    ; op  = record
      { id  = id , id
      ; _∘_ = λ { (g₁ , g₂) (f₁ , f₂) → g₁ ∘ f₁ , g₂ ∘ f₂ } }
    ; ≈-equiv = record
      { refl  = refl , refl
      ; sym   = λ { (f₁≈g₁ , f₂≈g₂) → sym f₁≈g₁ , sym f₂≈g₂ }
      ; trans = λ { (f₁≈g₁ , f₂≈g₂) (g₁≈h₁ , g₂≈h₂) → trans f₁≈g₁ g₁≈h₁ , trans f₂≈g₂ g₂≈h₂ }
      }
    ; ∘-cong₂ = λ { (g₁≈g₂ , g₁′≈g₂′) (f₁≈f₂ , f₁′≈f₂′) → ∘-cong₂ 𝓒 g₁≈g₂ f₁≈f₂ , ∘-cong₂ 𝓓 g₁′≈g₂′ f₁′≈f₂′ }
    ; ∘-unitˡ = ∘-unitˡ 𝓒 , ∘-unitˡ 𝓓
    ; ∘-unitʳ = ∘-unitʳ 𝓒 , ∘-unitʳ 𝓓
    ; ∘-assoc = ∘-assoc 𝓒 , ∘-assoc 𝓓
    }

  _⇒_ = [_,_]

open 𝓒𝓪𝓽

instance
  𝓒𝓪𝓽-op✓ : Op✓ _⟶_
  𝓒𝓪𝓽-op✓ =
    let ! : ∀ {𝓧} → 𝓧 ⟶ 𝟙
        ! = record
          { _₀_ = !
          ; _₁_ = !
          ; _₂_ = !
          ; resp-∘₀ = tt
          ; resp-∘₂ = tt
          }

        π₁ : ∀ {𝓒 𝓓} → 𝓒 × 𝓓 ⟶ 𝓒
        π₁ = record
          { _₀_ = π₁
          ; _₁_ = π₁
          ; _₂_ = π₁
          ; resp-∘₀ = refl
          ; resp-∘₂ = refl
          }

        π₂ : ∀ {𝓒 𝓓} → 𝓒 × 𝓓 ⟶ 𝓓
        π₂ = record
          { _₀_ = π₂
          ; _₁_ = π₂
          ; _₂_ = π₂
          ; resp-∘₀ = refl
          ; resp-∘₂ = refl
          }

        ⟨_,_⟩ : ∀ {𝓒 𝓓 𝓧} → 𝓧 ⟶ 𝓒 → 𝓧 ⟶ 𝓓 → 𝓧 ⟶ 𝓒 × 𝓓
        ⟨ 𝓕 , 𝓖 ⟩ = record
          { _₀_ = ⟨ 𝓕 ₀_ , 𝓖 ₀_ ⟩
          ; _₁_ = ⟨ 𝓕 ₁_ , 𝓖 ₁_ ⟩
          ; _₂_ = ⟨ 𝓕 ₂_ , 𝓖 ₂_ ⟩
          ; resp-∘₀ = resp-∘₀ 𝓕 , resp-∘₀ 𝓖
          ; resp-∘₂ = resp-∘₂ 𝓕 , resp-∘₂ 𝓖
          }

        ε : ∀ {𝓒 𝓓} → [ 𝓒 , 𝓓 ] × 𝓒 ⟶ 𝓓
        ε {𝓒} {𝓓} =
          let open DiagrammaticReasoning 𝓓
          in record
          { _₀_ = λ { (𝓕 , A) → 𝓕 ₀ A }
          ; _₁_ = λ { {𝓕 , A} {𝓖 , B} (α , f) → α ₍ B ₎ ∘ 𝓕 ₁ f }
          ; _₂_ = λ { {𝓕 , A} {𝓖 , B} {α , f} {α′ , f′} (α≈α′ , f≈f′) → ∘-cong₂ 𝓓 (α≈α′ B) (𝓕 ₂ f≈f′) }
          ; resp-∘₀ = λ { {𝓕 , A} → begin
            id ∘ 𝓕 ₁ id  ↓⟨ refl ⟩∘⟨ resp-∘₀ 𝓕 ⟩
            id ∘ id      ↓⟨ ∘-unitˡ 𝓓 ⟩
            id           ∎ }
          ; resp-∘₂ = λ { {𝓕 , A} {𝓖 , B} {𝓗 , C}
                          {α , f} -- α : 𝓝𝓪𝓽 ∣ 𝓕 ⟶ 𝓖
                                  -- f : 𝓒   ∣ A ⟶ B
                          {β , g} -- β : 𝓝𝓪𝓽 ∣ 𝓖 ⟶ 𝓗
                                  -- g : 𝓒   ∣ B ⟶ C
                          → begin
            (β ⋆ α) ₍ C ₎ ∘ 𝓕 ₁ (g ∘ f)            ↓⟨ refl ⟩∘⟨ resp-∘₂ 𝓕 ⟩
            (β ₍ C ₎ ∘ α ₍ C ₎) ∘ (𝓕 ₁ g ∘ 𝓕 ₁ f)  ↓⟨ ∘-assoc 𝓓 ⟩
            β ₍ C ₎ ∘ (α ₍ C ₎ ∘ (𝓕 ₁ g ∘ 𝓕 ₁ f))  ↑⟨ refl ⟩∘⟨ ∘-assoc 𝓓 ⟩
            β ₍ C ₎ ∘ ((α ₍ C ₎ ∘ 𝓕 ₁ g) ∘ 𝓕 ₁ f)  ↓⟨ refl ⟩∘⟨ natural α ⟩∘⟨ refl ⟩
            β ₍ C ₎ ∘ ((𝓖 ₁ g ∘ α ₍ B ₎) ∘ 𝓕 ₁ f)  ↓⟨ refl ⟩∘⟨ ∘-assoc 𝓓 ⟩
            β ₍ C ₎ ∘ (𝓖 ₁ g ∘ (α ₍ B ₎ ∘ 𝓕 ₁ f))  ↑⟨ ∘-assoc 𝓓 ⟩
            (β ₍ C ₎ ∘ 𝓖 ₁ g) ∘ (α ₍ B ₎ ∘ 𝓕 ₁ f)  ∎ }
          }

        ƛ_ : ∀ {𝓒 𝓓 𝓧} → 𝓧 × 𝓒 ⟶ 𝓓 → 𝓧 ⟶ [ 𝓒 , 𝓓 ]
        ƛ_ {𝓒} {𝓓} {𝓧} 𝓕 =
          let open DiagrammaticReasoning
          in record
          { _₀_ = λ A → record
            { _₀_ = λ B → 𝓕 ₀ (A , B)
            ; _₁_ = λ {B₁ B₂} (b : 𝓒 ∣ B₁ ⟶ B₂) → 𝓕 ₁ (id₍ A ₎ , b)
            ; _₂_ = λ {B₁ B₂ b₁ b₂} b₁≈b₂ → 𝓕 ₂ (refl₍ id₍ A ₎ ₎ , b₁≈b₂)
            ; resp-∘₀ = resp-∘₀ 𝓕
            ; resp-∘₂ = λ {B₁ B₂ B₃}
                          {b₁ : 𝓒 ∣ B₁ ⟶ B₂}
                          {b₂ : 𝓒 ∣ B₂ ⟶ B₃}
                          → begin
              𝓕 ₁ (id , b₂ ∘ b₁)             ↑⟨ 𝓕 ₂ (∘-unitˡ 𝓧 , refl) ⟩
              𝓕 ₁ (id ∘ id , b₂ ∘ b₁)        ↓⟨ resp-∘₂ 𝓕 ⟩
              𝓕 ₁ (id , b₂) ∘ 𝓕 ₁ (id , b₁)  ∎
            }
          ; _₁_ = λ {A₁ A₂} (a : 𝓧 ∣ A₁ ⟶ A₂) → record
            { _₍_₎    = λ B → 𝓕 ₁ (a , id₍ B ₎)
            ; natural = λ {B₁ B₂}
                          {b : 𝓒 ∣ B₁ ⟶ B₂}
                          → begin
              𝓕 ₁ (a , id) ∘ 𝓕 ₁ (id , b)  ↑⟨ resp-∘₂ 𝓕 ⟩
              𝓕 ₁ (a ∘ id , id ∘ b)        ↓⟨ 𝓕 ₂ (◁→▷ 𝓧 (∘-unitʳ 𝓧) (∘-unitˡ 𝓧) , ◁→▷ 𝓒 (∘-unitˡ 𝓒) (∘-unitʳ 𝓒)) ⟩
              𝓕 ₁ (id ∘ a , b ∘ id)        ↓⟨ resp-∘₂ 𝓕 ⟩
              𝓕 ₁ (id , b) ∘ 𝓕 ₁ (a , id)  ∎
            }
          ; _₂_ = λ {A₁ A₂} {a₁ a₂ : 𝓧 ∣ A₁ ⟶ A₂} a₁≈a₂ B → 𝓕 ₂ (a₁≈a₂ , refl₍ id₍ B ₎ ₎)
          ; resp-∘₀ = λ A → resp-∘₀ 𝓕
          ; resp-∘₂ = λ {A₁ A₂ A₃}
                        {a₁ : 𝓧 ∣ A₁ ⟶ A₂}
                        {a₂ : 𝓧 ∣ A₂ ⟶ A₃}
                        B → begin
            𝓕 ₁ (a₂ ∘ a₁ , id)             ↑⟨ 𝓕 ₂ (refl , ∘-unitʳ 𝓒) ⟩
            𝓕 ₁ (a₂ ∘ a₁ , id ∘ id)        ↓⟨ resp-∘₂ 𝓕 ⟩
            𝓕 ₁ (a₂ , id) ∘ 𝓕 ₁ (a₁ , id)  ∎
          }
    in record
    { 𝟙   = 𝟙
    ; _×_ = _×_
    ; _⇒_ = _⇒_
    ; !     = !
    ; π₁    = λ {𝓒 𝓓} → π₁ {𝓒} {𝓓}
    ; π₂    = λ {𝓒 𝓓} → π₂ {𝓒} {𝓓}
    ; ⟨_,_⟩ = ⟨_,_⟩
    ; ε     = ε
    ; ƛ_    = ƛ_
    }
