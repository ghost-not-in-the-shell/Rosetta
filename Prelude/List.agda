{-# OPTIONS --type-in-type #-}
module Rosetta.Prelude.List where
open import Agda.Builtin.List public
open import Rosetta.Prelude.Product renaming (Product to _×_)

infixr 5 _∷_
data All {A : Set} (P : A → Set) : List A → Set where
  []  : All P []
  _∷_ : ∀ {x xs} → P x → All P xs → All P (x ∷ xs)

fst : ∀ {A : Set} {P : A → Set} {x xs} → All P (x ∷ xs) → P x
fst (px ∷ pxs) = px

map : ∀ {A : Set} {P Q : A → Set}
  → (∀ {x}  →     P x  →     Q x)
  → (∀ {xs} → All P xs → All Q xs)
map f []         = []
map f (px ∷ pxs) = f px ∷ map f pxs

infix 4 _∈_
data _∈_ {A : Set} : A → List A → Set where
  ze : ∀ {x   xs}          → x ∈ x ∷ xs
  su : ∀ {x y xs} → x ∈ xs → x ∈ y ∷ xs

lookup : ∀ {A : Set} {P : A → Set} {xs}
  → All P xs → ∀ {x} → x ∈ xs → P x
lookup (px ∷ pxs) ze     = px
lookup (px ∷ pxs) (su i) = lookup pxs i
