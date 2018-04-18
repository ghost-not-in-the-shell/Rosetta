{-# OPTIONS --type-in-type #-}
module Rosetta.Prelude.Product where

infixr 4 _,_
record Product (A B : Set) : Set where
  constructor _,_
  field
    π₁ : A
    π₂ : B
