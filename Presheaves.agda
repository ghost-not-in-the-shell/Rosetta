{-# OPTIONS --type-in-type #-}
module Rosetta.Presheaves where
open import Rosetta.Category
open import Rosetta.Functors
open import Rosetta.Setoids

𝓟𝓼𝓱 : Category → Category
𝓟𝓼𝓱 𝓒 = [ 𝓒 ᵒᵖ , 𝓢𝓮𝓽 ]
