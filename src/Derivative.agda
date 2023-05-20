module Derivative where

open import Polynomial using (Polynomial)
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)

open Polynomial.Polynomial


infixl 10 ∂_

∂_ : Polynomial → Polynomial
∂ I        = K ⊤
∂ K k      = K ⊥
∂ (L ⊗ R) = ∂ L ⊗ R ⊕ L ⊗ ∂ R
∂ (L ⊕ R) = ∂ L ⊕ ∂ R
