{-# OPTIONS --guardedness #-}

module Common.FCoAlgebra where

open import Common.Polynomial using (Polynomial; ⟦_⟧)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)

open Common.Polynomial.Polynomial

record ν_ (F : Polynomial) : Set where
    coinductive
    field
        rest : ⟦ F ⟧ (ν F)
open ν_

Co-Algebra : Polynomial → Set → Set
Co-Algebra F A = A → ⟦ F ⟧ A

ana : {F : Polynomial} {A : Set} → Co-Algebra F A → A → ν F
rest (ana {F} ϕ x) = mapAna F F ϕ (ϕ x)
    where
        mapAna : ∀ {X} F G → Co-Algebra F X → ⟦ G ⟧ X → ⟦ G ⟧ (ν F)
        mapAna F I       ϕ x          = ana ϕ x
        mapAna F (K C)   ϕ x          = x
        mapAna F (L ⊕ R) ϕ (inj₁ xₗ) = inj₁ (mapAna F L ϕ xₗ)
        mapAna F (L ⊕ R) ϕ (inj₂ xᵣ) = inj₂ (mapAna F R ϕ xᵣ)
        mapAna F (L ⊗ R) ϕ (xₗ , xᵣ) = mapAna F L ϕ xₗ , mapAna F R ϕ xᵣ
