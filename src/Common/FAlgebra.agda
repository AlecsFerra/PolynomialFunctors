module Common.FAlgebra where

open import Common.Polynomial using (Polynomial; ⟦_⟧)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)

open Common.Polynomial.Polynomial

data μ_ (F : Polynomial) : Set where
    μ⟨_⟩ : ⟦ F ⟧ (μ F) → μ F

Algebra : Polynomial → Set → Set
Algebra F A = ⟦ F ⟧ A → A

cata : {F : Polynomial} {A : Set} → Algebra F A → μ F → A
cata {F} ϕ μ⟨ x ⟩ = ϕ (mapCata F F ϕ x)
    where
        mapCata : ∀ {X} F G → Algebra G X → ⟦ F ⟧ (μ G) → ⟦ F ⟧ X
        mapCata I       G ϕ μ⟨ x ⟩    = ϕ (mapCata G G ϕ x)
        mapCata (K C)   G ϕ x         = x
        mapCata (L ⊕ R) G ϕ (inj₁ xₗ) = inj₁ (mapCata L G ϕ xₗ)
        mapCata (L ⊕ R) G ϕ (inj₂ xᵣ) = inj₂ (mapCata R G ϕ xᵣ)
        mapCata (L ⊗ R) G ϕ (xₗ , xᵣ) = mapCata L G ϕ xₗ , mapCata R G ϕ xᵣ
