{-# OPTIONS --guardedness #-}

module FAlgebra where

open import GeneralizedPolynomial
  using (Polynomial; ⟦_⟧; ⟦_⟧₀; ⟦_⟧₁; K_; ∅; _,_)
open import Relation.Binary.PropositionalEquality
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Nat using (suc)

open Polynomial
open GeneralizedPolynomial.LeastFixpoint

Algebra : Polynomial 1 → Set → Set
Algebra F A = ⟦ F ⟧₁ A → A

cata : {F : Polynomial 1} {A : Set} → Algebra F A → ⟦ μ F ⟧₀ → A
cata {F} ϕₒ μ⟨ x ⟩ = ϕₒ (mapCata F F ϕₒ x)
  where
    mapCata : {X : Set} → (F G : Polynomial 1) → Algebra G X → ⟦ F ⟧ (∅ , (μ G)) → ⟦ F ⟧₁ X
    mapCata {X} (I 0)       G ϕ μ⟨ x ⟩    = ϕ (mapCata G G ϕ x)
    mapCata {X} (L ⊕ᵣ R)    G ϕ (inj₁ xₗ) = inj₁ (mapCata L G ϕ xₗ)
    mapCata {X} (L ⊕ᵣ R)    G ϕ (inj₂ xᵣ) = inj₂ (mapCata R G ϕ xᵣ)
    mapCata {X} (L ⊗ᵣ R)    G ϕ (xₗ , xᵣ) = mapCata L G ϕ xₗ , mapCata R G ϕ xᵣ
    mapCata {X} (μ F)       G ϕ μ⟨ x ⟩    = μ⟨ ? ⟩
    mapCata {X} (ν F)       G ϕ x         = {!!}
    mapCata {X} (wk_ {0} P) G ϕ x         = x
    mapCata {X} (wk_ {1} P) G ϕ x         = mapCata P G ϕ x

