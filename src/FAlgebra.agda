{-# OPTIONS --guardedness #-}

module FAlgebra where

open import GeneralizedPolynomial
  using (Polynomial; ⟦_⟧; ⟦_⟧₀; ⟦_⟧₁; K_; ∅; _,_)
open import Relation.Binary.PropositionalEquality

open Polynomial
open GeneralizedPolynomial.LeastFixpoint

Algebra : Polynomial 1 → Set → Set
Algebra F A = ⟦ F ⟧₁ A → A

-- lemma : (F : Polynomial) → ⟦ F ⟧₁ ⟦ μ F ⟧ₒ ≡ ⟦ F ⟧₁ (∅, μ F)

cata : {F : Polynomial 1} {A : Set} → Algebra F A → ⟦ μ F ⟧₀ → A
cata {F} ϕ μ⟨ x ⟩ = ϕ (mapCata F F ϕ x)
  where
    mapCata : {X : Set} → (F G : Polynomial 1) → Algebra G X → ⟦ F ⟧ (∅ , (μ G)) → ⟦ F ⟧₁ X
    mapCata {X} F G ϕ x = {!!}

