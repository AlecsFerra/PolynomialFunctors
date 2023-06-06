{-# OPTIONS --guardedness #-}

module Derivative where

open import GeneralizedPolynomial
  using (Polynomial; 𝟘; 𝟙; wkᵢ)

open import Data.Nat
  using (ℕ; _≟_; _≥_; suc; _≥?_; s≤s; z≤n; pred; _∸_; _+_)
open import Data.Nat.Properties using (≤-reflexive; ≤-step; n≤1+n)
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)


open import Relation.Binary.PropositionalEquality
  using (refl)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable
  using (toWitness; fromWitness; True)

open Polynomial
open GeneralizedPolynomial.LeastFixpoint
open GeneralizedPolynomial.GreatestFixpoint

mutual

  derivative : {n : ℕ} → (m : ℕ) → Polynomial n → Polynomial n
  derivative {n} m       (I k)     with k ≟ m
  ...                              | yes refl = wkᵢ 𝟙 z≤n
  ...                              | no  k≢m  = wkᵢ 𝟘 z≤n
  derivative {n} m       (K x)                = 𝟘
  derivative {n} m       (μ P)                = μ (wkᵢ (derivative (suc m) P [ μ P ]) (n≤1+n _)
                                              ⊕ᵣ   wkᵢ (derivative 0       P [ μ P ]) (n≤1+n _)
                                              ⊗ᵣ   wkᵢ (I 0)                          (s≤s z≤n))
  derivative {n} m       (ν P)                = ν (wkᵢ (derivative (suc m) P [ ν P ]) (n≤1+n _)
                                              ⊕ᵣ   wkᵢ (derivative 0       P [ ν P ]) (n≤1+n _)
                                              ⊗ᵣ   wkᵢ (I 0)                          (s≤s z≤n))
  derivative {n} 0       (wkᵣ P)              = wkᵢ 𝟘 z≤n
  derivative {n} (suc m) (wkᵣ P)              = wkᵣ (derivative m P)
  derivative {n} m       (L ⊕ᵣ R)             = derivative m L ⊕ᵣ derivative m R
  derivative {n} m       (L ⊗ᵣ R)             = (derivative m L ⊗ᵣ R) ⊕ᵣ (L ⊕ᵣ derivative m R)
  derivative {n} m       (F [ G ])            =  derivative (suc m) F [ G ]
                                              ⊕ᵣ derivative 0       F [ G ]
                                              ⊗ᵣ derivative m       G

infixl 10 ∂_
infixl 10 ∂_∙_

∂_ : {n : ℕ} → Polynomial n → Polynomial n
∂ P = derivative 1 P

∂_∙_ : {n : ℕ} → (m : ℕ) → {True (n ≥? m)} → Polynomial n → Polynomial n
∂_∙_ m {m≤n} P = derivative m P


