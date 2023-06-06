{-# OPTIONS --guardedness #-}

module CommonToGeneralized where

open import GeneralizedPolynomial as GP
open import Common.Polynomial as P

open import Relation.Binary.PropositionalEquality
    using (refl; _≡_)

open GP.Polynomial
open P.Polynomial

compile : P.Polynomial → GP.Polynomial 1
compile I       = I_ 0
compile (L ⊗ R) = compile L ⊗ᵣ compile R
compile (L ⊕ R) = compile L ⊕ᵣ compile R
compile (K C)   = wkᵣ (K C)

compile-same : {A : Set} → (P : P.Polynomial) → P.⟦ P ⟧ A ≡ ⟦ compile P ⟧₁ A
compile-same {A} I       = refl
compile-same {A} (K x)   = refl
compile-same {A} (L ⊗ R) rewrite (compile-same {A} L)
                         rewrite (compile-same {A} R)
                         = refl
compile-same {A} (L ⊕ R) rewrite (compile-same {A} L)
                         rewrite (compile-same {A} R)
                         = refl

