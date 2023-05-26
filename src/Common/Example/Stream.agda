{-# OPTIONS --guardedness #-}

module Common.Example.Stream where

open import Common.Polynomial using (Polynomial)
open import Common.FCoAlgebra using (ν_; ana)
open import Data.Unit using (tt)
open import Data.Product using (_,_; _×_; proj₁; proj₂)


open Common.Polynomial.Polynomial
open ν_

StreamF : Set → Polynomial
StreamF A = K A ⊗ I

Stream : Set → Set
Stream A = ν (StreamF A)

repeat : {A : Set} → A → Stream A
repeat = ana λ{ z → (z , z) }

map : {A B : Set} → (A → B) → Stream A → Stream B
map {A} {B} f = ana λ{ z → f (proj₁ (rest z)) , proj₂ (rest z) }
