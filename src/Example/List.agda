module Example.List where

open import Polynomial using (Polynomial)
open import FAlgebra using (μ_; cata)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)

open Polynomial.Polynomial
open μ_

List : Set → Set
List A = μ (ListF A)
    where
        ListF : Set → Polynomial
        ListF A = K ⊤ ⊕ K A ⊗ I

pattern [] = inj₁ tt
pattern _∷_ x xs = inj₂ (x , xs)

fold : {A B : Set} → (A → B → B) → B → List A → B
fold _*_ z = cata λ{ []       → z
                   ; (x ∷ xs) → x * xs }

map : {A B : Set} → (A → B) → List A → List B
map f = cata λ{ []       → μ⟨ [] ⟩
              ; (x ∷ xs) → μ⟨ f x ∷ xs ⟩ }
