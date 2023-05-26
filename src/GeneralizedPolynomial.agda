{-# OPTIONS --guardedness #-}

module GeneralizedPolynomial where

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; ∃-syntax; _,_)
open import Relation.Binary.PropositionalEquality
    using (_≡_; refl; ≢-sym)
open import Data.Nat
  using (ℕ; suc; _<_; _≤_; _⊔_; _+_; s≤s; z≤n; _≟_; _≤?_)
open import Data.Nat.Properties
  using (≤-reflexive; ≤-trans; ≤-step; n≤1+n; ≤∧≢⇒<; ≤-pred)
open import Relation.Nullary using (¬_; yes; no)

private module ℕExtra where
  n≤n⊔m : {n m : ℕ} → n ≤ n ⊔ m
  n≤n⊔m {0}     {m}     = z≤n
  n≤n⊔m {suc n} {0}     = ≤-reflexive refl
  n≤n⊔m {suc n} {suc m} = s≤s n≤n⊔m

  m≤n⊔m : {n m : ℕ} → m ≤ n ⊔ m
  m≤n⊔m {0}     {m}     = ≤-reflexive refl
  m≤n⊔m {suc n} {0}     = z≤n
  m≤n⊔m {suc n} {suc m} = s≤s m≤n⊔m


open ℕExtra

infixl 6 _⊕_
infixl 7 _⊗_

data Polynomial : ℕ → Set₁ where
    I_  : {n : ℕ} → (m : ℕ) → {m < n} → Polynomial n
    K_  : {n : ℕ} → Set → Polynomial n
    _⊗_ : {n m : ℕ} → Polynomial n → Polynomial m → Polynomial (n ⊔ m)
    _⊕_ : {n m : ℕ} → Polynomial n → Polynomial m → Polynomial (n ⊔ m)
    μ_  : {n : ℕ} → Polynomial (suc n) → Polynomial n
    ν_  : {n : ℕ} → Polynomial (suc n) → Polynomial n


data Context : ℕ → Set₁ where
  ∅   : Context 0
  _,[_]_ : {n m : ℕ} → Context n → (m ≤ n) → Polynomial m → Context (suc n)

-- I i means to lookup the i-th position in the context from the context
-- ∅ , a , b , c , d
--     3   2   1   0
lookup : {n : ℕ} → Context n → (m : ℕ) → {m < n} → ∃[ p ] Polynomial p × p < n
lookup (ctx ,[ m≤n ] X) 0       {p}     = _ , X , s≤s m≤n
lookup (ctx ,[ _   ] _) (suc m) {s≤s p} with lookup ctx m {p}
... | p , X , p<n = p , X , ≤-step p<n

-- ∅ , a , b , c , d (4)
-- wk to 2
-- ∅ , a , b
-- A = I 0 ⊕ I 1
-- B = I 0
-- A ⊗ B
weaken : ∀ {n m : ℕ} → (m ≤ n) → Context n → Context m
weaken {0} {0} z≤z ∅ = ∅
weaken {n} {m} m≤n ctx@(rest ,[ _ ] _) with n ≟ m
... | yes refl = ctx
... | no  n≢m  = weaken (≤-pred (≤∧≢⇒< m≤n (≢-sym n≢m))) rest

mutual
  eval : {n : ℕ} → Polynomial n → Context n → Set
  eval ((I m) {m<n}) ctx with lookup ctx m {m<n}
  ... | p , X , s≤s p<n = eval X (weaken (≤-trans p<n (n≤1+n _)) ctx)
  eval (K x)         ctx = x
  eval (L ⊗ R)       ctx = eval L (weaken n≤n⊔m ctx) × eval R (weaken m≤n⊔m ctx)
  eval (L ⊕ R)       ctx = eval L (weaken n≤n⊔m ctx) ⊎ eval R (weaken m≤n⊔m ctx)
  eval (μ P)         ctx = LeastFixpoint P ctx
  eval (ν P)         ctx = GreatestFixpoint P ctx

  data LeastFixpoint {n : ℕ} (P : Polynomial (suc n)) (ctx : Context n) : Set where
    μ⟨_⟩ : eval P (ctx ,[ ≤-reflexive refl ] (μ P)) → LeastFixpoint P ctx

  record GreatestFixpoint {n : ℕ} (P : Polynomial (suc n)) (ctx : Context n) : Set where
    coinductive
    field rest : eval P (ctx ,[ ≤-reflexive refl ] (ν P))
