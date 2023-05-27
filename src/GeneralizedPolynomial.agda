{-# OPTIONS --guardedness --no-positivity-check #-}

module GeneralizedPolynomial where

open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_)
open import Data.Product using (_×_; ∃-syntax; _,_)
open import Data.Nat
  using (ℕ; suc; _<_; _≤_; _⊔_; s≤s; z≤n; _≟_; _≤?_; _<?_;
        pred; _∸_)
open import Data.Nat.Properties
  using (≤-reflexive; ≤-trans; ≤-step; n≤1+n; ≤∧≢⇒<; ≤-pred;
        ≮⇒≥)
open import Data.Nat.Induction using (<-rec)

open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable
  using (True; toWitness; fromWitness)
open import Relation.Nullary.Negation
  using (contradiction)

open import Relation.Binary.PropositionalEquality
    using (refl; ≢-sym; _≡_)

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

infixl 6 _⊕ᵣ_
infixl 7 _⊗ᵣ_
infixl 6 _⊕_
infixl 7 _⊗_
infixr 8 μ_
infixr 8 ν_

data Polynomial : ℕ → Set₁ where
    I_   : (n : ℕ) → Polynomial (suc n)
    K_   : Set → Polynomial 0
    μ_   : {n : ℕ} → Polynomial (suc n) → Polynomial n
    ν_   : {n : ℕ} → Polynomial (suc n) → Polynomial n

    -- Shouldn't be used explicitly by users of the lib
    _⊕ᵣ_ : {n : ℕ} → Polynomial n → Polynomial n → Polynomial n
    _⊗ᵣ_ : {n : ℕ} → Polynomial n → Polynomial n → Polynomial n
    wk_  : {n m : ℕ} → Polynomial n → {True (n ≤? m)} → Polynomial m

-- Versions that infer weakening
_⊗_ : {n m : ℕ} → Polynomial n → Polynomial m → Polynomial (n ⊔ m)
L ⊗ R = (wk_ L {fromWitness n≤n⊔m}) ⊗ᵣ (wk_ R {fromWitness m≤n⊔m})

_⊕_ : {n m : ℕ} → Polynomial n → Polynomial m → Polynomial (n ⊔ m)
L ⊕ R = (wk_ L {fromWitness n≤n⊔m}) ⊕ᵣ (wk_ R {fromWitness m≤n⊔m})

data Context : ℕ → Set₁ where
  ∅      : Context 0
  _,_ : {n m : ℕ} → Context n → {True (m ≤? n)} → Polynomial m → Context (suc n)

-- I i means to lookup the i-th position in the context from the context
-- ∅ , a , b , c , d
--     3   2   1   0
lookup : {n : ℕ} → Context n → (m : ℕ) → {m < n} → ∃[ p ] Polynomial p × p < n
lookup (_,_ ctx {m≤n} X) 0       {p}     = _ , X , s≤s (toWitness m≤n)
lookup (ctx , _) (suc m) {s≤s p} with lookup ctx m {p}
... | p , X , p<n = p , X , ≤-step p<n

-- ∅ , a , b , c , d (4)
-- wk to 2
-- ∅ , a , b
-- A = I 0 ⊕ I 1
-- B = I 0
-- A ⊗ B
weaken-context : ∀ {n m : ℕ} → (m ≤ n) → Context n → Context m
weaken-context {0}     {0} z≤z ∅ = ∅
weaken-context {suc n} {m} m≤n ctx@(rest , _) with suc n ≟ m
... | yes refl = ctx
... | no  n≢m  = weaken-context (≤-pred (≤∧≢⇒< m≤n (≢-sym n≢m))) rest

mutual
  eval-impl : _
  eval-impl 0       rec (K x)           ctx = x
  eval-impl (suc n) rec (I m)           ctx with lookup ctx m {≤-reflexive refl}
  ... | p , X , p<n                         = rec p p<n X
                                                  (weaken-context (≤-trans (≤-pred p<n)
                                                                  (n≤1+n _)) ctx)
  eval-impl n rec (wk_ {f} {m} P {f≤m}) ctx with f ≟ m
  ... | yes refl                            = eval-impl _ rec P ctx
  ... | no  f≢m                             = rec f (≤∧≢⇒< (toWitness f≤m) f≢m) P
                                                           (weaken-context (toWitness f≤m) ctx)
  eval-impl n rec (μ P)                 ctx = LeastFixpoint P ctx
  eval-impl n rec (ν P)                 ctx = GreatestFixpoint P ctx
  eval-impl n rec (L ⊕ᵣ R)              ctx = eval-impl _ rec L ctx ⊎ eval-impl _ rec R ctx
  eval-impl n rec (L ⊗ᵣ R)              ctx = eval-impl _ rec L ctx × eval-impl _ rec R ctx

  lemmaₙ : {n : ℕ} → True (n ≤? n)
  lemmaₙ {n} = fromWitness (≤-reflexive refl)

  data LeastFixpoint {n : ℕ} (P : Polynomial (suc n)) (ctx : Context n) : Set where
    μ⟨_⟩ : eval P (_,_ ctx {lemmaₙ} (μ P)) → LeastFixpoint P ctx

  record GreatestFixpoint {n : ℕ} (P : Polynomial (suc n)) (ctx : Context n) : Set where
    coinductive
    field rest : eval P (_,_ ctx {lemmaₙ} (ν P))


  eval : {n : ℕ} → Polynomial n → Context n → Set
  eval {n} = <-rec _ eval-impl n

_[_/_] : {n g : ℕ} → Polynomial (suc n) → (i : ℕ) → {True (i ≤? n)} → Polynomial g → {True (g ≤? i)} → Polynomial n
_[_/_] {n} (I m)                 i {i<n} G {g≤n}                      with i ≟ m | i <? m
...                                        | yes i≡m  | i<?m          = wk_ G {fromWitness (≤-trans (toWitness g≤n)
                                                                                                      (toWitness i<n))}
_[_/_] {n} ((I suc m) )          i {i<n} G | no  i≢m  | yes i<m       = I m
...                                        | no  i≢m  | no  i≮m       = contradiction (≤∧≢⇒< (toWitness i<n) i≢m) i≮m
_[_/_] (μ P)                     i {i<n} G {g≤n}                      = μ (_[_/_] P (suc i) {fromWitness (s≤s (toWitness i<n))}
                                                                                                           G {fromWitness (≤-step (toWitness g≤n))})
_[_/_] (ν P)                     i {i<n} G {g≤n}                      = ν (_[_/_] P (suc i) {fromWitness (s≤s (toWitness i<n))}
                                                                                                           G {fromWitness (≤-step (toWitness g≤n))})
_[_/_] (L ⊕ᵣ R)                  i {i<n} G {g≤n}                      = (_[_/_] L i {i<n} G {g≤n}) ⊕ᵣ (_[_/_] R i {i<n} G {g≤n})
_[_/_] (L ⊗ᵣ R)                  i {i<n} G {g≤n}                      = (_[_/_] L i {i<n} G {g≤n}) ⊗ᵣ (_[_/_] R i {i<n} G {g≤n})
_[_/_] (wk_ {m}     {n} P {m≤n}) i {i<n} G {g≤n}                      with i <? m
_[_/_] (wk_ {0}     {n} P {m≤n}) i {i<n} G {g≤n} | yes i<m            = wk_ P
_[_/_] (wk_ {suc m} {n} P {m≤n}) i {i<n} G {g≤n} | yes i<m            = wk_ (_[_/_] P i {fromWitness (≤-pred i<m)}
                                                                                        G {g≤n})
                                                                              {fromWitness (≤-pred (toWitness m≤n))}
...                                              | no  i≮m            = wk_ P {fromWitness (≤-trans (≮⇒≥ i≮m) (toWitness i<n ))}

-- g ≤ n₁        (g≤n)
-- suc suc i ≤ m (i<m)
-- suc i ≤ n     (i<n)
-- m ≤ n₁        (m<n)

⟦_⟧ : {n m : ℕ} → {n≤m : True (n ≤? m)} → Polynomial n → Context m → Set
⟦_⟧ {_} {_} {n≤m} F ctx = eval F (weaken-context (toWitness n≤m) ctx)

⟦_⟧₁ : Polynomial 1 → Set → Set
⟦ P ⟧₁ X = ⟦ P ⟧ (∅ , K X)

⟦_⟧₀ : Polynomial 0 → Set
⟦ P ⟧₀ = ⟦ P ⟧ ∅

