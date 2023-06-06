{-# OPTIONS --guardedness --allow-unsolved-metas #-}

module GeneralizedPolynomial where

open import Data.Empty using (⊥-elim; ⊥)
open import Data.Unit using (⊤)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product
  using (_×_; ∃-syntax; _,_; proj₁; proj₂)
open import Data.Nat
  using (ℕ; suc; _<_; _≤_; _⊔_; s≤s; z≤n; _≟_; _≤?_; _<?_;
        pred; _∸_; _+_)
open import Data.Nat.Properties
  using (≤-reflexive; ≤-trans; ≤-step; n≤1+n; ≤∧≢⇒<; ≤-pred;
        ≮⇒≥; m≤m⊔n; m≤n⊔m; m<n⇒m≤1+n; m≤n⇒m<n∨m≡n)
open import Data.Nat.Induction using (<-rec)

open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Nullary.Decidable
  using (True; toWitness; fromWitness)
open import Relation.Nullary.Negation
  using (contradiction)

open import relation.binary.propositionalequality
    using (refl; ≢-sym; _≡_)

infixl 6 _⊕ᵣ_
infixl 7 _⊗ᵣ_
infixl 6 _⊕_
infixl 7 _⊗_
infixr 8 μ_
infixr 8 ν_
infixr 8 wk_
infixl 8 _[_]

private module ℕextra where
  m≤n⇒m≤1+n : ∀ {m n} → m ≤ n → m ≤ 1 + n
  m≤n⇒m≤1+n z≤n       = z≤n
  m≤n⇒m≤1+n (s≤s m≤n) = s≤s (m≤n⇒m≤1+n m≤n)

  lemma : (n m : ℕ) → (n ≤ suc m) → ¬ (n ≡ suc m) → n ≤ m
  lemma m n n≤m n≢m with m≤n⇒m<n∨m≡n n≤m
  ... | inj₁ n<m = ≤-pred n<m
  ... | inj₂ n≡m = contradiction n≡m n≢m

open ℕextra

data Polynomial : ℕ → Set₁ where
    I_   : (n : ℕ) → Polynomial (suc n)
    K_   : Set → Polynomial 0
    μ_   : {n : ℕ} → Polynomial (suc n) → Polynomial n
    ν_   : {n : ℕ} → Polynomial (suc n) → Polynomial n

    -- Shouldn't be used explicitly by users of the lib
    _⊕ᵣ_ : {n : ℕ} → Polynomial n → Polynomial n → Polynomial n
    _⊗ᵣ_ : {n : ℕ} → Polynomial n → Polynomial n → Polynomial n
    wkᵣ_  : {n : ℕ} → Polynomial n → Polynomial (suc n)
    _[_]  : {n : ℕ} → Polynomial (suc n) → Polynomial n → Polynomial n

-- Versions that infer weakening
wkᵢ : {n m : ℕ} → Polynomial n → (n ≤ m) → Polynomial m
wkᵢ {0}     {0}     P n≤m = P
wkᵢ {n}     {suc m} P n≤m with n ≟ suc m
... | yes refl = P
... | no n≢m   = wkᵣ (wkᵢ {n} {m} P (lemma n m n≤m n≢m))

wk_ : {n m : ℕ} → Polynomial n → {True (n ≤? m)} → Polynomial m
wk_ P {n≤m} = wkᵢ P (toWitness n≤m)

_⊗_ : {n m : ℕ} → Polynomial n → Polynomial m → Polynomial (n ⊔ m)
L ⊗ R = (wkᵢ L (m≤m⊔n _ _)) ⊗ᵣ (wkᵢ R (m≤n⊔m _ _))

_⊕_ : {n m : ℕ} → Polynomial n → Polynomial m → Polynomial (n ⊔ m)
L ⊕ R = (wkᵢ L (m≤m⊔n _ _)) ⊕ᵣ (wkᵢ R (m≤n⊔m _ _))


𝟘 : Polynomial 0
𝟘 = K ⊥

𝟙 : Polynomial 0
𝟙 = K ⊤

infixl 3 _,⟨_⟩_
data Context : ℕ → Set₁ where
  ∅      : Context 0
  _,⟨_⟩_ : {n m : ℕ} → Context n → (m ≤ n) → Polynomial m → Context (suc n)

infixl 3 _∙_
_∙_ : {n m : ℕ} → Context n → {True (m ≤? n)} → Polynomial m → Context (suc n)
_∙_ ctx {m≤n} P = ctx ,⟨ toWitness m≤n ⟩ P

lookup : {n : ℕ} → Context n → (m : ℕ) → (m < n) → ∃[ p ] Polynomial p × p < n
lookup (ctx ,⟨ m≤n ⟩ X) 0       p                     = _ , X , s≤s m≤n
lookup (ctx ,⟨ _   ⟩ _) (suc m) (s≤s p) with lookup ctx m p
...                                     | p , X , p<n = p , X , ≤-step p<n

mutual
  {-# TERMINATING #-}
  eval : {n m : ℕ} → (n ≤ m) → Polynomial n → Context m → Set
  eval m≤n (I k)     ctx with lookup ctx k m≤n
  ...                    | p , X , s≤s p<n = eval (≤-step p<n) X ctx
  eval n≤m (K x)     ctx                   = x
  eval n≤m (L ⊗ᵣ R)  ctx                   = eval n≤m L ctx × eval n≤m R ctx
  eval n≤m (L ⊕ᵣ R)  ctx                   = eval n≤m L ctx ⊎ eval n≤m R ctx
  eval n≤m (μ P)     ctx                   = LeastFixpoint n≤m P ctx
  eval n≤m (ν P)     ctx                   = GreatestFixpoint n≤m P ctx
  eval n≤m (wkᵣ P)   ctx                   = eval (≤-pred (m≤n⇒m≤1+n n≤m)) P ctx
  eval n≤m (F [ G ]) ctx                   = eval (s≤s n≤m) F (ctx ,⟨ n≤m ⟩ G)

  data LeastFixpoint {n m : ℕ}
    (n≤m : n ≤ m) (P : Polynomial (suc n)) (ctx : Context m) : Set where
    μ⟨_⟩ : eval (s≤s n≤m) P (ctx ,⟨ n≤m ⟩ μ P) → LeastFixpoint n≤m P ctx

  record GreatestFixpoint {n m : ℕ}
    (n≤m : n ≤ m) (P : Polynomial (suc n)) (ctx : Context m) : Set where
    coinductive
    field rest : eval (s≤s n≤m) P (ctx ,⟨ n≤m ⟩ ν P)


⟦_⟧ : {n m : ℕ} → {n≤m : True (n ≤? m)} → Polynomial n → Context m → Set
⟦_⟧ {_} {_} {n≤m} F ctx = eval (toWitness n≤m) F ctx

⟦_⟧₁ : Polynomial 1 → Set → Set
⟦ P ⟧₁ X = ⟦ P ⟧ (∅ ∙ K X)

⟦_⟧₀ : Polynomial 0 → Set
⟦ P ⟧₀ = ⟦ P ⟧ ∅
