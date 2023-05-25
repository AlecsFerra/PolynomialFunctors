{-# OPTIONS --guardedness #-}

module GeneralizedPolynomial where

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
    using (_≡_; refl; cong)
open import Function using (_∘_; id)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)

infixl 6 _⊕_
infixl 7 _⊗_
infixl 8 _⊙_

data Polynomial : Set₁ where
    I    : Polynomial
    K    : Set → Polynomial
    _⊗_ : Polynomial → Polynomial → Polynomial
    _⊕_ : Polynomial → Polynomial → Polynomial
    μ_   : Polynomial → Polynomial
    ν_   : Polynomial → Polynomial

𝟙 : Polynomial
𝟙 = K ⊤

𝟘 : Polynomial
𝟘 = K ⊥

_⊙_ : Polynomial → Polynomial → Polynomial
I        ⊙ G = G
K x      ⊙ G = K x
(L ⊗ R) ⊙ G = L ⊙ G ⊗ R ⊙ G
(L ⊕ R) ⊙ G = L ⊙ G ⊕ R ⊙ G
(μ F)    ⊙ G = μ F
(ν F)    ⊙ G = ν F


-- Fix F
-- F ⊙ F ⊙ ⋯ ⊙ F ⊙ F x
-- F ⊙ F ⊙ ⋯ ⊙ F (F x)
-- ⋯
-- F (F ⋯ (F (F x)) ⋯)

mutual
    ⟦_⟧ : Polynomial → Set → Set
    ⟦ I      ⟧ x = x
    ⟦ K k    ⟧ x = k
    ⟦ L ⊗ R ⟧ x = ⟦ L ⟧ x × ⟦ R ⟧ x
    ⟦ L ⊕ R ⟧ x = ⟦ L ⟧ x ⊎ ⟦ R ⟧ x
    ⟦ μ F    ⟧ x = LeastFixpoint F
    ⟦ ν F    ⟧ x = GreatestFixpoint F

    data LeastFixpoint (F : Polynomial) : Set where
        μ⟨_⟩ : ⟦ F ⟧ (LeastFixpoint F)  → LeastFixpoint F

    record GreatestFixpoint (F : Polynomial) : Set where
        coinductive
        field rest : ⟦ F ⟧ (GreatestFixpoint F)


⟦F⊙G⟧≡⟦F⟧∙⟦G⟧ : (F G : Polynomial) → ⟦ F ⊙ G ⟧ ≡ ⟦ F ⟧ ∘ ⟦ G ⟧
⟦F⊙G⟧≡⟦F⟧∙⟦G⟧ I        G = refl
⟦F⊙G⟧≡⟦F⟧∙⟦G⟧ (K k)    G = refl
⟦F⊙G⟧≡⟦F⟧∙⟦G⟧ (L ⊗ R) G rewrite ⟦F⊙G⟧≡⟦F⟧∙⟦G⟧ L G
                          rewrite ⟦F⊙G⟧≡⟦F⟧∙⟦G⟧ R G
                          = refl
⟦F⊙G⟧≡⟦F⟧∙⟦G⟧ (L ⊕ R) G rewrite ⟦F⊙G⟧≡⟦F⟧∙⟦G⟧ L G
                          rewrite ⟦F⊙G⟧≡⟦F⟧∙⟦G⟧ R G
                          = refl
⟦F⊙G⟧≡⟦F⟧∙⟦G⟧ (μ F)    G = refl
⟦F⊙G⟧≡⟦F⟧∙⟦G⟧ (ν F)    G = refl

infixl 10 ∂_

∂_ : Polynomial → Polynomial
∂ I        = 𝟙
∂ K k      = 𝟘
∂ (L ⊗ R) = ∂ L ⊗ R ⊕ L ⊗ ∂ R
∂ (L ⊕ R) = ∂ L ⊕ ∂ R
∂ (μ P)    = inner ⊗ {!   !}
    where inner = ∂ P ⊙ μ P
∂ (ν P)    = {!   !}

private module List where

    ListF : Set → Polynomial
    ListF A = μ (𝟙 ⊕ K A ⊗ I)

    List : Set → Set
    List A = ⟦ ListF A ⟧ ⊤

    infixr 3 _∷_
    pattern []       = μ⟨ inj₁ tt ⟩
    pattern _∷_ x xs = μ⟨ inj₂ (x , xs) ⟩

    map : ∀ {A B} → (A → B) → List A → List B
    map f []       = []
    map f (x ∷ xs) = f x ∷ map f xs

    open import Data.Nat

    _ : List ℕ
    _ = 2 ∷ 1 ∷ 0 ∷ []


    ListZipper : Set → Set
    ListZipper A = ⟦ ∂ (ListF A) ⟧ ⊥

    t : ∀ {A} → ListZipper A → A
    t x = {!   !}
