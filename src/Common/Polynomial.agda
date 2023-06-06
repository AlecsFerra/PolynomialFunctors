module Common.Polynomial where

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
    using (_≡_; refl)
open import Function using (_∘_; id)


infixl 6 _⊕_
infixl 7 _⊗_

data Polynomial : Set₁ where
    I    : Polynomial
    K_   : Set → Polynomial
    _⊗_  : Polynomial → Polynomial → Polynomial
    _⊕_  : Polynomial → Polynomial → Polynomial


⟦_⟧ : Polynomial → Set → Set
⟦ I      ⟧ x = x
⟦ K k    ⟧ x = k
⟦ L ⊗ R ⟧ x = ⟦ L ⟧ x × ⟦ R ⟧ x
⟦ L ⊕ R ⟧ x = ⟦ L ⟧ x ⊎ ⟦ R ⟧ x

_⊙_ : Polynomial → Polynomial → Polynomial
I       ⊙ G = G
(K k)   ⊙ G = K k
(L ⊗ R) ⊙ G = L ⊙ G ⊗ R ⊙ G
(L ⊕ R) ⊙ G = L ⊙ G ⊕ R ⊙ G

⟦F⊙G⟧≡⟦F⟧∙⟦G⟧ : (F G : Polynomial) → ⟦ F ⊙ G ⟧ ≡ ⟦ F ⟧ ∘ ⟦ G ⟧
⟦F⊙G⟧≡⟦F⟧∙⟦G⟧ I        G = refl
⟦F⊙G⟧≡⟦F⟧∙⟦G⟧ (K k)    G = refl
⟦F⊙G⟧≡⟦F⟧∙⟦G⟧ (L ⊗ R) G rewrite ⟦F⊙G⟧≡⟦F⟧∙⟦G⟧ L G
                          rewrite ⟦F⊙G⟧≡⟦F⟧∙⟦G⟧ R G
                          = refl
⟦F⊙G⟧≡⟦F⟧∙⟦G⟧ (L ⊕ R) G rewrite ⟦F⊙G⟧≡⟦F⟧∙⟦G⟧ L G
                          rewrite ⟦F⊙G⟧≡⟦F⟧∙⟦G⟧ R G
                          = refl

map : (F : Polynomial) → {X Y : Set} → (X → Y) → ⟦ F ⟧ X → ⟦ F ⟧ Y
map I        f x         = f x
map (K k)    f x         = x
map (L ⊗ R) f (xₗ , xᵣ) = map L f xₗ , map R f xᵣ
map (L ⊕ R) f (inj₁ xₗ) = inj₁ (map L f xₗ)
map (L ⊕ R) f (inj₂ xᵣ) = inj₂ (map R f xᵣ)
