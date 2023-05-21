module Reduction where

open import Term
open import Type
open import IsoType
open import Subs
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (refl)

infixr 2 _↪_

data _↪_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where
  -- functions

  ξ-·₁ : ∀ {Γ A B} {L L' : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
    → L ↪ L'
      ---------------
    → L · M ↪ L' · M

  ξ-·₂ : ∀ {Γ A B} {V : Γ ⊢ A ⇒ B} {M M' : Γ ⊢ A}
--    → Value V
    → M ↪ M'
      ---------------
    → V · M ↪ V · M'

  β-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B} {V : Γ ⊢ A}
--    → Value V
      --------------------
    → (ƛ N) · V ↪ N [ V ]

  -- products

  ξ-⟨,⟩₁ : ∀ {Γ A B} {M M' : Γ ⊢ A} {N : Γ ⊢ B}
    → M ↪ M'
      -------------------------
    → ⟨ M , N ⟩ ↪ ⟨ M' , N ⟩

  ξ-⟨,⟩₂ : ∀ {Γ A B} {V : Γ ⊢ A} {N N' : Γ ⊢ B}
--    → Value V
    → N ↪ N'
      -------------------------
    → ⟨ V , N ⟩ ↪ ⟨ V , N' ⟩

  ξ-proj : ∀ {Γ A B C p} {L L' : Γ ⊢ A × B}
    → L ↪ L'
      ---------------------
    → proj C {p} L ↪ proj C {p} L'

  β-proj₁ : ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
--    → Value V
--    → Value W
      ----------------------
    → proj A {inj₁ refl} ⟨ V , W ⟩ ↪ V

  β-proj₂ : ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
--    → Value V
--    → Value W
      ----------------------
    → proj B {inj₂ refl} ⟨ V , W ⟩ ↪ W

  ξ-≡ : ∀ {Γ A B} {N : Γ ⊢ A} {N' : Γ ⊢ A} {iso : A ≡ B}
    → N ↪ N'
    → [ iso ]≡ N ↪ [ iso ]≡ N'
  
  ζ : ∀ {Γ A B} {L L' : Γ , B ⊢ A}
    → L ↪ L'
    → ƛ L ↪ ƛ L'

