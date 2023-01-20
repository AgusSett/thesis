module Term where

open import Type
open import IsoType
open import Relation.Binary.PropositionalEquality renaming (_≡_ to _≋_)
open import Data.Sum

infix  4 _∋_
infixl 5 _,_
infix  9 S_

infix  4 _⊢_

infix  5 ƛ_
infixl 7 _·_
infix  9 `_


data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context

data _∋_ : Context → Type → Set where

  Z : ∀ {Γ A}
      ---------
    → Γ , A ∋ A

  S_ : ∀ {Γ A B}
    → Γ ∋ B
      ---------
    → Γ , A ∋ B

data _⊢_ : Context → Type → Set where

  -- variables

  `_ : ∀ {Γ A}
    → Γ ∋ A
      -----
    → Γ ⊢ A
  
  ⋆ : ∀ {Γ} → Γ ⊢ ⊤

  -- ≡

  [_]≡_ : ∀ {Γ A B} → A ≡ B → Γ ⊢ A → Γ ⊢ B -- (1) This rule constructs "wrong" terms

  -- functions

  ƛ_  :  ∀ {Γ A B}
    → Γ , A ⊢ B
      ---------
    → Γ ⊢ A ⇒ B

  _·_ : ∀ {Γ A B}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
      ---------
    → Γ ⊢ B

  -- products

  ⟨_,_⟩ : ∀ {Γ A B}
    → Γ ⊢ A
    → Γ ⊢ B
      -----------
    → Γ ⊢ A × B

  proj : ∀ {Γ A B}
    → (C : Type)
    → {proof : (C ≋ A) ⊎ (C ≋ B)}
    → Γ ⊢ A × B 
      -----------
    → Γ ⊢ C

{-
π : ∀ {Γ A B} → (C : Type) → {proof : True (C ≟ A) ⊎ True (C ≟ B)} → Γ ⊢ A × B 
    → Γ ⊢ C
π C {inj₁ x} A×B = proj C (inj₁ (toWitness x)) A×B
π C {inj₂ x} A×B = proj C (inj₂ (toWitness x)) A×B
-}

data Value : ∀ {Γ A} → Γ ⊢ A → Set where

  -- functions

  V-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B}
      ---------------------------
    → Value (ƛ N)
  
  -- unit

  V-⋆ : ∀ {Γ}
      ---------------------------
    → Value (⋆ {Γ})

  -- products

  V-⟨_,_⟩ : ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
    → Value V
    → Value W
      ----------------
    → Value ⟨ V , W ⟩
