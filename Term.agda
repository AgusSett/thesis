module Term where

open import Type
open import IsoType
open import Relation.Binary.PropositionalEquality renaming (_≡_ to _≋_) hiding (sym)
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

  [_]≡_ : ∀ {Γ A B} → A ≡ B → Γ ⊢ A → Γ ⊢ B -- (1) This rule constructs "unstable" terms

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


data Neutral : ∀ {Γ A} → Γ ⊢ A → Set
data Normal  : ∀ {Γ A} → Γ ⊢ A → Set

data Neutral where

  `_  : ∀ {Γ A} (x : Γ ∋ A)
      -------------
    → Neutral (` x)

  _·_  : ∀ {Γ A B} {L : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
    → Neutral L
    → Normal M
      ---------------
    → Neutral (L · M)
  
  proj : ∀ {Γ A B C p} {L : Γ ⊢ A × B}
    → Neutral L
      ---------------
    → Neutral (proj C {p} L)
  
  [_]≡_ : ∀ {Γ A B} {N : Γ ⊢ A}
    → (iso : A ≡ B)
    → Normal N
      ------------------
    → Neutral ([ iso ]≡ N)

data Normal where

  ^_ : ∀ {Γ A} {M : Γ ⊢ A}
    → Neutral M
      ---------
    → Normal M

  N-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B}
      ------------
    → Normal (ƛ N)
  
  ⟨_,_⟩ : ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
    → Normal V
    → Normal W
      ----------------
    → Normal ⟨ V , W ⟩
  
  N-⋆ : ∀ {Γ}
      ---------------------------
    → Normal (⋆ {Γ})
