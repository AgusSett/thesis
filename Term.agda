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

  π : ∀ {Γ A B}
    → (C : Type)
    → {proof : (C ≋ A) ⊎ (C ≋ B)}
    → Γ ⊢ A × B 
      -----------
    → Γ ⊢ C

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


data ⇓ : ∀ {Γ A} → Γ ⊢ A → Set
data ⇑ : ∀ {Γ A} → Γ ⊢ A → Set

-- Neutral M = Normal M × ¬ Value M
data ⇓ where

  `_  : ∀ {Γ A} (x : Γ ∋ A)
      -------------
    → ⇓ (` x)

  _·_  : ∀ {Γ A B} {L : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
    → ⇓ L → ⇑ M
      ---------------
    → ⇓ (L · M)
  
  π : ∀ {Γ A B C p} {L : Γ ⊢ A × B}
    → ⇓ L
      ---------------
    → ⇓ (π C {p} L)
  
  [_]≡_ : ∀ {Γ A B} {N : Γ ⊢ A}
    → (iso : A ≡ B)
    → ⇓ N
      ------------------
    → ⇓ ([ iso ]≡ N)

-- Normal M = ∀ {N} → ¬ (M ⇝ N)
data ⇑ where

  ^_ : ∀ {Γ A} {M : Γ ⊢ A}
    → ⇓ M
      ---------
    → ⇑ M

  N-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B}
    → {⇑ N}
      ------------
    → ⇑ (ƛ N)
  
  ⟨_,_⟩ : ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
    → ⇑ V
    → ⇑ W
      ----------------
    → ⇑ ⟨ V , W ⟩
  
  N-⋆ : ∀ {Γ}
      ---------------------------
    → ⇑ (⋆ {Γ})

open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_)

closed→¬⇓ : ∀ {A} → (N : ∅ ⊢ A) → ¬ (⇓ N)
closed→¬⇓ ⋆          = λ ()
closed→¬⇓ (ƛ _)      = λ ()
closed→¬⇓ ⟨ _ , _ ⟩  = λ ()
closed→¬⇓ ([ _ ]≡ x) = λ { ([ _ ]≡ ⇓x) → closed→¬⇓ x ⇓x }
closed→¬⇓ (x · _)    = λ { (⇓x · _) → closed→¬⇓ x ⇓x }
closed→¬⇓ (π _ x)    = λ { (π ⇓x) → closed→¬⇓ x ⇓x }

closed⇑→Value : ∀ {A} → {N : ∅ ⊢ A} → ⇑ N → Value N
closed⇑→Value N-⋆            = V-⋆
closed⇑→Value N-ƛ            = V-ƛ
closed⇑→Value ⟨ a , b ⟩      = V-⟨ closed⇑→Value a , closed⇑→Value b ⟩
closed⇑→Value {N = N} (^ ⇓N) = ⊥-elim (closed→¬⇓ N ⇓N)