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
    → Value V
    → M ↪ M'
      ---------------
    → V · M ↪ V · M'

  β-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B} {V : Γ ⊢ A}
    → Value V
      --------------------
    → (ƛ N) · V ↪ N [ V ]

  -- products

  ξ-⟨,⟩₁ : ∀ {Γ A B} {M M' : Γ ⊢ A} {N : Γ ⊢ B}
    → M ↪ M'
      -------------------------
    → ⟨ M , N ⟩ ↪ ⟨ M' , N ⟩

  ξ-⟨,⟩₂ : ∀ {Γ A B} {V : Γ ⊢ A} {N N' : Γ ⊢ B}
    → Value V
    → N ↪ N'
      -------------------------
    → ⟨ V , N ⟩ ↪ ⟨ V , N' ⟩

  ξ-proj : ∀ {Γ A B C p} {L L' : Γ ⊢ A × B}
    → L ↪ L'
      ---------------------
    → proj C {p} L ↪ proj C {p} L'

  β-proj₁ : ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
    → Value V
    → Value W
      ----------------------
    → proj A {inj₁ refl} ⟨ V , W ⟩ ↪ V

  β-proj₂ : ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
    → Value V
    → Value W
      ----------------------
    → proj B {inj₂ refl} ⟨ V , W ⟩ ↪ W

  ξ-≡ : ∀ {Γ A B} {N : Γ ⊢ A} {N' : Γ ⊢ A} {iso : A ≡ B}
    → N ↪ N'
    → [ iso ]≡ N ↪ [ iso ]≡ N'

data Progress {Γ A} (M : Γ ⊢ A) : Set where

  step : ∀ {N : Γ ⊢ A}
    → M ↪ N
      ----------
    → Progress M

  done :
      Value M
      ----------
    → Progress M
  
  nothing : Progress M

progress : ∀ {A}
  → (M : ∅ ⊢ A)
    -----------
  → Progress M
progress (` ())
progress ⋆                                = done V-⋆
progress (ƛ N)                            = done V-ƛ
progress (L · M) with progress L
...    | nothing                          = nothing
...    | step L↪L'                        = step (ξ-·₁ L↪L')
...    | done V-ƛ with progress M
...        | nothing                      = nothing
...        | step M↪M'                    = step (ξ-·₂ V-ƛ M↪M')
...        | done VM                      = step (β-ƛ VM)
progress ⟨ M , N ⟩ with progress M
...    | nothing                          = nothing
...    | step M↪M'                        = step (ξ-⟨,⟩₁ M↪M')
...    | done VM with progress N
...        | nothing                      = nothing
...        | step N↪N'                    = step (ξ-⟨,⟩₂ VM N↪N')
...        | done VN                      = done (V-⟨ VM , VN ⟩)
progress (proj C {p} L) with progress L
...    | nothing                          = nothing
...    | step L↪L'                        = step (ξ-proj L↪L')
progress (proj C {inj₁ refl} L) | done V-⟨ VM , VN ⟩ = step (β-proj₁ VM VN)
progress (proj C {inj₂ refl} L) | done V-⟨ VM , VN ⟩ = step (β-proj₂ VM VN)
progress ([ iso ]≡ N) with progress N
...    | nothing                          = nothing       
...    | step N↪N'                        = step (ξ-≡ N↪N')
...    | done V                           = nothing -- (2) Can't do anything when we have a value inside [_]≡_
 