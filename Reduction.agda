module Reduction where

open import Term
open import Type
open import IsoType hiding (sym)
open import Subs
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (cong₂; sym; refl)

infixr 2 _↪_

data _↪_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  -- functions

  ξ-·₁ : ∀ {Γ A B} {L L' : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
    → L ↪ L'
      ---------------
    → L · M ↪ L' · M

  ξ-·₂ : ∀ {Γ A B} {V : Γ ⊢ A ⇒ B} {M M' : Γ ⊢ A}
    → M ↪ M'
      ---------------
    → V · M ↪ V · M'

  β-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B} {V : Γ ⊢ A}
      --------------------
    → (ƛ N) · V ↪ N [ V ]
  
  ζ : ∀ {Γ A B} {L L' : Γ , B ⊢ A}
    → L ↪ L'
    → ƛ L ↪ ƛ L'

  -- products

  ξ-⟨,⟩₁ : ∀ {Γ A B} {M M' : Γ ⊢ A} {N : Γ ⊢ B}
    → M ↪ M'
      -----------------------
    → ⟨ M , N ⟩ ↪ ⟨ M' , N ⟩

  ξ-⟨,⟩₂ : ∀ {Γ A B} {V : Γ ⊢ A} {N N' : Γ ⊢ B}
    → N ↪ N'
      -----------------------
    → ⟨ V , N ⟩ ↪ ⟨ V , N' ⟩

  ξ-π : ∀ {Γ A B C p} {L L' : Γ ⊢ A × B}
    → L ↪ L'
      ---------------------
    → π C {p} L ↪ π C {p} L'

  β-π₁ : ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
      ------------------------------
    → π A {inj₁ refl} ⟨ V , W ⟩ ↪ V

  β-π₂ : ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
      ------------------------------
    → π B {inj₂ refl} ⟨ V , W ⟩ ↪ W

  -- iso

  ξ-≡ : ∀ {Γ A B} {N : Γ ⊢ A} {N' : Γ ⊢ A} {iso : A ≡ B}
    → N ↪ N'
    → [ iso ]≡ N ↪ [ iso ]≡ N'


↪[] : ∀ {Γ Δ A}{t t' : Γ ⊢ A}{σ : Subst Γ Δ} → t ↪ t' → subst σ t ↪ subst σ t'
↪[] (ξ-·₁ step) = ξ-·₁ (↪[] step)
↪[] (ξ-·₂ step) = ξ-·₂ (↪[] step)
↪[] {σ = σ} (β-ƛ {N = N} {V = V})
  rewrite (sym (subst-commute {Σ = ∅} {N = N} {M = V} {σ = σ}))
    = β-ƛ
↪[] (ζ step) = ζ (↪[] step)
↪[] (ξ-⟨,⟩₁ step) = ξ-⟨,⟩₁ (↪[] step)
↪[] (ξ-⟨,⟩₂ step) = ξ-⟨,⟩₂ (↪[] step)
↪[] (ξ-π step) = ξ-π (↪[] step)
↪[] β-π₁ = β-π₁
↪[] β-π₂ = β-π₂
↪[] (ξ-≡ step) = ξ-≡ (↪[] step)
 