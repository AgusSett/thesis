module Eval where

open import Term
open import IsoType
open import IsoTerm
open import Reduction

infix  2 _⇝_
infix  1 begin_
infixr 2 _⇄⟨_⟩_
infixr 2 _↪⟨_⟩_
infix  3 _∎

data _⇝_ {Γ A} : (Γ ⊢ A) → (Γ ⊢ A) → Set where

  _∎ : (M : Γ ⊢ A)
      ------
    → M ⇝ M
  
  _⇄⟨_⟩_ : (L : Γ ⊢ A) {M N : Γ ⊢ A}
    → L ⇄ M
    → M ⇝ N
      ------
    → L ⇝ N

  _↪⟨_⟩_ : (L : Γ ⊢ A) {M N : Γ ⊢ A}
    → L ↪ M
    → M ⇝ N
      ------
    → L ⇝ N


begin_ : ∀ {Γ A} {M N : Γ ⊢ A}
  → M ⇝ N
    ------
  → M ⇝ N
begin M⇝N = M⇝N


data Steps {A} : ∅ ⊢ A → Set where

  steps : {L N : ∅ ⊢ A}
    → L ⇝ N
      ----------
    → Steps L

open import Data.Nat using (ℕ; zero; suc)

eval : ∀ {A}
  → ℕ -- Agda need this argument for the termination check, maybe we could use the measure of the type here
  → (L : ∅ ⊢ A)
  → Steps L
eval zero L                     = steps (L ∎)
eval (suc n) L with symmetric L
...            | nothing with progress L
eval (suc n) L | nothing | step {M} L↪M with eval n M
...            | steps M⇝N                  = steps (L ↪⟨ L↪M ⟩ M⇝N)
eval (suc n) L | nothing | done VL = steps (L ∎)
eval (suc n) L | nothing | nothing = steps (L ∎)
eval (suc n) L | step {M} L⇄M with eval n M
...            | steps M⇝N                  = steps (L ⇄⟨ L⇄M ⟩ M⇝N)



open import Type
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (refl)

-- This was computed using C-c C-n `eval 10 (([ curry ]≡ proj (⊤ ⇒ ⊤ ⇒ ⊤) {inj₁ refl} ([ sym dist ]≡ (ƛ ([ sym dist ]≡ (ƛ ⟨ ⋆ , ⋆ ⟩))))) · ⟨ ⋆ , ⋆ ⟩)`
_ : (([ curry ]≡ proj (⊤ ⇒ ⊤ ⇒ ⊤) ([ sym dist ]≡ (ƛ ([ sym dist ]≡ (ƛ ⟨ ⋆ , ⋆ ⟩))))) · ⟨ ⋆ , ⋆ ⟩) ⇝ ⋆
_ =
  begin
    [ curry ]≡ proj (⊤ ⇒ ⊤ ⇒ ⊤) ([ sym dist ]≡ (ƛ ([ sym dist ]≡ (ƛ ⟨ ⋆ , ⋆ ⟩)))) · ⟨ ⋆ , ⋆ ⟩
      ⇄⟨ curry ⟩
    proj (⊤ ⇒ ⊤ ⇒ ⊤) ([ sym dist ]≡ (ƛ ([ sym dist ]≡ (ƛ ⟨ ⋆ , ⋆ ⟩)))) · ⋆ · ⋆
      ⇄⟨ ξ-·₁ (ξ-·₁ (ξ-proj (ξ-≡ (ξ-ƛ (sym dist-ƛ))))) ⟩
    proj (⊤ ⇒ ⊤ ⇒ ⊤) ([ sym dist ]≡ (ƛ ⟨ ƛ ⋆ , ƛ ⋆ ⟩)) · ⋆ · ⋆
      ⇄⟨ ξ-·₁ (ξ-·₁ (ξ-proj (sym dist-ƛ))) ⟩
    proj (⊤ ⇒ ⊤ ⇒ ⊤) ⟨ ƛ (ƛ ⋆) , ƛ (ƛ ⋆) ⟩ · ⋆ · ⋆
      ↪⟨ ξ-·₁ (ξ-·₁ (β-proj₁ V-ƛ V-ƛ)) ⟩
    (ƛ (ƛ ⋆)) · ⋆ · ⋆
      ↪⟨ ξ-·₁ (β-ƛ V-⋆) ⟩
    (ƛ ⋆) · ⋆
      ↪⟨ β-ƛ V-⋆ ⟩
    ⋆
  ∎