module Eval where

open import Term
open import IsoType
open import IsoTerm
open import Reduction
open import Progress
open import StrongNorm using (SN; sn; strong-norm)

infix  2 _⇝*_
infix  1 begin_
infixr 2 _⇄⟨_⟩_
infixr 2 _↪⟨_⟩_
infix  3 _∎

data _⇝*_ {Γ A} : (Γ ⊢ A) → (Γ ⊢ A) → Set where

  _∎ : (M : Γ ⊢ A)
      ------
    → M ⇝* M
  
  _⇄⟨_⟩_ : (L : Γ ⊢ A) {M N : Γ ⊢ A}
    → L ⇄ M
    → M ⇝* N
      ------
    → L ⇝* N

  _↪⟨_⟩_ : (L : Γ ⊢ A) {M N : Γ ⊢ A}
    → L ↪ M
    → M ⇝* N
      ------
    → L ⇝* N


begin_ : ∀ {Γ A} {M N : Γ ⊢ A}
  → M ⇝* N
    ------
  → M ⇝* N
begin M⇝N = M⇝N


data Steps {A} : ∅ ⊢ A → Set where

  steps : {L N : ∅ ⊢ A}
    → L ⇝* N
    → Value N
      ----------
    → Steps L

open import Data.Sum using (inj₁; inj₂)

eval´ : ∀ {A}
  → (L : ∅ ⊢ A)
  → SN L
  → Steps L
eval´ L _ with progress L
eval´ L _      | done ⇑L       =  steps (L ∎) (closed⇑→Value ⇑L)
eval´ L (sn f) | step⇄ {M} L⇄M with eval´ M (f (inj₂ L⇄M))
...               | steps M⇝N fin  =  steps (L ⇄⟨ L⇄M ⟩ M⇝N) fin
eval´ L (sn f) | step↪ {M} L↪M with eval´ M (f (inj₁ L↪M))
...               | steps M⇝N fin  =  steps (L ↪⟨ L↪M ⟩ M⇝N) fin

eval : ∀ {A} → (L : ∅ ⊢ A) → Steps L
eval L = eval´ L (strong-norm L)
