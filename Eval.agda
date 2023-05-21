module Eval where

open import Term
open import IsoType
open import IsoTerm
open import Reduction
open import Progress

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
  → ℕ -- Agda need this argument for the termination check
  → (L : ∅ ⊢ A)
  → Steps L
eval zero L                     = steps (L ∎)
eval (suc n) L with progress L
eval (suc n) L | done VL = steps (L ∎)
eval (suc n) L | step⇄ {M} L⇄M with eval n M
...            | steps M⇝N                  = steps (L ⇄⟨ L⇄M ⟩ M⇝N)
eval (suc n) L | step↪ {M} L↪M with eval n M
...            | steps M⇝N                  = steps (L ↪⟨ L↪M ⟩ M⇝N)



open import Type
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (refl)

data SN {Γ A} (t : Γ ⊢ A) : Set where
  sn : (∀ {t'} → t ↪ t' ⊎ t ⇄ t' → SN t') → SN t

-- This was computed using C-c C-n `eval 10 (([ curry ]≡ proj (⊤ ⇒ ⊤ ⇒ ⊤) {inj₁ refl} ([ sym dist ]≡ (ƛ ([ sym dist ]≡ (ƛ ⟨ ⋆ , ⋆ ⟩))))) · ⟨ ⋆ , ⋆ ⟩)`
_ : (([ curry ]≡ proj (⊤ ⇒ ⊤ ⇒ ⊤) ([ sym dist ]≡ (ƛ ([ sym dist ]≡ (ƛ ⟨ ⋆ , ⋆ ⟩))))) · ⟨ ⋆ , ⋆ ⟩) ⇝ (⋆ {∅})
_ =
  begin
    [ curry ]≡ proj (⊤ ⇒ ⊤ ⇒ ⊤) ([ sym dist ]≡ (ƛ ([ sym dist ]≡ (ƛ ⟨ ⋆ , ⋆ ⟩)))) · ⟨ ⋆ , ⋆ ⟩
      ⇄⟨ curry ⟩
    proj (⊤ ⇒ ⊤ ⇒ ⊤) ([ sym dist ]≡ (ƛ ([ sym dist ]≡ (ƛ ⟨ ⋆ , ⋆ ⟩)))) · ⋆ · ⋆
      ⇄⟨ ξ-·₁ (ξ-·₁ (ξ-proj (ξ-≡ (ζ (sym dist-ƛ))))) ⟩
    proj (⊤ ⇒ ⊤ ⇒ ⊤) ([ sym dist ]≡ (ƛ ⟨ ƛ ⋆ , ƛ ⋆ ⟩)) · ⋆ · ⋆
      ⇄⟨ ξ-·₁ (ξ-·₁ (ξ-proj (sym dist-ƛ))) ⟩
    proj (⊤ ⇒ ⊤ ⇒ ⊤) ⟨ ƛ (ƛ ⋆) , ƛ (ƛ ⋆) ⟩ · ⋆ · ⋆
      ↪⟨ ξ-·₁ (ξ-·₁ (β-proj₁)) ⟩
    (ƛ (ƛ ⋆)) · ⋆ · ⋆
      ↪⟨ ξ-·₁ (β-ƛ) ⟩
    (ƛ ⋆) · ⋆
      ↪⟨ β-ƛ ⟩
    ⋆
  ∎

open import Subs using (rename)

⟦_⟧_ : ∀ {Γ B} → (r : Γ ⊢ B) → (A : Type) → Γ ⊢ (A ⇒ A) ⇒ B
⟦ r ⟧ A = ƛ rename S_ r

_⟪_⟫ : ∀ {Γ B} → (A : Type) → (r : Γ ⊢ (A ⇒ A) ⇒ B) → Γ ⊢ B
A ⟪ r ⟫ = r · (ƛ ` Z)

𝟙 : Type
𝟙 = τ

𝟚 : Type
𝟚 = τ ⇒ τ

-- Ω = (λx:T.xx)(λx:T.xx) : T
Ω : ∅ ⊢ ⊤
Ω = (ƛ ` Z · [ abs ]≡ (` Z)) · (ƛ [ sym abs ]≡ (` Z) · ` Z)

_ : Ω ⇝ ⋆ 
_ =
  begin
    Ω
      ↪⟨ β-ƛ ⟩
    (ƛ ([ sym abs ]≡ (` Z)) · ` Z) · ([ abs ]≡ (ƛ ([ sym abs ]≡ (` Z)) · ` Z))
      ⇄⟨ ξ-·₂ abs ⟩
    (ƛ ([ sym abs ]≡ (` Z)) · ` Z) · ⋆
      ↪⟨ β-ƛ ⟩
    ([ sym abs ]≡ ⋆) · ⋆
      ⇄⟨ ξ-·₁ (sym abs) ⟩
    (ƛ ⋆) · ⋆
      ↪⟨ β-ƛ ⟩
    ⋆
  ∎

_ : ∀ {Γ A B} → Γ , B , A ⊢ A
_ = (ƛ proj _ {inj₁ refl} ([ comm ]≡ (` Z))) · ⟨ ` (S Z) , ` Z ⟩

_ : ∀ {Γ A B} → Γ  ⊢ A × B ⇒ B
_ = (ƛ proj _ {inj₁ refl} ([ comm ]≡ (` Z)))

_ : ∀ {Γ A B} → Γ ⊢ A ⇒ B ⇒ (A × B)
_ = ƛ ƛ ⟨ ` (S Z) , ` Z ⟩

_ : ∀ {Γ A B} → Γ ⊢ (A ⇒ B ⇒ A) × (A ⇒ B ⇒ B)
_ = [ sym dist ]≡ (ƛ [ sym dist ]≡ (ƛ ⟨ ` (S Z) , ` Z ⟩))

test : ∀ {Γ} → Γ ⊢ ⊤
test = proj _ {inj₁ refl} ([ sym dist ]≡ ([ curry ]≡ (ƛ ƛ ⟨ ` (S Z) , ` Z ⟩))) · ⟨ ⋆ , ⋆ ⟩

--- 


_ : ∀ {Γ A B} → Γ ⊢ A ⇒ (B ⇒ B)
_ = (([ sym curry ]≡ ([ cong⇒₁ comm ]≡ ([ curry ]≡ (ƛ ƛ ` Z)))) · (ƛ ` Z))
-- ƛ ([ cong⇒₁ comm ]≡ ([ curry ]≡ (ƛ ƛ ` Z))) · ⟨ ` S Z , ` Z ⟩
-- ƛ ([ curry ]≡ (ƛ ƛ ` Z)) · [ cong⇒₁ comm ]≡ ⟨ ` S Z , ` Z ⟩
-- ƛ ([ curry ]≡ (ƛ ƛ ` Z)) · ⟨ ` Z , ` S Z ⟩
-- ƛ (ƛ ƛ ` Z) · ` Z  · ` S Z

_ : ∀ {Γ A B} → Γ ⊢ (A ⇒ B ⇒ A) × (A ⇒ B ⇒ B)
_ = ⟨ ƛ ƛ ` (S Z) , ƛ ƛ ` Z ⟩

_ : ∀ {Γ A B} → Γ ⊢ A ⇒ B ⇒ (A × B)
_ = ƛ ([ dist ]≡ ⟨ ƛ ` (S Z) , ƛ ` Z ⟩)

