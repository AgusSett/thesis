module IsoTerm where

open import IsoType
open import Type
open import Term
open import Reduction
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (refl)
open import Subs using (rename; subst; _[_])

infix  4 _⇄_

σ-cong⇒₁ : ∀ {Γ A B C} → (iso : B ≡ A) → Γ , A ∋ C → Γ , B ⊢ C
σ-cong⇒₁ iso Z      =  [ iso ]≡ (` Z)
σ-cong⇒₁ iso (S x)  =  ` (S x)

σ-uncurry : ∀ {Γ A B C} → Γ , A × B ∋ C → Γ , A , B ⊢ C
σ-uncurry Z = ⟨ (` (S Z)) , (` Z) ⟩
σ-uncurry (S x) = ` (S (S x))

σ-curry : ∀ {Γ A B C} → Γ , A , B ∋ C → Γ , A × B ⊢ C
σ-curry {B = B} Z = proj B {inj₂ refl} (` Z)
σ-curry {A = A} (S Z) = proj A {inj₁ refl} (` Z)
σ-curry (S (S x)) = ` (S x)


-- (3) This realtion eliminates the [_]≡_ from the terms
data _⇄_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where
  comm : ∀ {Γ A B} → {r : Γ ⊢ A} → {s : Γ ⊢ B}
    → [ comm ]≡ ⟨ r , s ⟩ ⇄ ⟨ s , r ⟩
  asso : ∀ {Γ A B C} → {r : Γ ⊢ A} → {s : Γ ⊢ B} → {t : Γ ⊢ C}
    → [ asso ]≡ ⟨ r , ⟨ s , t ⟩ ⟩ ⇄ ⟨ ⟨ r , s ⟩ , t ⟩
  dist-ƛ : ∀ {Γ A B C} → {r : Γ , C ⊢ A} → {s : Γ , C ⊢ B}
    → [ dist ]≡ ⟨ ƛ r , ƛ s ⟩ ⇄ ƛ ⟨ r , s ⟩
  dist-· : ∀ {Γ A B C} → {r : Γ ⊢ C ⇒ A} → {s : Γ ⊢ C ⇒ B} → {t : Γ ⊢ C} -- ???
    → [ dist ]≡ ⟨ r , s ⟩ · t ⇄ ⟨ r · t , s · t ⟩
  curry : ∀ {Γ A B C} → {r : Γ ⊢ A ⇒ B ⇒ C} → {s : Γ ⊢ A} → {t : Γ ⊢ B}  -- ???
    → [ curry ]≡ r · ⟨ s , t ⟩ ⇄ r · s · t
  uncurry : ∀ {Γ A B C} → {r : Γ ⊢ A × B ⇒ C} → {s : Γ ⊢ A} → {t : Γ ⊢ B} -- ???
    → [ sym curry ]≡ r · s · t ⇄ r · ⟨ s , t ⟩

  curry-s : ∀ {Γ A B C} → {r : Γ , A , B ⊢ C}
    → [ curry ]≡ (ƛ ƛ r) ⇄ ƛ subst σ-curry r
  uncurry-s : ∀ {Γ A B C} → {r : Γ , A × B ⊢ C}
    → [ sym curry ]≡ (ƛ r) ⇄ ƛ ƛ subst σ-uncurry r

  eta : ∀ {Γ A B} → {r : Γ ⊢ A ⇒ B}
    → r ⇄ ƛ rename S_ r · ` Z
  
  split : ∀ {Γ A B} → {r : Γ ⊢ A × B}
    → r ⇄ ⟨ proj A {inj₁ refl} r , proj B {inj₂ refl} r ⟩

  id-× : ∀ {Γ A} → {r : Γ ⊢ A} → {t : Γ ⊢ ⊤}
    → [ id-× ]≡ ⟨ r , t ⟩ ⇄ r
  id-⇒ : ∀ {Γ A} → {r : Γ ⊢ ⊤ ⇒ A}
    → [ id-⇒ ]≡ r ⇄ r · ⋆
  sym-id-⇒ : ∀ {Γ A} → {r : Γ ⊢ A}
    → [ sym id-⇒ ]≡ r ⇄ ƛ rename S_ r
  abs : ∀ {Γ A} → {r : Γ ⊢ A ⇒ ⊤} → {t : Γ ⊢ ⊤}
    → [ abs ]≡ r ⇄ t

  sym : ∀ {Γ A B} → {r : Γ ⊢ A} → {s : Γ ⊢ B} → {iso : A ≡ B}
    → [ iso ]≡ r ⇄ s
    → [ sym iso ]≡ s ⇄ r
  
  sym-sym : ∀ {Γ A B} → {r : Γ ⊢ A} → {iso : A ≡ B}
    → [ sym (sym iso) ]≡ r ⇄ [ iso ]≡ r
  
  cong⇒₁ : ∀ {Γ A B C} → {r : Γ , A ⊢ C} → {iso : A ≡ B}
    → [ cong⇒₁ iso ]≡ (ƛ r) ⇄ ƛ subst (σ-cong⇒₁ (sym iso)) r

  sym-cong⇒₁ : ∀ {Γ A B C} → {r : Γ , B ⊢ C} → {iso : A ≡ B}
    → [ sym (cong⇒₁ iso) ]≡ (ƛ r) ⇄ ƛ subst (σ-cong⇒₁ iso) r
  
  cong⇒₂ : ∀ {Γ A B C} → {r : Γ , C ⊢ A} → {iso : A ≡ B}
    → [ cong⇒₂ iso ]≡ (ƛ r) ⇄ ƛ ([ iso ]≡ r)
  
  sym-cong⇒₂ : ∀ {Γ A B C} → {r : Γ , C ⊢ B} → {iso : A ≡ B}
    → [ sym (cong⇒₂ iso) ]≡ (ƛ r) ⇄ ƛ ([ sym iso ]≡ r)
  
  cong×₁ : ∀ {Γ A B C} → {r : Γ ⊢ A} → {s : Γ ⊢ C} → {iso : A ≡ B}
    → [ cong×₁ iso ]≡ ⟨ r , s ⟩ ⇄ ⟨ [ iso ]≡ r , s ⟩
  
  sym-cong×₁ : ∀ {Γ A B C} → {r : Γ ⊢ B} → {s : Γ ⊢ C} → {iso : A ≡ B}
    → [ sym (cong×₁ iso) ]≡ ⟨ r , s ⟩ ⇄ ⟨ [ sym iso ]≡ r , s ⟩
  
  cong×₂ : ∀ {Γ A B C} → {r : Γ ⊢ C} → {s : Γ ⊢ A} → {iso : A ≡ B}
    → [ cong×₂ iso ]≡ ⟨ r , s ⟩ ⇄ ⟨ r , [ iso ]≡ s ⟩
  
  sym-cong×₂ : ∀ {Γ A B C} → {r : Γ ⊢ C} → {s : Γ ⊢ B} → {iso : A ≡ B}
    → [ sym (cong×₂ iso) ]≡ ⟨ r , s ⟩ ⇄ ⟨ r , [ sym iso ]≡ s ⟩
  
  ξ-·₁ : ∀ {Γ A B} {L L' : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
    → L ⇄ L'
    → L · M ⇄ L' · M

  ξ-·₂ : ∀ {Γ A B} {L : Γ ⊢ A ⇒ B} {M M' : Γ ⊢ A}
    → M ⇄ M'
    → L · M ⇄ L · M'
  
  ξ-⟨,⟩₁ : ∀ {Γ A B} {M M' : Γ ⊢ A} {N : Γ ⊢ B}
    → M ⇄ M'
    → ⟨ M , N ⟩ ⇄ ⟨ M' , N ⟩

  ξ-⟨,⟩₂ : ∀ {Γ A B} {M : Γ ⊢ A} {N N' : Γ ⊢ B}
    → N ⇄ N'
    → ⟨ M , N ⟩ ⇄ ⟨ M , N' ⟩

  ξ-proj : ∀ {Γ A B C p} {L L' : Γ ⊢ A × B}
    → L ⇄ L'
    → proj C {p} L ⇄ proj C {p} L'
  
  ξ-≡ : ∀ {Γ A B} {L L' : Γ ⊢ A} {iso : A ≡ B}
    → L ⇄ L'
    → ([ iso ]≡ L) ⇄ ([ iso ]≡ L')
  
  ζ : ∀ {Γ A B} {L L' : Γ , B ⊢ A}
    → L ⇄ L'
    → ƛ L ⇄ ƛ L'
