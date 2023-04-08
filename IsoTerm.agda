module IsoTerm where

open import IsoType
open import Type
open import Term
open import Reduction
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (refl)
open import Subs using (rename; subst)

infix  4 _⇄_

σ : ∀ {Γ A B C} → (iso : B ≡ A) → Γ , A ∋ C → Γ , B ⊢ C
σ iso Z      =  [ iso ]≡ (` Z)
σ iso (S x)  =  ` (S x)

-- (3) This realtion eliminates the [_]≡_ from the terms
data _⇄_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where
  comm : ∀ {Γ A B} → {r : Γ ⊢ A} → {s : Γ ⊢ B}
    → [ comm ]≡ ⟨ r , s ⟩ ⇄ ⟨ s , r ⟩
  asso : ∀ {Γ A B C} → {r : Γ ⊢ A} → {s : Γ ⊢ B} → {t : Γ ⊢ C}
    → [ asso ]≡ ⟨ r , ⟨ s , t ⟩ ⟩ ⇄ ⟨ ⟨ r , s ⟩ , t ⟩
  dist-ƛ : ∀ {Γ A B C} → {r : Γ , C ⊢ A} → {s : Γ , C ⊢ B}
    → [ dist ]≡ ⟨ ƛ r , ƛ s ⟩ ⇄ ƛ ⟨ r , s ⟩
  dist-· : ∀ {Γ A B C} → {r : Γ ⊢ C ⇒ A} → {s : Γ ⊢ C ⇒ B} → {t : Γ ⊢ C}
    → [ dist ]≡ ⟨ r , s ⟩ · t ⇄ ⟨ r · t , s · t ⟩
  curry : ∀ {Γ A B C} → {r : Γ ⊢ A ⇒ B ⇒ C} → {s : Γ ⊢ A} → {t : Γ ⊢ B}
    → [ curry ]≡ r · ⟨ s , t ⟩ ⇄ r · s · t
  uncurry₂ : ∀ {Γ A B C} → {r : Γ ⊢ A × B ⇒ C} → {s : Γ ⊢ A} → {t : Γ ⊢ B}
    → [ sym curry ]≡ r · s · t ⇄ r · ⟨ s , t ⟩
  uncurry₁ : ∀ {Γ A B C} → {r : Γ ⊢ A × B ⇒ C} → {s : Γ ⊢ A}
    → [ sym curry ]≡ r · s ⇄ ƛ rename S_ r · ⟨ rename S_ s , ` Z ⟩

  dist-πƛ : ∀ {Γ A B C} {T p₁ p₂} → {r : Γ , C ⊢ A × B}
    → proj (C ⇒ T) {p₁} ([ sym dist ]≡ (ƛ r)) ⇄ ƛ proj T {p₂} r
  dist-π· : ∀ {Γ A B C} {T p₁ p₂} → {r : Γ ⊢ C ⇒ A × B} → {s : Γ ⊢ C}
    → proj (C ⇒ T) {p₁} ([ sym dist ]≡ r) · s ⇄ proj T {p₂} (r · s)
  
  split₁ : ∀ {Γ A B C} → {r : Γ ⊢ A} → {s : Γ ⊢ B × C}
    → proj (A × B) {inj₁ refl} ([ asso ]≡ ⟨ r , s ⟩) ⇄ ⟨ r , proj B {inj₁ refl} s ⟩
  split₂ : ∀ {Γ A B C} → {r : Γ ⊢ A} → {s : Γ ⊢ B × C}
    → proj C {inj₂ refl} ([ asso ]≡ ⟨ r , s ⟩) ⇄ proj C {inj₂ refl} s

  sym-split₁ : ∀ {Γ A B C} → {r : Γ ⊢ A × B} → {s : Γ ⊢ C}
    → proj A {inj₁ refl} ([ sym asso ]≡ ⟨ r , s ⟩) ⇄ proj A {inj₁ refl} r
  sym-split₂ : ∀ {Γ A B C} → {r : Γ ⊢ A × B} → {s : Γ ⊢ C}
    → proj (B × C) {inj₂ refl} ([ sym asso ]≡ ⟨ r , s ⟩) ⇄ ⟨ proj B {inj₂ refl} r , s ⟩

  id-× : ∀ {Γ A} → {r : Γ ⊢ A}
    → [ id-× ]≡ ⟨ r , ⋆ ⟩ ⇄ r
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
  
--  inv : ∀ {Γ A B} → {r : Γ ⊢ A} → {iso : A ≡ B}
--    → [ sym iso ]≡ ([ iso ]≡ r) ⇄ r
  
--  cong⇒₁2 : ∀ {Γ A B C} → {r : Γ , A ⊢ C} → {iso : A ≡ B}
--    → [ cong⇒₁ iso ]≡ (ƛ r) ⇄ ƛ subst (σ (sym iso)) r

  cong⇒₁ : ∀ {Γ A B C} → {r : Γ ⊢ A ⇒ C} → {s : Γ ⊢ B} → {iso : A ≡ B}
    → [ cong⇒₁ iso ]≡ r · s ⇄ r · [ sym iso ]≡ s
  
  sym-cong⇒₁ : ∀ {Γ A B C} → {r : Γ ⊢ B ⇒ C} → {s : Γ ⊢ A} → {iso : A ≡ B}
    → [ sym (cong⇒₁ iso) ]≡ r · s ⇄ r · [ iso ]≡ s
  
  cong⇒₂ : ∀ {Γ A B C} → {r : Γ , C ⊢ A} → {iso : A ≡ B}
    → [ cong⇒₂ iso ]≡ (ƛ r) ⇄ ƛ ([ iso ]≡ r)
  
--  cong⇒₂2 : ∀ {Γ A B C} → {r : Γ ⊢ C ⇒ A} → {s : Γ ⊢ C} → {iso : A ≡ B}
--    → [ cong⇒₂ iso ]≡ r · s ⇄ [ iso ]≡ (r · s)
  
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
