module IsoTerm where

open import IsoType
open import Type
open import Term
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (refl)
open import Subs using (Subst; Rename; rename; subst; _[_]; _•_; ids; ⟪_⟫)
open import Function.Base using (_∘_)

infix  4 _⇄_

σ-cong⇒₁ : ∀ {Γ A B} → (iso : B ≡ A) → Subst (Γ , A) (Γ , B)
σ-cong⇒₁ iso Z      =  [ iso ]≡ (` Z)
σ-cong⇒₁ iso (S x)  =  ` (S x)

--test : ∀ {Γ A B} → (iso : B ≡ A) → Subst (Γ , A) (Γ , B)
--test iso = [ iso ]≡ (` Z) • λ z → ` (S z)

σ-uncurry : ∀ {Γ A B} → Subst (Γ , A × B) (Γ , A , B)
σ-uncurry Z = ⟨ (` (S Z)) , (` Z) ⟩
σ-uncurry (S x) = ` (S (S x))

--test2 : ∀ {Γ A B} → Subst (Γ , A × B) (Γ , A , B)
--test2 = ⟨ (` (S Z)) , (` Z) ⟩ • λ x → ` (S (S x))

σ-curry : ∀ {Γ A B} → Subst (Γ , A , B) (Γ , A × B)
σ-curry {B = B} Z = proj B {inj₂ refl} (` Z)
σ-curry {A = A} (S Z) = proj A {inj₁ refl} (` Z)
σ-curry (S (S x)) = ` (S x)

--test : ∀ {Γ A B} → Subst (Γ , A , B) (Γ , A × B)
--test {A = A}{B = B} = proj B {inj₂ refl} (` Z) • proj A {inj₁ refl} (` Z) • ids ∘ S_


-- (3) This realtion eliminates the [_]≡_ from the terms
data _⇄_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where
  comm : ∀ {Γ A B} → {r : Γ ⊢ A} → {s : Γ ⊢ B}
    → [ comm ]≡ ⟨ r , s ⟩ ⇄ ⟨ s , r ⟩
  sym-comm : ∀ {Γ A B} → {r : Γ ⊢ A} → {s : Γ ⊢ B}
    → [ sym comm ]≡ ⟨ r , s ⟩ ⇄ ⟨ s , r ⟩
  asso : ∀ {Γ A B C} → {r : Γ ⊢ A} → {s : Γ ⊢ B} → {t : Γ ⊢ C}
    → [ asso ]≡ ⟨ r , ⟨ s , t ⟩ ⟩ ⇄ ⟨ ⟨ r , s ⟩ , t ⟩
  sym-asso : ∀ {Γ A B C} → {r : Γ ⊢ A} → {s : Γ ⊢ B} → {t : Γ ⊢ C}
    → [ sym asso ]≡ ⟨ ⟨ r , s ⟩ , t ⟩ ⇄ ⟨ r , ⟨ s , t ⟩ ⟩
  asso-split : ∀ {Γ A B C} → {r : Γ ⊢ A} → {s : Γ ⊢ B × C}
    → [ asso ]≡ ⟨ r , s ⟩ ⇄ ⟨ ⟨ r , proj B {inj₁ refl} s ⟩ , proj C {inj₂ refl} s ⟩
  sym-asso-split : ∀ {Γ A B C} → {r : Γ ⊢ A × B} → {s : Γ ⊢ C}
    → [ sym asso ]≡ ⟨ r , s ⟩ ⇄ ⟨ proj A {inj₁ refl} r , ⟨ proj B {inj₂ refl} r , s ⟩ ⟩

  dist-ƛ : ∀ {Γ A B C} → {r : Γ , C ⊢ A} → {s : Γ , C ⊢ B}
    → [ dist ]≡ ⟨ ƛ r , ƛ s ⟩ ⇄ ƛ ⟨ r , s ⟩
  sym-dist-ƛ : ∀ {Γ A B C} → {r : Γ , C ⊢ A} → {s : Γ , C ⊢ B}
    → [ sym dist ]≡ (ƛ ⟨ r , s ⟩) ⇄ ⟨ ƛ r , ƛ s ⟩
  sym-dist-ƛ-split : ∀ {Γ A B C} → {r : Γ , C ⊢ A × B}
    → [ sym dist ]≡ (ƛ r) ⇄ ⟨ ƛ proj A {inj₁ refl} r , ƛ proj B {inj₂ refl} r ⟩
  dist-ƛη₁ : ∀ {Γ A B C} → {r : Γ ⊢ C ⇒ A} → {s : Γ ⊢ C ⇒ B}
    → [ dist ]≡ ⟨ r , s ⟩ ⇄ ƛ ⟨ rename S_ r · ` Z , rename S_ s · ` Z ⟩
  dist-ƛη₂ : ∀ {Γ A B C} → {r : Γ , C ⊢ A} → {s : Γ ⊢ C ⇒ B}
    → [ dist ]≡ ⟨ ƛ r , s ⟩ ⇄ ƛ ⟨ r , rename S_ s · ` Z ⟩

  curry-s : ∀ {Γ A B C} → {r : Γ , A , B ⊢ C}
    → [ curry ]≡ (ƛ ƛ r) ⇄ ƛ subst Subs.σ-curry r
  curry-sη : ∀ {Γ A B C} → {r : Γ , A ⊢ B ⇒ C}
    → [ curry ]≡ (ƛ r) ⇄ ƛ subst Subs.σ-curry (rename S_ r · ` Z)
  uncurry-s : ∀ {Γ A B C} → {r : Γ , A × B ⊢ C}
    → [ sym curry ]≡ (ƛ r) ⇄ ƛ ƛ subst Subs.σ-uncurry r

  --eta : ∀ {Γ A B} → {r : Γ ⊢ A ⇒ B}
  --  → r ⇄ ƛ rename S_ r · ` Z
  
  --split : ∀ {Γ A B} → {r : Γ ⊢ A × B}
  --  → r ⇄ ⟨ proj A {inj₁ refl} r , proj B {inj₂ refl} r ⟩

  id-× : ∀ {Γ A} → {r : Γ ⊢ A} → {t : Γ ⊢ ⊤}
    → [ id-× ]≡ ⟨ r , t ⟩ ⇄ r
  sym-id-× : ∀ {Γ A} → {r : Γ ⊢ A}
    → [ sym id-× ]≡ r ⇄ ⟨ r , ⋆ ⟩
  id-⇒ : ∀ {Γ A} → {r : Γ ⊢ ⊤ ⇒ A}
    → [ id-⇒ ]≡ r ⇄ r · ⋆
  sym-id-⇒ : ∀ {Γ A} → {r : Γ ⊢ A}
    → [ sym id-⇒ ]≡ r ⇄ ƛ rename S_ r
  abs : ∀ {Γ A} → {r : Γ ⊢ A ⇒ ⊤}
    → [ abs ]≡ r ⇄ ⋆
  sym-abs : ∀ {Γ A} → {t : Γ ⊢ ⊤}
    → [ sym abs ]≡ t ⇄ ƛ rename (S_ {A = A}) t -- λ ⋆
  
  sym-sym : ∀ {Γ A B} → {r : Γ ⊢ A} → {iso : A ≡ B}
    → [ sym (sym iso) ]≡ r ⇄ [ iso ]≡ r
  
  cong⇒₁ : ∀ {Γ A B C} → {r : Γ , A ⊢ C} → {iso : A ≡ B}
    → [ cong⇒₁ iso ]≡ (ƛ r) ⇄ ƛ subst (Subs.σ-cong⇒₁ (sym iso)) r

  sym-cong⇒₁ : ∀ {Γ A B C} → {r : Γ , B ⊢ C} → {iso : A ≡ B}
    → [ sym (cong⇒₁ iso) ]≡ (ƛ r) ⇄ ƛ subst (Subs.σ-cong⇒₁ iso) r
  
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

open import Subs using
  (subst-shift-weaken
  ; rename-shift-weaken
  ; subst-cong⇒₁-commute
  ; subst-uncurry-commute
  ; subst-curry-commute
  ; subst-curryη-commute)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; cong₂; refl; trans)


⇄[] : ∀ {Γ Δ A}{t t' : Γ ⊢ A}{σ : Subst Γ Δ} → t ⇄ t' → subst σ t ⇄ subst σ t'
⇄[] comm = comm
⇄[] sym-comm = sym-comm
⇄[] asso = asso
⇄[] sym-asso = sym-asso
⇄[] asso-split = asso-split
⇄[] sym-asso-split = sym-asso-split
⇄[] dist-ƛ = dist-ƛ
⇄[] sym-dist-ƛ = sym-dist-ƛ
⇄[] sym-dist-ƛ-split = sym-dist-ƛ-split
⇄[] {σ = σ} (dist-ƛη₁ {C = C}{r = r}{s = s})
  rewrite (subst-shift-weaken {Σ = ∅} {B = C} {N = r} {σ = σ}) | (subst-shift-weaken {Σ = ∅} {B = C} {N = s} {σ = σ})
    = dist-ƛη₁
⇄[] {σ = σ} (dist-ƛη₂ {C = C}{s = s})
  rewrite (subst-shift-weaken {Σ = ∅} {B = C} {N = s} {σ = σ})
    = dist-ƛη₂
⇄[] {σ = σ} (curry-s {r = r})
  rewrite (Relation.Binary.PropositionalEquality.sym (subst-curry-commute {Σ = ∅} {N = r} {σ = σ}))
    = curry-s
⇄[] {σ = σ} (curry-sη {r = r})
  rewrite (Relation.Binary.PropositionalEquality.sym (subst-curryη-commute {N = r} {σ = σ}))
    = curry-sη
⇄[] {σ = σ} (uncurry-s {r = r})
  rewrite (Relation.Binary.PropositionalEquality.sym (subst-uncurry-commute {Σ = ∅} {N = r} {σ = σ}))
    = uncurry-s
⇄[] id-× = id-×
⇄[] sym-id-× = sym-id-×
⇄[] id-⇒ = id-⇒
⇄[] {σ = σ} (sym-id-⇒ {r = r})
  rewrite subst-shift-weaken {Σ = ∅} {B = ⊤} {N = r} {σ = σ}
    = sym-id-⇒
⇄[] abs = abs
⇄[] {σ = σ} (sym-abs {A = A} {t = t})
  rewrite (subst-shift-weaken {Σ = ∅} {B = A} {N = t} {σ = σ})
    = sym-abs
⇄[] sym-sym = sym-sym
⇄[] {σ = σ} (cong⇒₁ {r = r} {iso = iso})
  rewrite (Relation.Binary.PropositionalEquality.sym (subst-cong⇒₁-commute {Σ = ∅} {N = r} {σ = σ} {iso = sym iso}))
    = cong⇒₁
⇄[] {σ = σ} (sym-cong⇒₁ {r = r} {iso = iso})
  rewrite (Relation.Binary.PropositionalEquality.sym (subst-cong⇒₁-commute {Σ = ∅} {N = r} {σ = σ} {iso = iso}))
    = sym-cong⇒₁
⇄[] cong⇒₂ = cong⇒₂
⇄[] sym-cong⇒₂ = sym-cong⇒₂
⇄[] cong×₁ = cong×₁
⇄[] sym-cong×₁ = sym-cong×₁
⇄[] cong×₂ = cong×₂
⇄[] sym-cong×₂ = sym-cong×₂
⇄[] (ξ-·₁ step) = ξ-·₁ (⇄[] step)
⇄[] (ξ-·₂ step) = ξ-·₂ (⇄[] step)
⇄[] (ξ-⟨,⟩₁ step) = ξ-⟨,⟩₁ (⇄[] step)
⇄[] (ξ-⟨,⟩₂ step) = ξ-⟨,⟩₂ (⇄[] step)
⇄[] (ξ-proj step) = ξ-proj (⇄[] step)
⇄[] (ξ-≡ step) = ξ-≡ (⇄[] step)
⇄[] (ζ step) = ζ (⇄[] step)


open import Data.Product using (∃; proj₁; proj₂) renaming (_,_ to ﹙_,_﹚; _×_ to _⊗_)
open import Relation.Binary.PropositionalEquality using (cong; refl)
open import Subs using
  ( rename-cong⇒₁-commute
  ; rename-uncurry-commute
  ; rename-curry-commute
  ; rename-curryη-commute)


rename⇄ : ∀ {Γ Δ A}{t : Γ ⊢ A}{σ : Rename Γ Δ}{t'} → (rename σ t) ⇄ t' → ∃ λ t'' → (t ⇄ t'') ⊗ (rename σ t'' Relation.Binary.PropositionalEquality.≡ t')
rename⇄ {t = [ curry ]≡ (ƛ ƛ t)} curry-s = ﹙ _ , ﹙ curry-s , cong ƛ_ (Relation.Binary.PropositionalEquality.sym (rename-curry-commute {N = t})) ﹚ ﹚
rename⇄ {t = [ curry ]≡ (ƛ t)}{σ = σ} curry-sη
  rewrite rename-curryη-commute {N = t} {ρ = σ}
    = ﹙ _ , ﹙ curry-sη , refl ﹚ ﹚
rename⇄ {t = [ asso ]≡ ⟨ a , ⟨ b , c ⟩ ⟩} asso = ﹙ _ , ﹙ asso , refl ﹚ ﹚
rename⇄ {t = [ asso ]≡ ⟨ a , b ⟩} asso-split = ﹙ _ , ﹙ asso-split , refl ﹚ ﹚
rename⇄ {t = [ comm ]≡ ⟨ a , b ⟩} comm = ﹙ _ , ﹙ comm , refl ﹚ ﹚
rename⇄ {t = [ dist ]≡ ⟨ ƛ a , ƛ b ⟩} dist-ƛ = ﹙ _ , ﹙ dist-ƛ , refl ﹚ ﹚
rename⇄ {t = [ dist ]≡ ⟨ ƛ a , b ⟩}{σ = σ} (dist-ƛη₂ {C = C})
  rewrite Relation.Binary.PropositionalEquality.sym (rename-shift-weaken {Σ = ∅} {B = C} {N = b} {ρ = σ})
    = ﹙ _ , ﹙ dist-ƛη₂ , refl ﹚ ﹚
rename⇄ {t = [ dist ]≡ ⟨ a , b ⟩}{σ = σ} (dist-ƛη₁ {C = C})
  rewrite Relation.Binary.PropositionalEquality.sym (rename-shift-weaken {Σ = ∅} {B = C} {N = b} {ρ = σ}) | Relation.Binary.PropositionalEquality.sym (rename-shift-weaken {Σ = ∅} {B = C} {N = a} {ρ = σ})
    = ﹙ _ , ﹙ dist-ƛη₁ , refl ﹚ ﹚
rename⇄ {t = [ id-× ]≡ ⟨ a , b ⟩} id-× = ﹙ _ , ﹙ id-× , refl ﹚ ﹚
rename⇄ {t = [ id-⇒ ]≡ t} id-⇒ = ﹙ _ , ﹙ id-⇒ , refl ﹚ ﹚
rename⇄ {t = [ sym id-⇒ ]≡ t} sym-id-⇒ = ﹙ _ , ﹙ sym-id-⇒ , cong ƛ_ (rename-shift-weaken {Σ = ∅}) ﹚ ﹚
rename⇄ {t = [ abs ]≡ t} abs = ﹙ _ , ﹙ abs , refl ﹚ ﹚
rename⇄ {t = [ sym comm ]≡ ⟨ a , b ⟩} (sym-comm) = ﹙ _ , ﹙ sym-comm , refl ﹚ ﹚
rename⇄ {t = [ sym asso ]≡ ⟨ ⟨ a , b ⟩ , c ⟩} (sym-asso) = ﹙ _ , ﹙ sym-asso , refl ﹚ ﹚
rename⇄ {t = [ sym asso ]≡ ⟨ a , c ⟩} (sym-asso-split) = ﹙ _ , ﹙ sym-asso-split , refl ﹚ ﹚
rename⇄ {t = [ sym dist ]≡ (ƛ ⟨ a , b ⟩)} (sym-dist-ƛ) = ﹙ _ , ﹙ sym-dist-ƛ , refl ﹚ ﹚
rename⇄ {t = [ sym dist ]≡ (ƛ a)} (sym-dist-ƛ-split) = ﹙ _ , ﹙ sym-dist-ƛ-split , refl ﹚ ﹚
rename⇄ {t = [ sym curry ]≡ (ƛ t)} uncurry-s = ﹙ _ , ﹙ uncurry-s , cong ƛ_ (cong ƛ_ (Relation.Binary.PropositionalEquality.sym (rename-uncurry-commute {N = t}))) ﹚ ﹚
rename⇄ {t = [ sym id-× ]≡ t} (sym-id-×) = ﹙ _ , ﹙ sym-id-× , refl ﹚ ﹚
rename⇄ {t = [ sym abs ]≡ t} (sym-abs) = ﹙ _ , ﹙ sym-abs , (cong ƛ_ (rename-shift-weaken {Σ = ∅})) ﹚ ﹚
rename⇄ {t = [ sym (cong⇒₁ iso)]≡ (ƛ t)} (sym-cong⇒₁) = ﹙ _ , ﹙ sym-cong⇒₁ , (cong ƛ_ (Relation.Binary.PropositionalEquality.sym (rename-cong⇒₁-commute {N = t}))) ﹚ ﹚
rename⇄ {t = [ sym (cong⇒₂ iso)]≡ (ƛ t)} (sym-cong⇒₂) = ﹙ _ , ﹙ sym-cong⇒₂ , refl ﹚ ﹚
rename⇄ {t = [ sym (cong×₁ iso)]≡ ⟨ a , b ⟩} (sym-cong×₁) = ﹙ _ , ﹙ sym-cong×₁ , refl ﹚ ﹚
rename⇄ {t = [ sym (cong×₂ iso)]≡ ⟨ a , b ⟩} (sym-cong×₂) = ﹙ _ , ﹙ sym-cong×₂ , refl ﹚ ﹚
rename⇄ {t = [ sym (sym iso) ]≡ t} sym-sym = ﹙ _ , ﹙ sym-sym , refl ﹚ ﹚
rename⇄ {t = [ cong⇒₁ iso ]≡ (ƛ r)} cong⇒₁ = ﹙ _ , ﹙ cong⇒₁ , cong ƛ_ (Relation.Binary.PropositionalEquality.sym (rename-cong⇒₁-commute {N = r})) ﹚ ﹚
rename⇄ {t = [ _ ]≡ (ƛ r)} cong⇒₂ = ﹙ _ , ﹙ cong⇒₂ , refl ﹚ ﹚
rename⇄ {t = [ cong×₁ iso ]≡ ⟨ a , b ⟩} cong×₁ = ﹙ _ , ﹙ cong×₁ , refl ﹚ ﹚
rename⇄ {t = [ cong×₂ iso ]≡ ⟨ a , b ⟩} cong×₂ = ﹙ _ , ﹙ cong×₂ , refl ﹚ ﹚
rename⇄ {t = ƛ t} (ζ step) with rename⇄ step
... | ﹙ _ , ﹙ step , refl ﹚ ﹚ = ﹙ _ , ﹙ ζ step , refl ﹚ ﹚
rename⇄ {t = f · a} (ξ-·₁ step) with rename⇄ step
... | ﹙ _ , ﹙ step , refl ﹚ ﹚ = ﹙ _ , ﹙ ξ-·₁ step , refl ﹚ ﹚
rename⇄ {t = f · a} (ξ-·₂ step) with rename⇄ step
... | ﹙ _ , ﹙ step , refl ﹚ ﹚ = ﹙ _ , ﹙ (ξ-·₂ step) , refl ﹚ ﹚
rename⇄ {t = ⟨ a , b ⟩} (ξ-⟨,⟩₁ step) with rename⇄ step
... | ﹙ _ , ﹙ step , refl ﹚ ﹚ = ﹙ _ , ﹙ (ξ-⟨,⟩₁ step) , refl ﹚ ﹚
rename⇄ {t = ⟨ a , b ⟩} (ξ-⟨,⟩₂ step) with rename⇄ step
... | ﹙ _ , ﹙ step , refl ﹚ ﹚ = ﹙ _ , ﹙ (ξ-⟨,⟩₂ step) , refl ﹚ ﹚
rename⇄ {t = proj _ t} (ξ-proj step) with rename⇄ step
... | ﹙ _ , ﹙ step , refl ﹚ ﹚ = ﹙ _ , ﹙ (ξ-proj step) , refl ﹚ ﹚
rename⇄ {t = [ _ ]≡ t} (ξ-≡ step) with rename⇄ step
... | ﹙ _ , ﹙ step , refl ﹚ ﹚ = ﹙ _ , ﹙ (ξ-≡ step) , refl ﹚ ﹚
