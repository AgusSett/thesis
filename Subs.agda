module Subs where

open import Term

Rename : Context → Context → Set
Rename Γ Δ = ∀{A} → Γ ∋ A → Δ ∋ A

Subst : Context → Context → Set
Subst Γ Δ = ∀{A} → Γ ∋ A → Δ ⊢ A

infixr 6 _•_

ids : ∀{Γ} → Subst Γ Γ
ids x = ` x

_•_ : ∀{Γ Δ A} → (Δ ⊢ A) → Subst Γ Δ → Subst (Γ , A) Δ
(M • σ) Z = M
(M • σ) (S x) = σ x


ext : ∀ {Γ Δ A}
  → Rename Γ Δ
    ---------------------------------
  → Rename (Γ , A) (Δ , A)
ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)


rename : ∀ {Γ Δ}
  → Rename Γ Δ
    -----------------------
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
rename ρ (` x)          =  ` (ρ x)
rename ρ (ƛ N)          =  ƛ (rename (ext ρ) N)
rename ρ (L · M)        =  (rename ρ L) · (rename ρ M)
rename ρ ⟨ M , N ⟩      =  ⟨ rename ρ M , rename ρ N ⟩
rename ρ (proj C {p} L) =  proj C {p} (rename ρ L)
rename ρ ⋆              =  ⋆
rename ρ ([ iso ]≡ N)   =  [ iso ]≡ rename ρ N


exts : ∀ {Γ Δ A}
  → Subst Γ Δ
    ---------------------------------
  → Subst (Γ , A) (Δ , A)
exts σ Z      =  ` Z
exts σ (S x)  =  rename S_ (σ x)

subst : ∀ {Γ Δ} → Subst Γ Δ → (∀ {C} → Γ ⊢ C → Δ ⊢ C)
subst σ (` k)          =  σ k
subst σ (ƛ N)          =  ƛ (subst (exts σ) N)
subst σ (L · M)        =  (subst σ L) · (subst σ M)
subst σ ⟨ M , N ⟩      =  ⟨ subst σ M , subst σ N ⟩
subst σ (proj C {p} L) =  proj C {p} (subst σ L)
subst σ ⋆              =  ⋆
subst σ ([ iso ]≡ N)   =  [ iso ]≡ subst σ N

⟪_⟫ : ∀{Γ Δ A} → Subst Γ Δ → Γ ⊢ A → Δ ⊢ A
⟪ σ ⟫ = λ M → subst σ M

_[_] : ∀ {Γ A B}
  → Γ , B ⊢ A
  → Γ ⊢ B
    ---------
  → Γ ⊢ A
_[_] {Γ} {A} {B} N M =  ⟪ M • ids ⟫ N


_,*_ : Context → Context → Context
Γ ,* ∅       = Γ
Γ ,* (Δ , A) = (Γ ,* Δ) , A

ext* : ∀ {Γ Δ Σ} → Rename Γ Δ → Rename (Γ ,* Σ) (Δ ,* Σ)
ext* {Σ = ∅}     ρ = ρ
ext* {Σ = _ , _} ρ = ext (ext* ρ)

exts* : ∀ {Γ Δ Σ} → Subst Γ Δ → Subst (Γ ,* Σ) (Δ ,* Σ)
exts* {Σ = ∅}     σ = σ
exts* {Σ = _ , _} σ = exts (exts* σ)


open import Relation.Binary.PropositionalEquality using (_≡_; cong; cong₂; refl; sym; trans)
open import Function.Base using (_∘_)

sub-id-var : ∀{Γ Σ} {A} {v : Γ ,* Σ ∋ A} → exts* {Σ = Σ} ids v ≡ ` v
sub-id-var {Σ = ∅} {v = v} = refl
sub-id-var {Σ = Σ , _} {v = Z} = refl
sub-id-var {Σ = Σ , _} {v = S v} = cong (rename S_) (sub-id-var {Σ = Σ} {v = v})


sub-id : ∀{Γ Σ} {A} {N : Γ ,* Σ ⊢ A} → ⟪ exts* {Σ = Σ} ids ⟫ N ≡ N
sub-id {Σ = Σ} {N = ` v} = sub-id-var {Σ = Σ} {v = v}
sub-id {N = ⋆} = refl
sub-id {Σ = Σ} {N = ƛ N} = cong ƛ_ (sub-id {Σ = Σ , _} {N = N})
sub-id {Σ = Σ} {N = a · b} = cong₂ _·_ (sub-id {Σ = Σ} {N = a}) (sub-id {Σ = Σ} {N = b})
sub-id {Σ = Σ} {N = ⟨ a , b ⟩} = cong₂ ⟨_,_⟩ (sub-id {Σ = Σ} {N = a}) (sub-id {Σ = Σ} {N = b})
sub-id {Σ = Σ} {N = proj _ N} = cong (proj _) (sub-id {Σ = Σ} {N = N})
sub-id {Σ = Σ} {N = [ iso ]≡ N} = cong ([ iso ]≡_) (sub-id {Σ = Σ} {N = N})

rename-subst-ids-var : ∀{Γ Δ Σ A}{v : Γ ,* Σ ∋ A}{ρ : Rename Γ Δ}
    → exts* (ids ∘ ρ) v ≡ ` ((ext* ρ) v)
rename-subst-ids-var {Σ = ∅} {v = Z} = refl
rename-subst-ids-var {Σ = ∅} {v = S v} = refl
rename-subst-ids-var {Σ = Σ , _} {v = Z} = refl
rename-subst-ids-var {Σ = Σ , _} {v = S v} {ρ = ρ} = cong (rename S_) (rename-subst-ids-var {v = v} {ρ = ρ})

rename-subst-ids : ∀{Γ Δ Σ A}{N : Γ ,* Σ ⊢ A}{ρ : Rename Γ Δ}
    → ⟪ exts* (ids ∘ ρ) ⟫ N ≡ rename (ext* ρ) N
rename-subst-ids {N = ` v} {ρ = ρ} = rename-subst-ids-var {v = v} {ρ = ρ}
rename-subst-ids {N = ⋆} = refl
rename-subst-ids {N = ƛ n} {ρ = ρ} = cong ƛ_ (rename-subst-ids {N = n} {ρ = ρ})
rename-subst-ids {N = a · b} {ρ = ρ} = cong₂ _·_ (rename-subst-ids {N = a} {ρ = ρ}) (rename-subst-ids {N = b} {ρ = ρ})
rename-subst-ids {N = ⟨ a , b ⟩} {ρ = ρ} = cong₂ ⟨_,_⟩ (rename-subst-ids {N = a} {ρ = ρ}) (rename-subst-ids {N = b} {ρ = ρ})
rename-subst-ids {N = proj _ n} {ρ = ρ} = cong (proj _) (rename-subst-ids {N = n} {ρ = ρ})
rename-subst-ids {N = [ iso ]≡ n} {ρ = ρ} = cong ([ iso ]≡_) (rename-subst-ids {N = n} {ρ = ρ})


subst-weaken-var : ∀{Γ Δ Σ A B}{v : Γ ,* Σ ∋ A}{M : Δ ⊢ B}{σ : Subst Γ Δ}
    → exts* (M • σ) ((ext* S_) v) ≡ exts* σ v
subst-weaken-var {Σ = ∅} {v = v} = refl
subst-weaken-var {Σ = Σ , _} {v = Z} = refl
subst-weaken-var {Σ = Σ , _} {v = S v} {σ = σ} = cong (rename S_) (subst-weaken-var {v = v} {σ = σ})

subst-weaken : ∀{Γ Δ Σ A B}{N : Γ ,* Σ ⊢ A}{M : Δ ⊢ B}{σ : Subst Γ Δ}
    → ⟪ exts* (M • σ) ⟫ (rename (ext* S_) N) ≡ ⟪ exts* σ ⟫ N
subst-weaken {N = ` v} {σ = σ} = subst-weaken-var {v = v} {σ = σ}
subst-weaken {N = ⋆} {σ = σ} = refl
subst-weaken {N = ƛ n} {σ = σ} = cong ƛ_ (subst-weaken {N = n} {σ = σ})
subst-weaken {N = a · b} {σ = σ} = cong₂ _·_ (subst-weaken {N = a} {σ = σ}) (subst-weaken {N = b} {σ = σ})
subst-weaken {N = ⟨ a , b ⟩} {σ = σ} = cong₂ ⟨_,_⟩ (subst-weaken {N = a} {σ = σ}) (subst-weaken {N = b} {σ = σ})
subst-weaken {N = proj _ n} {σ = σ} = cong (proj _) (subst-weaken {N = n} {σ = σ})
subst-weaken {N = [ iso ]≡ n} {σ = σ} = cong ([ iso ]≡_) (subst-weaken {N = n} {σ = σ})

rename-shift-weaken-var : ∀{Γ Δ Σ A B}{v : Γ ,* Σ ∋ A}{ρ : Rename Γ Δ}
    → ext* (ext ρ) (ext* {Σ = Σ} (S_ {A = B}) v) ≡ ext* S_ (ext* ρ v)
rename-shift-weaken-var {Σ = ∅} = refl
rename-shift-weaken-var {Σ = Σ , _} {v = Z} = refl
rename-shift-weaken-var {Σ = Σ , _} {v = S v} = cong S_ (rename-shift-weaken-var {v = v})

rename-shift-weaken : ∀{Γ Δ Σ A B}{N : Γ ,* Σ ⊢ A}{ρ : Rename Γ Δ}
    → rename (ext* (ext ρ)) (rename (ext* {Σ = Σ} (S_ {A = B})) N) ≡ rename (ext* S_) (rename (ext* ρ) N)
rename-shift-weaken {N = ` v} = cong `_ (rename-shift-weaken-var  {v = v})
rename-shift-weaken {N = ⋆} = refl
rename-shift-weaken {N = ƛ N} {ρ = ρ} = cong ƛ_ (rename-shift-weaken {N = N} {ρ = ρ})
rename-shift-weaken {N = a · b} {ρ = ρ} = cong₂ _·_ (rename-shift-weaken {N = a} {ρ = ρ}) (rename-shift-weaken {N = b} {ρ = ρ})
rename-shift-weaken {N = ⟨ a , b ⟩} {ρ = ρ} = cong₂ ⟨_,_⟩ (rename-shift-weaken {N = a} {ρ = ρ}) (rename-shift-weaken {N = b} {ρ = ρ})
rename-shift-weaken {N = proj _ N} {ρ = ρ} = cong (proj _) (rename-shift-weaken {N = N} {ρ = ρ})
rename-shift-weaken {N = [ iso ]≡ N} {ρ = ρ} = cong ([ iso ]≡_) (rename-shift-weaken {N = N} {ρ = ρ})

subst-shift-weaken-var : ∀{Γ Δ Σ A B}{v : Γ ,* Σ ∋ A}{σ : Subst Γ Δ}
    → exts* (exts σ) (ext* {Σ = Σ} (S_ {A = B}) v) ≡ rename (ext* (S_)) (exts* σ v)
subst-shift-weaken-var {Σ = ∅} = refl
subst-shift-weaken-var {Σ = Σ , _} {v = Z} = refl
subst-shift-weaken-var {Σ = Σ , _} {v = S v} {σ = σ} =
  trans
    (cong (rename S_) (subst-shift-weaken-var {v = v}))
    (sym (rename-shift-weaken {Σ = ∅}))

subst-shift-weaken : ∀{Γ Δ Σ A B}{N : Γ ,* Σ ⊢ A}{σ : Subst Γ Δ}
    → ⟪ exts* (exts σ) ⟫ (rename (ext* {Σ = Σ} (S_ {A = B})) N) ≡ rename (ext* S_) (⟪ exts* σ ⟫ N)
subst-shift-weaken {N = ` v} = subst-shift-weaken-var {v = v}
subst-shift-weaken {N = ⋆} = refl
subst-shift-weaken {N = ƛ N} {σ = σ} = cong ƛ_ (subst-shift-weaken {N = N} {σ = σ})
subst-shift-weaken {N = a · b} {σ = σ} = cong₂ _·_ (subst-shift-weaken {N = a} {σ = σ}) (subst-shift-weaken {N = b} {σ = σ})
subst-shift-weaken {N = ⟨ a , b ⟩} {σ = σ} = cong₂ ⟨_,_⟩ (subst-shift-weaken {N = a} {σ = σ}) (subst-shift-weaken {N = b} {σ = σ})
subst-shift-weaken {N = proj _ N} {σ = σ} = cong (proj _) (subst-shift-weaken {N = N} {σ = σ})
subst-shift-weaken {N = [ iso ]≡ N} {σ = σ} = cong ([ iso ]≡_) (subst-shift-weaken {N = N} {σ = σ})

subst-split-var : ∀{Γ Δ Δ₁ Σ A B}{v : (Γ , A) ,* Σ ∋ B}{M : Δ₁ ⊢ A}{σ : Subst Γ Δ}{ρ : Rename Δ Δ₁}
    → exts* (M • (⟪ ids ∘ ρ ⟫ ∘ σ)) v ≡ ⟪ exts* (M • (ids ∘ ρ)) ⟫ (exts* (exts σ) v)
subst-split-var {Σ = ∅} {v = Z} = refl
subst-split-var {Σ = ∅} {v = S v} {σ = σ} {ρ = ρ} = sym (subst-weaken {N = σ v} {σ = ids ∘ ρ})
subst-split-var {Σ = Σ , _} {v = Z} = refl
subst-split-var {Σ = Σ , _} {v = S v} {M = M} {σ = σ} {ρ = ρ} =
  trans
    (cong (rename S_) (subst-split-var {v = v} {σ = σ}))
    (sym (subst-shift-weaken {Σ = ∅} {N = exts* (exts σ) v}))

subst-split : ∀{Γ Δ Δ₁ Σ A B}{N : (Γ , A) ,* Σ ⊢ B}{M : Δ₁ ⊢ A}{σ : Subst Γ Δ}{ρ : Rename Δ Δ₁}
    → ⟪ exts* (M • (⟪ ids ∘ ρ ⟫ ∘ σ)) ⟫ N ≡ ⟪ exts* (M • (ids ∘ ρ)) ⟫ (⟪ exts* (exts σ) ⟫ N)
subst-split {N = ` v} = subst-split-var {v = v}
subst-split {N = ⋆} = refl
subst-split {N = ƛ n} {σ = σ} {ρ = ρ} = cong ƛ_ (subst-split {N = n} {σ = σ} {ρ = ρ})
subst-split {N = a · b} {σ = σ} {ρ = ρ} = cong₂ _·_ (subst-split {N = a} {σ = σ} {ρ = ρ}) (subst-split {N = b} {σ = σ} {ρ = ρ})
subst-split {N = ⟨ a , b ⟩} {σ = σ} {ρ = ρ} = cong₂ ⟨_,_⟩ (subst-split {N = a} {σ = σ} {ρ = ρ}) (subst-split {N = b} {σ = σ} {ρ = ρ})
subst-split {N = proj _ N} {σ = σ} {ρ = ρ} = cong (proj _) (subst-split {N = N} {σ = σ} {ρ = ρ})
subst-split {N = [ iso ]≡ N} {σ = σ} {ρ = ρ} = cong ([ iso ]≡_) (subst-split {N = N} {σ = σ} {ρ = ρ})

rename-subst-var : ∀{Γ Δ Δ′ Σ A B}{v : (Γ , B) ,* Σ ∋ A}{N : Δ′ ⊢ B}{ρ : Rename Γ Δ}{σ : Subst Δ Δ′}
    → exts* (N • σ) (ext* (ext ρ) v) ≡ exts* (N • (σ ∘ ρ)) v
rename-subst-var {Σ = ∅} {v = Z} = refl
rename-subst-var {Σ = ∅} {v = S v} = refl
rename-subst-var {Σ = Σ , _} {v = Z} = refl
rename-subst-var {Σ = Σ , _} {v = S v} = cong (rename S_) (rename-subst-var {v = v})


rename-subst : ∀{Γ Δ Δ′ Σ A B}{M : (Γ , B) ,* Σ ⊢ A}{N : Δ′ ⊢ B}{ρ : Rename Γ Δ}{σ : Subst Δ Δ′}
    → ⟪ exts* (N • σ) ⟫ (rename (ext* (ext ρ)) M) ≡ ⟪ exts* (N • (σ ∘ ρ)) ⟫ M
rename-subst {M = ` v} = rename-subst-var {v = v}
rename-subst {M = ⋆} = refl
rename-subst {M = ƛ n} {ρ = ρ} {σ = σ} = cong ƛ_ (rename-subst {M = n} {ρ = ρ} {σ = σ})
rename-subst {M = a · b} {ρ = ρ} {σ = σ} = cong₂ _·_ (rename-subst {M = a} {ρ = ρ} {σ = σ}) (rename-subst {M = b} {ρ = ρ} {σ = σ})
rename-subst {M = ⟨ a , b ⟩} {ρ = ρ} {σ = σ} = cong₂ ⟨_,_⟩ (rename-subst {M = a} {ρ = ρ} {σ = σ}) (rename-subst {M = b} {ρ = ρ} {σ = σ})
rename-subst {M = proj _ n} {ρ = ρ} {σ = σ} = cong (proj _) (rename-subst {M = n} {ρ = ρ} {σ = σ})
rename-subst {M = [ iso ]≡ n} {ρ = ρ} {σ = σ} = cong ([ iso ]≡_) (rename-subst {M = n} {ρ = ρ} {σ = σ})

rename-subst-commute-var : ∀{Γ Δ Σ A B}{v : (Γ , A) ,* Σ ∋ B}{M : Γ ⊢ A}{ρ : Rename Γ Δ}
    → rename (ext* ρ) (exts* (M • ids) v) ≡ exts* ((rename ρ M) • ids) ((ext* (ext ρ) v))
rename-subst-commute-var {Σ = ∅} {v = Z} = refl
rename-subst-commute-var {Σ = ∅} {v = S v} = refl
rename-subst-commute-var {Σ = Σ , _} {v = Z} = refl
rename-subst-commute-var {Σ = Σ , _} {v = S v} {M = M} {ρ = ρ} =
  trans
    (rename-shift-weaken {Σ = ∅} {N = exts* (M • ids) v})
    (cong (rename S_) (rename-subst-commute-var {v = v}))

rename-subst-commute : ∀{Γ Δ Σ A B}{N : (Γ , A) ,* Σ ⊢ B}{M : Γ ⊢ A}{ρ : Rename Γ Δ}
    → rename (ext* ρ) (⟪ exts* (M • ids) ⟫ N) ≡ ⟪ exts* ((rename ρ M) • ids) ⟫ (rename (ext* (ext ρ)) N)
rename-subst-commute {N = ` v} = rename-subst-commute-var {v = v}
rename-subst-commute {N = ⋆} = refl
rename-subst-commute {N = ƛ N} {ρ = ρ} = cong ƛ_ (rename-subst-commute {N = N} {ρ = ρ})
rename-subst-commute {N = a · b} {ρ = ρ} = cong₂ _·_ (rename-subst-commute {N = a} {ρ = ρ}) (rename-subst-commute {N = b} {ρ = ρ})
rename-subst-commute {N = ⟨ a , b ⟩} {ρ = ρ} = cong₂ ⟨_,_⟩ (rename-subst-commute {N = a} {ρ = ρ}) (rename-subst-commute {N = b} {ρ = ρ})
rename-subst-commute {N = proj _ N} {ρ = ρ} = cong (proj _) (rename-subst-commute {N = N} {ρ = ρ})
rename-subst-commute {N = [ iso ]≡ N} {ρ = ρ} = cong ([ iso ]≡_) (rename-subst-commute {N = N} {ρ = ρ})

subst-commute-var : ∀{Γ Δ Σ A B}{v : (Γ , B) ,* Σ ∋ A}{M : Γ ⊢ B}{σ : Subst Γ Δ}
    → ⟪ exts* (⟪ σ ⟫ M • ids) ⟫ (exts* (exts σ) v) ≡ ⟪ exts* σ ⟫ (exts* (M • ids) v)
subst-commute-var {Σ = ∅} {v = Z} = refl
subst-commute-var {Σ = ∅} {v = S v} {M = M} {σ = σ} =
  trans
    (subst-weaken {Σ = ∅} {N = σ v} {M = ⟪ σ ⟫ M} {σ = ids})
    (sub-id {Σ = ∅} {N = σ v})
subst-commute-var {Σ = Σ , _} {v = Z} = refl
subst-commute-var {Σ = Σ , _} {v = S v} {M = M} {σ = σ} =
  trans
    (subst-shift-weaken {Σ = ∅} {N = exts* (exts σ) v} {σ = exts* (⟪ σ ⟫ M • ids)})
    (trans
      (cong (rename S_) (subst-commute-var {v = v} {M = M} {σ = σ}))
      (sym (subst-shift-weaken {Σ = ∅} {N = exts* (M • ids) v} {σ = exts* σ})))

subst-commute : ∀{Γ Δ Σ A B}{N : (Γ , B) ,* Σ ⊢ A}{M : Γ ⊢ B}{σ : Subst Γ Δ}
    → ⟪ exts* (⟪ σ ⟫ M • ids) ⟫ (⟪ exts* (exts σ) ⟫ N) ≡ ⟪ exts* σ ⟫ (⟪ exts* (M • ids) ⟫ N)
subst-commute {N = ` v} = subst-commute-var {v = v}
subst-commute {N = ⋆} = refl
subst-commute {N = ƛ N} {σ = σ} = cong ƛ_ (subst-commute {N = N} {σ = σ})
subst-commute {N = a · b} {σ = σ} = cong₂ _·_ (subst-commute {N = a} {σ = σ}) (subst-commute {N = b} {σ = σ})
subst-commute {N = ⟨ a , b ⟩} {σ = σ} = cong₂ ⟨_,_⟩ (subst-commute {N = a} {σ = σ}) (subst-commute {N = b} {σ = σ})
subst-commute {N = proj _ N} {σ = σ} = cong (proj _) (subst-commute {N = N} {σ = σ})
subst-commute {N = [ iso ]≡ N} {σ = σ} = cong ([ iso ]≡_) (subst-commute {N = N} {σ = σ})

Z-weaken-var : ∀{Γ Σ A B}{v : (Γ , B) ,* Σ ∋ A}
    → exts* (` Z • ids ∘ S_) v ≡ ` v
Z-weaken-var {Σ = ∅} {v = Z} = refl
Z-weaken-var {Σ = ∅} {v = S v} = refl
Z-weaken-var {Σ = _ , _} {v = Z} = refl
Z-weaken-var {Σ = _ , _} {v = S v} = cong (rename S_) (Z-weaken-var {v = v})

Z-weaken : ∀{Γ Σ A B}{N : (Γ , B) ,* Σ ⊢ A}
    → ⟪ exts* (` Z • ids ∘ S_) ⟫ N ≡ N
Z-weaken {N = ` v} = Z-weaken-var {v = v}
Z-weaken {N = ⋆} = refl
Z-weaken {N = ƛ N}  = cong ƛ_ (Z-weaken {Σ = _ , _} {N = N} )
Z-weaken {N = a · b}  = cong₂ _·_ (Z-weaken {N = a} ) (Z-weaken {N = b} )
Z-weaken {N = ⟨ a , b ⟩}  = cong₂ ⟨_,_⟩ (Z-weaken {N = a} ) (Z-weaken {N = b} )
Z-weaken {N = proj _ N}  = cong (proj _) (Z-weaken {N = N} )
Z-weaken {N = [ iso ]≡ N}  = cong ([ iso ]≡_) (Z-weaken {N = N} )


open import IsoType renaming (_≡_ to _≡T_) hiding (sym)
open import Type using (_×_; _⇒_)
open import Data.Sum using (inj₁; inj₂)

σ-cong⇒₁ : ∀ {Γ A B} → (iso : B ≡T A) → Subst (Γ , A) (Γ , B)
σ-cong⇒₁ iso = [ iso ]≡ (` Z) • (ids ∘ S_)

subst-cong⇒₁-commute-var : ∀{Γ Δ Σ A B C}{v : (Γ , A) ,* Σ ∋ C}{σ : Subst Γ Δ}{iso : B ≡T A}
    → ⟪ exts* (σ-cong⇒₁ iso) ⟫ (exts* (exts σ) v) ≡ ⟪ exts* (exts σ) ⟫ (exts* (σ-cong⇒₁ iso) v)
subst-cong⇒₁-commute-var {Σ = ∅} {v = Z} = refl
subst-cong⇒₁-commute-var {Σ = ∅} {v = S v} {σ = σ} =
  trans
    (subst-weaken {Σ = ∅} {N = σ v})
    (rename-subst-ids {Σ = ∅})
subst-cong⇒₁-commute-var {Σ = Σ , _} {v = Z} = refl
subst-cong⇒₁-commute-var {Σ = Σ , _} {v = S v} {σ = σ} {iso = iso} =
  trans
    (subst-shift-weaken {Σ = ∅} {N = exts* (exts σ) v})
    (trans
      (cong (rename S_) (subst-cong⇒₁-commute-var {v = v}))
      (sym (subst-shift-weaken {Σ = ∅} {N = exts* (σ-cong⇒₁ iso) v})))

subst-cong⇒₁-commute : ∀{Γ Δ Σ A B C}{N : (Γ , A) ,* Σ ⊢ C}{σ : Subst Γ Δ}{iso : B ≡T A}
    → ⟪ exts* (σ-cong⇒₁ iso) ⟫ (⟪ exts* (exts σ) ⟫ N) ≡ ⟪ exts* (exts σ) ⟫ (⟪ exts* (σ-cong⇒₁ iso) ⟫ N)
subst-cong⇒₁-commute {N = ` v} = subst-cong⇒₁-commute-var {v = v}
subst-cong⇒₁-commute {N = ⋆} = refl
subst-cong⇒₁-commute {N = ƛ N} {σ = σ} = cong ƛ_ (subst-cong⇒₁-commute {Σ = _ , _} {N = N} {σ = σ})
subst-cong⇒₁-commute {N = a · b} {σ = σ} = cong₂ _·_ (subst-cong⇒₁-commute {N = a} {σ = σ}) (subst-cong⇒₁-commute {N = b} {σ = σ})
subst-cong⇒₁-commute {N = ⟨ a , b ⟩} {σ = σ} = cong₂ ⟨_,_⟩ (subst-cong⇒₁-commute {N = a} {σ = σ}) (subst-cong⇒₁-commute {N = b} {σ = σ})
subst-cong⇒₁-commute {N = proj _ N} {σ = σ} = cong (proj _) (subst-cong⇒₁-commute {N = N} {σ = σ})
subst-cong⇒₁-commute {N = [ iso ]≡ N} {σ = σ} = cong ([ iso ]≡_) (subst-cong⇒₁-commute {N = N} {σ = σ})

σ-uncurry : ∀ {Γ A B} → Subst (Γ , A × B) (Γ , A , B)
σ-uncurry = ⟨ (` (S Z)) , (` Z) ⟩ • λ x → ` (S (S x))

rename-split-var : ∀{Γ Σ A B C}{v : Γ ,* Σ ∋ A}
    → (ext* {Σ = Σ} (S_ {A = C}) (ext* (S_ {A = B}) v)) ≡ (ext* (λ x → S (S x)) v)
rename-split-var {Σ = ∅} = refl
rename-split-var {Σ = _ , _} {v =  Z} = refl
rename-split-var {Σ = _ , _} {v = (S v)} = cong S_ (rename-split-var {v = v})

rename-split : ∀{Γ Σ A B C}{N : Γ ,* Σ ⊢ A}
    → rename (ext* {Σ = Σ} (S_ {A = C})) (rename (ext* (S_ {A = B})) N) ≡ rename (ext* (λ x → S (S x))) N
rename-split {N = ` v} = cong `_ rename-split-var
rename-split {N = ⋆} = refl
rename-split {N = [ iso ]≡ N} = cong ([ iso ]≡_) (rename-split {N = N})
rename-split {N = ƛ N} = cong ƛ_ (rename-split {Σ = _ , _} {N = N})
rename-split {N = a · b} = cong₂ _·_ (rename-split {N = a}) (rename-split {N = b})
rename-split {N = ⟨ a , b ⟩} = cong₂ ⟨_,_⟩ (rename-split {N = a}) (rename-split {N = b})
rename-split {N = proj _ N} = cong (proj _) (rename-split {N = N})

subst-uncurry-commute-var : ∀{Γ Δ Σ A B C}{v : (Γ , A × B) ,* Σ ∋ C}{σ : Subst Γ Δ}
    → ⟪ exts* {Σ = Σ} (σ-uncurry) ⟫ (exts* (exts σ) v) ≡ ⟪ exts* (exts (exts σ)) ⟫ (exts* (σ-uncurry) v)
subst-uncurry-commute-var {Σ = ∅} {v = Z} = refl
subst-uncurry-commute-var {Σ = ∅} {v = S v} {σ = σ} =
  trans
    (subst-weaken {Σ = ∅} {N = σ v})
    (trans (rename-subst-ids {Σ = ∅} {N = σ v}) (sym (rename-split {Σ = ∅} {N = σ v})))
subst-uncurry-commute-var {Σ = Σ , x} {v = Z} = refl
subst-uncurry-commute-var {Σ = Σ , x} {v = S v} {σ = σ} =
  trans
    (subst-shift-weaken {Σ = ∅} {N = exts* (exts σ) v})
    (trans
      (cong (rename S_) (subst-uncurry-commute-var {v = v}))
      (sym (subst-shift-weaken {Σ = ∅} {N = exts* σ-uncurry v})))

subst-uncurry-commute : ∀{Γ Δ Σ A B C}{N : (Γ , A × B) ,* Σ ⊢ C}{σ : Subst Γ Δ}
    → ⟪ exts* {Σ = Σ} (σ-uncurry) ⟫ (⟪ exts* (exts σ) ⟫ N) ≡ ⟪ exts* (exts (exts σ)) ⟫ (⟪ exts* (σ-uncurry) ⟫ N)
subst-uncurry-commute {N = ` v} = subst-uncurry-commute-var {v = v}
subst-uncurry-commute {N = ⋆} = refl
subst-uncurry-commute {N = [ iso ]≡ N} = cong [ iso ]≡_ (subst-uncurry-commute {N = N})
subst-uncurry-commute {N = ƛ N} = cong ƛ_ (subst-uncurry-commute {Σ = _ , _} {N = N})
subst-uncurry-commute {N = a · b} = cong₂ _·_ (subst-uncurry-commute {N = a}) (subst-uncurry-commute {N = b})
subst-uncurry-commute {N = ⟨ a , b ⟩} = cong₂ ⟨_,_⟩ (subst-uncurry-commute {N = a}) (subst-uncurry-commute {N = b})
subst-uncurry-commute {N = proj _ N} = cong (proj _) (subst-uncurry-commute {N = N})

σ-curry : ∀ {Γ A B} → Subst (Γ , A , B) (Γ , A × B)
σ-curry {A = A}{B = B} = proj B {inj₂ refl} (` Z) • proj A {inj₁ refl} (` Z) • ids ∘ S_

subst-curry-commute-var : ∀{Γ Δ Σ A B C}{v : (Γ , A , B) ,* Σ ∋ C}{σ : Subst Γ Δ}
    → ⟪ exts* {Σ = Σ} σ-curry ⟫ (exts* (exts (exts σ)) v) ≡ ⟪ exts* (exts σ) ⟫ (exts* σ-curry v)
subst-curry-commute-var {Σ = ∅} {v = Z} = refl
subst-curry-commute-var {Σ = ∅} {v = S Z} = refl
subst-curry-commute-var {Σ = ∅} {v = S (S v)} {σ = σ} =
  trans
    (subst-weaken {Σ = ∅} {N = rename S_ (σ v)})
    (trans (subst-weaken {Σ = ∅} {N = σ v}) (rename-subst-ids {Σ = ∅} {N = σ v}))
subst-curry-commute-var {Σ = Σ , x} {v = Z} = refl
subst-curry-commute-var {Σ = Σ , x} {v = S v} {σ = σ} =
  trans
    (subst-shift-weaken {Σ = ∅} {N = exts* (exts (exts σ)) v})
    (trans
      (cong (rename S_) (subst-curry-commute-var {v = v}))
      (sym (subst-shift-weaken {Σ = ∅} {N = exts* σ-curry v})))

subst-curry-commute : ∀{Γ Δ Σ A B C}{N : (Γ , A , B) ,* Σ ⊢ C}{σ : Subst Γ Δ}
    → ⟪ exts* {Σ = Σ} σ-curry ⟫ (⟪ exts* (exts (exts σ)) ⟫ N) ≡ ⟪ exts* (exts σ) ⟫ (⟪ exts* σ-curry ⟫ N)
subst-curry-commute {N = ` v} = subst-curry-commute-var {v = v}
subst-curry-commute {N = ⋆} = refl
subst-curry-commute {N = [ iso ]≡ N} = cong [ iso ]≡_ (subst-curry-commute {N = N})
subst-curry-commute {N = ƛ N} = cong ƛ_ (subst-curry-commute {Σ = _ , _} {N = N})
subst-curry-commute {N = a · b} = cong₂ _·_ (subst-curry-commute {N = a}) (subst-curry-commute {N = b})
subst-curry-commute {N = ⟨ a , b ⟩} = cong₂ ⟨_,_⟩ (subst-curry-commute {N = a}) (subst-curry-commute {N = b})
subst-curry-commute {N = proj _ N} = cong (proj _) (subst-curry-commute {N = N})

subst-curryη-commute : ∀{Γ Δ A B C}{N : Γ , A ⊢ B ⇒ C}{σ : Subst Γ Δ}
    → ⟪ σ-curry {B = B} ⟫ (rename S_ (⟪ exts σ ⟫ N)) ≡ ⟪ exts σ ⟫ (⟪ σ-curry ⟫ (rename S_ N))
subst-curryη-commute {B = B} {N = N} {σ = σ}
  rewrite sym (subst-shift-weaken {Σ = ∅} {B = B} {N = N} {σ = exts σ})
    = subst-curry-commute {Σ = ∅} {N = rename S_ N} {σ = σ}


exts-ext-var : ∀ {Γ Δ Σ}{A B}{v : (Γ , B) ,* Σ ∋ A}{ρ : Rename Γ Δ}
        → ` ((ext* (ext ρ)) v) ≡ exts* (exts (ids ∘ ρ)) v
exts-ext-var {Σ = ∅} {v = Z} = refl
exts-ext-var {Σ = ∅} {v = S v} = refl
exts-ext-var {Σ = _ , _} {v = Z} = refl
exts-ext-var {Σ = _ , _} {v = S v} = cong (rename S_) (exts-ext-var {v = v})

exts-ext : ∀ {Γ Δ Σ}{A B}{N : (Γ , B) ,* Σ ⊢ A}{ρ : Rename Γ Δ}
        → rename (ext* (ext ρ)) N ≡ ⟪ exts* (exts (ids ∘ ρ)) ⟫ N
exts-ext {N = ` v} = exts-ext-var {v = v}
exts-ext {N = ⋆} = refl
exts-ext {N = [ iso ]≡ N} = cong [ iso ]≡_ (exts-ext {N = N})
exts-ext {N = ƛ N} = cong ƛ_ (exts-ext {Σ = _ , _} {N = N})
exts-ext {N = a · b} = cong₂ _·_ (exts-ext {N = a}) (exts-ext {N = b})
exts-ext {N = ⟨ a , b ⟩} = cong₂ ⟨_,_⟩ (exts-ext {N = a}) (exts-ext {N = b})
exts-ext {N = proj _ N} = cong (proj _) (exts-ext {N = N})

rename-cong⇒₁-commute : ∀{Γ Δ A B C}{N : Γ , A ⊢ C}{ρ : Rename Γ Δ}{iso : B ≡T A}
    → ⟪ σ-cong⇒₁ iso ⟫ (rename (ext ρ) N) ≡ rename (ext ρ) (⟪ σ-cong⇒₁ iso ⟫ N)
rename-cong⇒₁-commute {N = N} {ρ = ρ} {iso = iso}
  rewrite exts-ext {Σ = ∅} {N = N} {ρ = ρ} | exts-ext {Σ = ∅} {N = ⟪ σ-cong⇒₁ iso ⟫ N} {ρ = ρ}
    = subst-cong⇒₁-commute {Σ = ∅} {N = N} {σ = ids ∘ ρ}

rename-uncurry-commute : ∀{Γ Δ A B C}{N : Γ , A × B ⊢ C}{ρ : Rename Γ Δ}
    → ⟪ σ-uncurry ⟫ (rename (ext ρ) N) ≡ rename (ext (ext ρ)) (⟪ σ-uncurry ⟫ N)
rename-uncurry-commute {N = N} {ρ = ρ}
  rewrite exts-ext {Σ = ∅} {N = N} {ρ = ρ} | exts-ext {Σ = ∅ , _} {N = ⟪ σ-uncurry ⟫ N} {ρ = ρ}
    = subst-uncurry-commute {Σ = ∅} {N = N} {σ = ids ∘ ρ}

rename-curry-commute : ∀{Γ Δ A B C}{N : Γ , A , B ⊢ C}{ρ : Rename Γ Δ}
    → ⟪ σ-curry ⟫ (rename (ext (ext ρ)) N) ≡ rename (ext ρ) (⟪ σ-curry ⟫ N)
rename-curry-commute {N = N} {ρ = ρ}
  rewrite exts-ext {Σ = ∅ , _} {N = N} {ρ = ρ} | exts-ext {Σ = ∅} {N = ⟪ σ-curry ⟫ N} {ρ = ρ}
    = subst-curry-commute {Σ = ∅} {N = N} {σ = ids ∘ ρ}

rename-curryη-commute : ∀{Γ Δ A B C}{N : Γ , A ⊢ B ⇒ C}{ρ : Rename Γ Δ}
    → ⟪ σ-curry {B = B} ⟫ (rename S_ (rename (ext ρ) N)) ≡ rename (ext ρ) (⟪ σ-curry ⟫ (rename S_ N))
rename-curryη-commute {B = B} {N = N} {ρ = ρ}
  rewrite exts-ext {Σ = ∅} {N = N} {ρ = ρ} | exts-ext {Σ = ∅} {N = ⟪ σ-curry {B = B} ⟫ (rename S_ N)} {ρ = ρ}
    = subst-curryη-commute {N = N} {σ = ids ∘ ρ}


subst-curry-split-var : ∀{Γ Δ Σ A B C}{v : (Γ , A , B) ,* Σ ∋ C}{u : Δ ⊢ A × B}{ρ : Rename Γ Δ}
    → ⟪ exts* (proj B {inj₂ refl} u • ids) ⟫ (⟪ exts* (exts (proj A {inj₁ refl} u • ids ∘ ρ)) ⟫ (` v)) ≡ ⟪ exts* (u • ids ∘ ρ) ⟫ (⟪ exts* σ-curry ⟫ (` v))
subst-curry-split-var {Σ = ∅} {v = Z} = refl
subst-curry-split-var {Σ = ∅} {A = A} {v = S Z}{u} =
  cong (proj A) (trans (subst-weaken {Σ = ∅} {N = u}) (sub-id {Σ = ∅} {N = u}))
subst-curry-split-var {Σ = ∅} {A = A} {v = S (S v)} = refl
subst-curry-split-var {Σ = _ , _} {v = Z} = refl
subst-curry-split-var {Σ = _ , _} {A = A} {v = S v}{u}{ρ} =
  trans
    (subst-shift-weaken {Σ = ∅} {N = exts* (exts (proj A u • ids ∘ ρ)) v})
    (trans
      (cong (rename S_) (subst-curry-split-var {v = v}))
      (sym (subst-shift-weaken {Σ = ∅} {N = ⟪ exts* σ-curry ⟫ (` v)})))


subst-curry-split : ∀{Γ Δ Σ A B C}{N : (Γ , A , B) ,* Σ ⊢ C}{u : Δ ⊢ A × B}{ρ : Rename Γ Δ}
    → ⟪ exts* (proj B {inj₂ refl} u • ids) ⟫ (⟪ exts* (exts (proj A {inj₁ refl} u • ids ∘ ρ)) ⟫ N) ≡ ⟪ exts* (u • ids ∘ ρ) ⟫ (⟪ exts* σ-curry ⟫ N)
subst-curry-split {N = ` v} = subst-curry-split-var {v = v}
subst-curry-split {N = ⋆} = refl
subst-curry-split {N = [ iso ]≡ N} = cong [ iso ]≡_ (subst-curry-split {N = N})
subst-curry-split {N = ƛ N} = cong ƛ_ (subst-curry-split {Σ = _ , _} {N = N})
subst-curry-split {N = a · b} = cong₂ _·_ (subst-curry-split {N = a}) (subst-curry-split {N = b})
subst-curry-split {N = ⟨ a , b ⟩} = cong₂ ⟨_,_⟩ (subst-curry-split {N = a}) (subst-curry-split {N = b})
subst-curry-split {N = proj _ N} = cong (proj _) (subst-curry-split {N = N})

subst-curry-split2 : ∀{Γ A B C}{N : Γ , A , B ⊢ C}
    → ⟪ proj B {inj₂ refl} (` Z) • ids ⟫ (⟪ exts (proj A {inj₁ refl} (` Z) • ids ∘ S_) ⟫ N) ≡ ⟪ σ-curry ⟫ N
subst-curry-split2 {N = N} = trans (subst-curry-split {Σ = ∅} {N = N} {u = ` Z} {ρ = S_}) (Z-weaken {Σ = ∅} {N = ⟪ σ-curry ⟫ N})

subst-shift-curry-split : ∀{Γ Δ A B C}{N : Γ , A ⊢ C}{u : Δ ⊢ A × B}{ρ : Rename Γ Δ}
    → ⟪ proj A {inj₁ refl} u • ids ∘ ρ ⟫ N ≡ ⟪ (u • ids ∘ ρ) ⟫ (⟪ σ-curry ⟫ (rename S_ N))
subst-shift-curry-split {A = A}{B = B}{N = N}{u}{ρ} =
  trans
    (sym (trans
      (cong (⟪ proj B u • ids ⟫) (subst-shift-weaken {Σ = ∅} {N = N}))
      (trans
        (subst-weaken {Σ = ∅} {N = ⟪ proj A u • ids ∘ ρ ⟫ N})
        (sub-id {Σ = ∅} {N = ⟪ proj A u • ids ∘ ρ ⟫ N}))))
    (subst-curry-split {Σ = ∅} {N = rename S_ N} {u} {ρ})

subst-cong⇒₁-split-var : ∀{Γ Δ Σ A B C}{v : (Γ , A) ,* Σ ∋ C}{iso : B ≡T A}{u : Δ ⊢ B}{ρ : Rename Γ Δ}
    → ⟪ exts* (u • ids ∘ ρ) ⟫ (⟪ exts* (σ-cong⇒₁ iso) ⟫ (` v)) ≡ ⟪ exts* (([ iso ]≡ u) • ids ∘ ρ) ⟫ (` v)
subst-cong⇒₁-split-var {Σ = ∅} {v = Z} = refl
subst-cong⇒₁-split-var {Σ = ∅} {v = S v} = refl
subst-cong⇒₁-split-var {Σ = Σ , x} {v = Z} = refl
subst-cong⇒₁-split-var {Σ = Σ , x} {v = S v} {iso = iso} =
  trans
    (subst-shift-weaken {Σ = ∅} {N = exts* (σ-cong⇒₁ iso) v})
    (cong (rename S_) (subst-cong⇒₁-split-var {v = v}))

subst-cong⇒₁-split : ∀{Γ Δ Σ A B C}{N : (Γ , A) ,* Σ ⊢ C}{iso : B ≡T A}{u : Δ ⊢ B}{ρ : Rename Γ Δ}
    → ⟪ exts* (u • ids ∘ ρ) ⟫ (⟪ exts* (σ-cong⇒₁ iso) ⟫ N) ≡ ⟪ exts* (([ iso ]≡ u) • ids ∘ ρ) ⟫ N
subst-cong⇒₁-split {N = ` v} = subst-cong⇒₁-split-var {v = v}
subst-cong⇒₁-split {N = ⋆} = refl
subst-cong⇒₁-split {N = [ iso ]≡ N} = cong [ iso ]≡_ (subst-cong⇒₁-split {N = N})
subst-cong⇒₁-split {N = ƛ N} = cong ƛ_ (subst-cong⇒₁-split {Σ = _ , _} {N = N})
subst-cong⇒₁-split {N = a · b} = cong₂ _·_ (subst-cong⇒₁-split {N = a}) (subst-cong⇒₁-split {N = b})
subst-cong⇒₁-split {N = ⟨ a , b ⟩} = cong₂ ⟨_,_⟩ (subst-cong⇒₁-split {N = a}) (subst-cong⇒₁-split {N = b})
subst-cong⇒₁-split {N = proj _ N} = cong (proj _) (subst-cong⇒₁-split {N = N})


subst-uncurry-split2-var : ∀{Γ Δ Δ₁ Σ A B C}{v : (Γ , A × B) ,* Σ ∋ C}{u : Δ ⊢ A}{u₁ : Δ₁ ⊢ B}{ρ : Rename Γ Δ}{ρ₁ : Rename Δ Δ₁}
    → ⟪ exts* (u₁ • ids ∘ ρ₁) ⟫ (⟪ exts* (exts (u • ids ∘ ρ)) ⟫ (exts* σ-uncurry v)) ≡ exts* (⟨ rename ρ₁ u , u₁ ⟩ • ids ∘ ρ₁ ∘ ρ) v
subst-uncurry-split2-var {Σ = ∅} {v = Z} {u = u} = cong₂ ⟨_,_⟩ (trans (subst-weaken {Σ = ∅} {N = u}) (rename-subst-ids {Σ = ∅})) refl
subst-uncurry-split2-var {Σ = ∅} {v = S v} = refl
subst-uncurry-split2-var {Σ = _ , _} {v = Z} = refl
subst-uncurry-split2-var {Σ = _ , _} {v = S v}{u}{u₁}{ρ}{ρ₁} =
  trans
    (cong (⟪ exts (exts* (u₁ • ids ∘ ρ₁)) ⟫) (subst-shift-weaken {Σ = ∅} {N = exts* σ-uncurry v}))
    (trans
      (subst-shift-weaken {Σ = ∅} {N = ⟪ exts* (exts (u • ids ∘ ρ)) ⟫ (exts* σ-uncurry v)})
      (cong (rename S_) (subst-uncurry-split2-var {v = v})))

subst-uncurry-split2 : ∀{Γ Δ Δ₁ Σ A B C}{N : (Γ , A × B) ,* Σ ⊢ C}{u : Δ ⊢ A}{u₁ : Δ₁ ⊢ B}{ρ : Rename Γ Δ}{ρ₁ : Rename Δ Δ₁}
    → ⟪ exts* (u₁ • ids ∘ ρ₁) ⟫ (⟪ exts* (exts (u • ids ∘ ρ)) ⟫ (⟪ exts* σ-uncurry ⟫ N)) ≡ ⟪ exts* (⟨ rename ρ₁ u , u₁ ⟩ • ids ∘ ρ₁ ∘ ρ) ⟫ N
subst-uncurry-split2 {N = ` v} = subst-uncurry-split2-var {v = v}
subst-uncurry-split2 {N = ⋆} = refl
subst-uncurry-split2 {N = [ iso ]≡ N} = cong [ iso ]≡_ (subst-uncurry-split2 {N = N})
subst-uncurry-split2 {N = ƛ N} = cong ƛ_ (subst-uncurry-split2 {Σ = _ , _} {N = N})
subst-uncurry-split2 {N = a · b} = cong₂ _·_ (subst-uncurry-split2 {N = a}) (subst-uncurry-split2 {N = b})
subst-uncurry-split2 {N = ⟨ a , b ⟩} = cong₂ ⟨_,_⟩ (subst-uncurry-split2 {N = a}) (subst-uncurry-split2 {N = b})
subst-uncurry-split2 {N = proj _ N} = cong (proj _) (subst-uncurry-split2 {N = N})

subst-shift-uncurry-split : ∀{Γ Δ A B C}{N : Γ , A × B ⊢ C}{u : Δ ⊢ A}{ρ : Rename Γ Δ}
    → ⟪ exts (u • ids ∘ ρ) ⟫ (⟪ σ-uncurry ⟫ N) ≡ ⟪ ⟨ rename S_ u , ` Z ⟩ • ids ∘ (λ x → (S ρ x)) ⟫ N
subst-shift-uncurry-split {N = N} {u = u} {ρ = ρ} = trans (sym (Z-weaken {Σ = ∅})) (subst-uncurry-split2 {Σ = ∅} {N = N} {u = u} {u₁ = ` Z} {ρ = ρ} {ρ₁ = S_})

subst-uncurry-split : ∀{Γ Δ A B C}{N : Γ , A × B ⊢ C}{u : Δ ⊢ B}{ρ : Rename (Γ , A) Δ}
    → ⟪ u • ids ∘ ρ ⟫ (⟪ σ-uncurry ⟫ N) ≡ ⟪ ⟨ ` ρ Z , u ⟩ • ids ∘ (λ x → ρ (S x)) ⟫ N
subst-uncurry-split {N = N} {u = u} {ρ = ρ} =
  trans
    (cong (⟪ u • ids ∘ ρ ⟫) (sym (Z-weaken {Σ = ∅ , _} {N = ⟪ σ-uncurry ⟫ N})))
    (subst-uncurry-split2 {Σ = ∅} {N = N} {u = ` Z} {u₁ = u} {ρ = S_} {ρ₁ = ρ})