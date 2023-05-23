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