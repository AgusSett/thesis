module StrongNorm where

open import Function.Base using (_∘_; case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; cong₂; refl; sym; trans) renaming (subst to transport)
open import Data.Product using (∃; proj₁; proj₂) renaming (_,_ to ﹙_,_﹚; _×_ to _⊗_)
open import Data.Sum

infix  4 _⊢_
infix  4 _∋_
infixl 5 _,_

infixr 7 _⇒_
infixr 9 _×_

infix  5 ƛ_
infixl 7 _·_
infix  9 `_
infix  9 S_


data Type : Set where
  _⇒_ : Type → Type → Type
  τ   : Type
  ⊤   : Type
  _×_ : Type → Type → Type


data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context


data _∋_ : Context → Type → Set where

  Z : ∀ {Γ A}
      ---------
    → Γ , A ∋ A

  S_ : ∀ {Γ A B}
    → Γ ∋ A
      ---------
    → Γ , B ∋ A


data _⊢_ : Context → Type → Set where

  `_ : ∀ {Γ A}
    → Γ ∋ A
      -----
    → Γ ⊢ A
  
  ⋆ : ∀ {Γ} → Γ ⊢ ⊤

  ƛ_  : ∀ {Γ A B}
    → Γ , A ⊢ B
      ---------
    → Γ ⊢ A ⇒ B

  _·_ : ∀ {Γ A B}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
      ---------
    → Γ ⊢ B
  
  ⟨_,_⟩ : ∀ {Γ A B}
    → Γ ⊢ A
    → Γ ⊢ B
      -----------
    → Γ ⊢ A × B

  proj : ∀ {Γ A B}
    → (C : Type)
    → {proof : (C ≡ A) ⊎ (C ≡ B)}
    → Γ ⊢ A × B 
      -----------
    → Γ ⊢ C


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
rename ρ ⋆ = ⋆
rename ρ ⟨ a , b ⟩ = ⟨ rename ρ a , rename ρ b ⟩
rename ρ (proj _ {p} x) = proj _ {p} (rename ρ x)

exts : ∀ {Γ Δ A}
  → Subst Γ Δ
    ---------------------------------
  → Subst (Γ , A) (Δ , A)
exts σ Z      =  ` Z
exts σ (S x)  =  rename S_ (σ x)

subst : ∀ {Γ Δ}
  → Subst Γ Δ
    -----------------------
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
subst σ (` k)          =  σ k
subst σ (ƛ N)          =  ƛ (subst (exts σ) N)
subst σ (L · M)        =  (subst σ L) · (subst σ M)
subst σ ⋆ = ⋆
subst σ ⟨ a , b ⟩ = ⟨ subst σ a , subst σ b ⟩
subst σ (proj _ {p} x) = proj _ {p} (subst σ x)

⟪_⟫ : ∀{Γ Δ A} → Subst Γ Δ → Γ ⊢ A → Δ ⊢ A
⟪ σ ⟫ = λ M → subst σ M

_[_] : ∀ {Γ A B}
  → Γ , B ⊢ A
  → Γ ⊢ B
    ---------
  → Γ ⊢ A
_[_] {Γ} {A} {B} N M = ⟪ M • ids ⟫ N



infix 2 _↪_

data _↪_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  ξ-·₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
    → L ↪ L′
      ---------------
    → L · M ↪ L′ · M

  ξ-·₂ : ∀ {Γ A B} {V : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A}
    → M ↪ M′
      ---------------
    → V · M ↪ V · M′

  β : ∀ {Γ A B} {N : Γ , A ⊢ B} {W : Γ ⊢ A}
      --------------------
    → (ƛ N) · W ↪ N [ W ]
  
  ζ : ∀ {Γ A B} {L L' : Γ , B ⊢ A}
    → L ↪ L'
      --------------------
    → ƛ L ↪ ƛ L'
  
  ξ-⟨,⟩₁ : ∀ {Γ A B} {M M' : Γ ⊢ A} {N : Γ ⊢ B}
    → M ↪ M'
      -------------------------
    → ⟨ M , N ⟩ ↪ ⟨ M' , N ⟩

  ξ-⟨,⟩₂ : ∀ {Γ A B} {V : Γ ⊢ A} {N N' : Γ ⊢ B}
    → N ↪ N'
      -------------------------
    → ⟨ V , N ⟩ ↪ ⟨ V , N' ⟩

  ξ-proj : ∀ {Γ A B C p} {L L' : Γ ⊢ A × B}
    → L ↪ L'
      ---------------------
    → proj C {p} L ↪ proj C {p} L'

  β-proj₁ : ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
      ----------------------
    → proj A {inj₁ refl} ⟨ V , W ⟩ ↪ V

  β-proj₂ : ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
      ----------------------
    → proj B {inj₂ refl} ⟨ V , W ⟩ ↪ W

{-
  Acá se presentan propiedades de las substitución y los rename.
  Se usa _,*_ para probar una generalización de las propiedades que simplifica el caso del ƛ_
  pero se complica el caso de la variable.
-}

_,*_ : Context → Context → Context
Γ ,* ∅       = Γ
Γ ,* (Δ , A) = (Γ ,* Δ) , A

ext* : ∀ {Γ Δ Σ} → Rename Γ Δ → Rename (Γ ,* Σ) (Δ ,* Σ)
ext* {Σ = ∅}     ρ = ρ
ext* {Σ = _ , _} ρ = ext (ext* ρ)

exts* : ∀ {Γ Δ Σ} → Subst Γ Δ → Subst (Γ ,* Σ) (Δ ,* Σ)
exts* {Σ = ∅}     σ = σ
exts* {Σ = _ , _} σ = exts (exts* σ)

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

rename-shift-weaken-var : ∀{Γ Δ Σ A B}{v : Γ ,* Σ ∋ A}{ρ : Rename Γ Δ}
    → ext* (ext ρ) (ext* {Σ = Σ} (S_ {B = B}) v) ≡ ext* S_ (ext* ρ v)
rename-shift-weaken-var {Σ = ∅} = refl
rename-shift-weaken-var {Σ = Σ , _} {v = Z} = refl
rename-shift-weaken-var {Σ = Σ , _} {v = S v} = cong S_ (rename-shift-weaken-var {v = v})

rename-shift-weaken : ∀{Γ Δ Σ A B}{N : Γ ,* Σ ⊢ A}{ρ : Rename Γ Δ}
    → rename (ext* (ext ρ)) (rename (ext* {Σ = Σ} (S_ {B = B})) N) ≡ rename (ext* S_) (rename (ext* ρ) N)
rename-shift-weaken {N = ` v} = cong `_ (rename-shift-weaken-var  {v = v})
rename-shift-weaken {N = ⋆} = refl
rename-shift-weaken {N = ƛ N} {ρ = ρ} = cong ƛ_ (rename-shift-weaken {N = N} {ρ = ρ})
rename-shift-weaken {N = a · b} {ρ = ρ} = cong₂ _·_ (rename-shift-weaken {N = a} {ρ = ρ}) (rename-shift-weaken {N = b} {ρ = ρ})
rename-shift-weaken {N = ⟨ a , b ⟩} {ρ = ρ} = cong₂ ⟨_,_⟩ (rename-shift-weaken {N = a} {ρ = ρ}) (rename-shift-weaken {N = b} {ρ = ρ})
rename-shift-weaken {N = proj _ N} {ρ = ρ} = cong (proj _) (rename-shift-weaken {N = N} {ρ = ρ})

subst-shift-weaken-var : ∀{Γ Δ Σ A B}{v : Γ ,* Σ ∋ A}{σ : Subst Γ Δ}
    → exts* (exts σ) (ext* {Σ = Σ} (S_ {B = B}) v) ≡ rename (ext* (S_)) (exts* σ v)
subst-shift-weaken-var {Σ = ∅} = refl
subst-shift-weaken-var {Σ = Σ , _} {v = Z} = refl
subst-shift-weaken-var {Σ = Σ , _} {v = S v} {σ = σ} =
  trans
    (cong (rename S_) (subst-shift-weaken-var {v = v}))
    (sym (rename-shift-weaken {Σ = ∅}))

subst-shift-weaken : ∀{Γ Δ Σ A B}{N : Γ ,* Σ ⊢ A}{σ : Subst Γ Δ}
    → ⟪ exts* (exts σ) ⟫ (rename (ext* {Σ = Σ} (S_ {B = B})) N) ≡ rename (ext* S_) (⟪ exts* σ ⟫ N)
subst-shift-weaken {N = ` v} = subst-shift-weaken-var {v = v}
subst-shift-weaken {N = ⋆} = refl
subst-shift-weaken {N = ƛ N} {σ = σ} = cong ƛ_ (subst-shift-weaken {N = N} {σ = σ})
subst-shift-weaken {N = a · b} {σ = σ} = cong₂ _·_ (subst-shift-weaken {N = a} {σ = σ}) (subst-shift-weaken {N = b} {σ = σ})
subst-shift-weaken {N = ⟨ a , b ⟩} {σ = σ} = cong₂ ⟨_,_⟩ (subst-shift-weaken {N = a} {σ = σ}) (subst-shift-weaken {N = b} {σ = σ})
subst-shift-weaken {N = proj _ N} {σ = σ} = cong (proj _) (subst-shift-weaken {N = N} {σ = σ})

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

↪[] : ∀ {Γ Δ A}{t t' : Γ ⊢ A}{σ : Subst Γ Δ} → t ↪ t' → subst σ t ↪ subst σ t'
↪[] (ξ-·₁ step) = ξ-·₁ (↪[] step)
↪[] (ξ-·₂ step) = ξ-·₂ (↪[] step)
↪[] {Δ = Δ} {σ = σ} (β {N = N} {W = W})
  rewrite cong₂ (_↪_) {x = (ƛ subst (exts σ) N) · subst σ W} refl (sym (subst-commute {Σ = ∅} {N = N} {M = W} {σ = σ}))
    = β
↪[] (ζ step) = ζ (↪[] step)
↪[] (ξ-⟨,⟩₁ step) = ξ-⟨,⟩₁ (↪[] step)
↪[] (ξ-⟨,⟩₂ step) = ξ-⟨,⟩₂ (↪[] step)
↪[] (ξ-proj step) = ξ-proj (↪[] step)
↪[] β-proj₁ = β-proj₁
↪[] β-proj₂ = β-proj₂

----------

--- Acá comienza la prueba de strong norm ---

data SN {Γ A} (t : Γ ⊢ A) : Set where
  sn : (∀ {t'} → t ↪ t' → SN t') → SN t

-- Esta definicion es igual a SN pero se agrega una propiedad P que se debe cumplir para t.

data SN* {Γ A} (P : Γ ⊢ A → Set) (t : Γ ⊢ A) : Set where
  sn* : P t → (∀ {t'} → t ↪ t' → SN* P t') → SN* P t


open import Data.Unit using (tt) renaming (⊤ to Top)

{-
  Esta es la propiedad que vamos a usar en SN*
  La principal diferencia con la prueba de reducibility candidates es que predica sobre terminos en lugar
  de tipos y ademas tenemos
    ∀ u → ⟦ u ⟧ → ⟦ t [ u ] ⟧
  en lugar de
    ∀ u → ⟦ u ⟧ → ⟦ t · u ⟧

  Otra particularidad es aparece un rename ρ, ∀ ρ u → ⟦ u ⟧ → ⟦ (rename ρ t) [ u ] ⟧
  esto es necesario para poder hacer la prueba de Γ ⊨ σ → (Γ , A) ⊨ (exts σ), es decir,
  la extensión de una substitución adecuada también es una substitución adecuada.
-}

⟦_⟧ : ∀ {Γ A} → Γ ⊢ A → Set
⟦ (ƛ t) ⟧ = ∀ {Δ}{ρ : Rename _ Δ}{u} → SN* ⟦_⟧ u → SN* ⟦_⟧ (⟪ u • (ids ∘ ρ) ⟫ t)
⟦ ⟨ a , b ⟩ ⟧ = SN* ⟦_⟧ a ⊗ SN* ⟦_⟧ b
⟦ t ⟧ = Top

-- Definición de las substituciónes adecuadas

_⊨_ : ∀{Δ} → (Γ : Context) → (σ : Subst Γ Δ) → Set
Γ ⊨ σ = ∀{A} (v : Γ ∋ A) → SN* ⟦_⟧ (σ {A} v)


SN*-SN : ∀ {Γ A} {t : Γ ⊢ A} → SN* ⟦_⟧ t → SN t
SN*-SN (sn* Lt SNt) = sn (λ step → SN*-SN (SNt step))

{-
  Todo esto es necesario para probar ⊨exts
  El Rename ρ que aparecia en ⟦_⟧ es necesario para probar ⟦⟧-rename, ya que como ocurre en varias partes de
  la prueba, estamos obligados a probar una generalización para poder destrabar algún caso.

  ⊨exts va a ser necesario porque en adequacy (ƛ n) necesitamos SN n, en reducibility candidates no es necesario
  esto ya que usa 'atom' en ∀ u → ⟦ u ⟧ → ⟦ t [ u ] ⟧ para cerrar el termino t.
-}

rename↪ : ∀ {Γ Δ A}{t : Γ ⊢ A}{σ : Rename Γ Δ}{t'} → (rename σ t) ↪ t' → ∃ λ t'' → (t ↪ t'') ⊗ (rename σ t'' ≡ t')
rename↪ {t = ƛ t} (ζ step) with rename↪ step
... | ﹙ _ , ﹙ step , refl ﹚ ﹚ = ﹙ _ , ﹙ ζ step , refl ﹚ ﹚
rename↪ {t = ` v · b} (ξ-·₂ step) with rename↪ step
... | ﹙ _ , ﹙ step , refl ﹚ ﹚ = ﹙ _ , ﹙ ξ-·₂ step , refl ﹚ ﹚
rename↪ {t = (ƛ a) · b} (ξ-·₁ (ζ step)) with rename↪ step 
... | ﹙ _ , ﹙ step , refl ﹚ ﹚ = ﹙ _ , ﹙ ξ-·₁ (ζ step) , refl ﹚ ﹚
rename↪ {t = (ƛ a) · b} (ξ-·₂ step) with rename↪ step 
... | ﹙ _ , ﹙ step , refl ﹚ ﹚ = ﹙ _ , ﹙ ξ-·₂ step , refl ﹚ ﹚
rename↪ {t = (ƛ a) · b} β = ﹙ a [ b ] , ﹙ β , (rename-subst-commute {N = a} {M = b}) ﹚ ﹚
rename↪ {t = f · a · b} (ξ-·₁ step) with rename↪ step
... | ﹙ _ , ﹙ step , refl ﹚ ﹚ = ﹙ _ , ﹙ ξ-·₁ step , refl ﹚ ﹚
rename↪ {t = f · a · b} (ξ-·₂ step) with rename↪ step
... | ﹙ _ , ﹙ step , refl ﹚ ﹚ = ﹙ _ , ﹙ ξ-·₂ step , refl ﹚ ﹚
rename↪ {t = ⟨ a , b ⟩} (ξ-⟨,⟩₁ step) with rename↪ step
... | ﹙ _ , ﹙ step , refl ﹚ ﹚ = ﹙ _ , ﹙ ξ-⟨,⟩₁ step , refl ﹚ ﹚
rename↪ {t = ⟨ a , b ⟩} (ξ-⟨,⟩₂ step) with rename↪ step
... | ﹙ _ , ﹙ step , refl ﹚ ﹚ = ﹙ _ , ﹙ ξ-⟨,⟩₂ step , refl ﹚ ﹚
rename↪ {t = proj _ ⟨ a , b ⟩} β-proj₁ = ﹙ a , ﹙ β-proj₁ , refl ﹚ ﹚
rename↪ {t = proj _ ⟨ a , b ⟩} β-proj₂ = ﹙ b , ﹙ β-proj₂ , refl ﹚ ﹚
rename↪ {t = proj _ t} (ξ-proj step) with rename↪ step
rename↪ {t = proj _ {inj₁ x} t} (ξ-proj _) | ﹙ _ , ﹙ step , refl ﹚ ﹚ = ﹙ _ , ﹙ ξ-proj step , refl ﹚ ﹚
rename↪ {t = proj _ {inj₂ y} t} (ξ-proj _) | ﹙ _ , ﹙ step , refl ﹚ ﹚ = ﹙ _ , ﹙ ξ-proj step , refl ﹚ ﹚
rename↪ {t = proj _ f · a} (ξ-·₁ step) with rename↪ step
... | ﹙ _ , ﹙ step , refl ﹚ ﹚ = ﹙ _ , ﹙ ξ-·₁ step , refl ﹚ ﹚
rename↪ {t = proj _ f · a} (ξ-·₂ step) with rename↪ step
... | ﹙ _ , ﹙ step , refl ﹚ ﹚ = ﹙ _ , ﹙ ξ-·₂ step , refl ﹚ ﹚


SN*-rename : ∀{Γ Δ A} {t : Γ ⊢ A} → (ρ : Rename Γ Δ) → SN* ⟦_⟧ t → SN* ⟦_⟧ (rename ρ t)

⟦⟧-rename : ∀{Γ Δ A} {t : Γ ⊢ A} → (ρ : Rename Γ Δ) → ⟦ t ⟧ → ⟦ rename ρ t ⟧
⟦⟧-rename {t = ` v} ρ tt = tt
⟦⟧-rename {t = a · b} ρ tt = tt
⟦⟧-rename {A = A ⇒ B} {t = ƛ n} ρ Ln {_}{ρ₁}{u}
    rewrite cong (SN* ⟦_⟧) (rename-subst {Σ = ∅} {M = n} {N = u} {ρ = ρ} {σ = (ids ∘ ρ₁)})
  = λ SNu → Ln {_} {ρ₁ ∘ ρ} SNu
⟦⟧-rename {t = ⋆} ρ x = tt
⟦⟧-rename {t = ⟨ a , b ⟩} ρ ﹙ SN*a , SN*b ﹚ = ﹙ SN*-rename ρ SN*a , SN*-rename ρ SN*b ﹚
⟦⟧-rename {t = proj _ t} ρ x = tt

SN*-rename ρ (sn* Lt SNt) = sn* (⟦⟧-rename ρ Lt) λ step → case (rename↪ step) of λ {﹙ t' , ﹙ t↪t' , refl ﹚ ﹚ → SN*-rename ρ (SNt t↪t')}

⊨exts : ∀{Γ Δ A} {σ : Subst Γ Δ} → Γ ⊨ σ → (Γ , A) ⊨ (exts σ)
⊨exts σ Z = sn* tt (λ ())
⊨exts σ (S v) = SN*-rename S_ (σ v)

⊨rename : ∀{Γ Δ Δ₁} {σ : Subst Γ Δ} → Γ ⊨ σ → (ρ : Rename Δ Δ₁) → Γ ⊨ (⟪ ids ∘ ρ ⟫ ∘ σ)
⊨rename {σ = σ} Lσ ρ v rewrite cong (SN* ⟦_⟧) (rename-subst-ids {Σ = ∅} {N = σ v} {ρ = ρ}) = SN*-rename ρ (Lσ v)

-------


↪SN* : ∀ {Γ A}{t t' : Γ ⊢ A} → t ↪ t' → SN* ⟦_⟧ t → SN* ⟦_⟧ t'
↪SN* step (sn* _ SNt) = SNt step

lemma-ƛ : ∀ {Γ A B} → {t : Γ , B ⊢ A} → ⟦ ƛ t ⟧ → SN* ⟦_⟧ t → SN* ⟦_⟧ (ƛ t)
lemma-ƛ {t = t} Lƛ (sn* _ SNt) = sn* Lƛ (λ {(ζ step) → lemma-ƛ (λ {u} SNu → ↪SN* (↪[] step) (Lƛ SNu)) (SNt step)})


lemma-· : ∀ {Γ A B} → {a : Γ ⊢ A ⇒ B} {b : Γ ⊢ A} → SN* ⟦_⟧ a → SN* ⟦_⟧ b → SN* ⟦_⟧ (a · b)
lemma-· SN*a SN*b = sn* tt λ step → aux SN*a SN*b step
  where aux : ∀ {Γ A B} {a : Γ ⊢ B ⇒ A} {b : Γ ⊢ B} {t' : Γ ⊢ A} → SN* ⟦_⟧ a → SN* ⟦_⟧ b → a · b ↪ t' → SN* ⟦_⟧ t'
        aux (sn* La SNa) SN*b (ξ-·₁ step) = lemma-· (SNa step) SN*b
        aux SN*a (sn* Lb SNb) (ξ-·₂ step) = lemma-· SN*a (SNb step)
        aux (sn* La SNa) SN*b β = La SN*b 


lemma-⟨,⟩ : ∀ {Γ A B} → {a : Γ ⊢ A} {b : Γ ⊢ B} → SN* ⟦_⟧ a → SN* ⟦_⟧ b → SN* ⟦_⟧ (⟨ a , b ⟩)
lemma-⟨,⟩ SN*a SN*b = sn* ﹙ SN*a , SN*b ﹚ λ step → aux SN*a SN*b step
  where aux : ∀ {Γ A B} {a : Γ ⊢ A} {b : Γ ⊢ B} {t' : Γ ⊢ A × B} → SN* ⟦_⟧ a → SN* ⟦_⟧ b → ⟨ a , b ⟩ ↪ t' → SN* ⟦_⟧ t'
        aux (sn* La SNa) SN*b (ξ-⟨,⟩₁ step) = lemma-⟨,⟩ (SNa step) SN*b
        aux SN*a (sn* Lb SNb) (ξ-⟨,⟩₂ step) = lemma-⟨,⟩ SN*a (SNb step)


lemma-proj : ∀ {Γ A B C p} → {t : Γ ⊢ A × B} → SN* ⟦_⟧ t → SN* ⟦_⟧ (proj C {p} t)
lemma-proj SN*t = sn* tt (aux SN*t)
  where aux : ∀ {Γ A B C p t'} → {t : Γ ⊢ A × B} → SN* ⟦_⟧ t → (proj C {p} t) ↪ t' → SN* ⟦_⟧ t'
        aux (sn* Lt SNt) (ξ-proj step) = lemma-proj (SNt step)
        aux (sn* ﹙ SN*t' , _ ﹚ SNt) β-proj₁ = SN*t'
        aux (sn* ﹙ _ , SN*t' ﹚ SNt) β-proj₂ = SN*t'

-- ids es una substitución adecuada

⊨ids : ∀{Γ} → Γ ⊨ ids
⊨ids _ = sn* tt (λ ())

-- cons entre una substitución adecuada y un termino SN* es también una substitución adecuada

⊨_•_ : ∀{Γ Δ A} {σ : Subst Δ Γ} {t : Γ ⊢ A} → SN* ⟦_⟧ t → Δ ⊨ σ → (Δ , A) ⊨ (t • σ)
(⊨ t • σ) Z = t
(⊨ t • σ) (S v) = σ v


adequacy : ∀ {Γ Δ A} {σ : Subst Γ Δ} → (t : Γ ⊢ A) → Γ ⊨ σ → SN* ⟦_⟧ (⟪ σ ⟫ t)
adequacy (` v) σ = σ v
adequacy ⋆ σ = sn* tt (λ ())
adequacy ⟨ a , b ⟩ σ = lemma-⟨,⟩ (adequacy a σ) (adequacy b σ)
adequacy (proj _ x) σ = lemma-proj (adequacy x σ)
adequacy (a · b) σ = lemma-· (adequacy a σ) (adequacy b σ)
adequacy {A = A ⇒ B} {σ = σ} (ƛ n) Lσ =
  lemma-ƛ
    (λ { {ρ = ρ}{u = u} SNu →
      transport (SN* ⟦_⟧)
        (subst-split {Σ = ∅} {N = n})
        (adequacy n (⊨ SNu • (⊨rename Lσ ρ)))}) -- {u • (⟪ ids ∘ ρ ⟫ ∘ σ)}
    (adequacy n (⊨exts Lσ))

SN-substitute : ∀ {Γ Δ A}{σ : Subst Γ Δ}{t : Γ ⊢ A} → SN (subst σ t) → SN t
SN-substitute (sn SNtσ) = sn (λ step → SN-substitute (SNtσ (↪[] step)))

strong-norm : ∀ {Γ A} (t : Γ ⊢ A) → SN t
strong-norm t = SN-substitute (SN*-SN (adequacy t ⊨ids))

-------------------------

data Value : ∀ {Γ A} → Γ ⊢ A → Set where

  V-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B}
      ---------------------------
    → Value (ƛ N)

  V-⋆ : ∀ {Γ} → Value (⋆ {Γ})

  V-⟨_,_⟩ : ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
    → Value V
    → Value W
      ----------------
    → Value ⟨ V , W ⟩

data Progress {A} (M : ∅ ⊢ A) : Set where

  step : ∀ {N : ∅ ⊢ A}
    → M ↪ N
      ----------
    → Progress M

  done :
      Value M
      ----------
    → Progress M

progress : ∀ {A} → (M : ∅ ⊢ A) → Progress M
progress ⋆                           =  done V-⋆
progress (ƛ N)                       =  done V-ƛ
progress (L · M) with progress L
...    | step L↪L′                   =  step (ξ-·₁ L↪L′)
...    | done V-ƛ with progress M
...        | step M↪M′               =  step (ξ-·₂ M↪M′)
...        | done VM                 =  step β
progress ⟨ M , N ⟩ with progress M
...    | step M↪M′                   =  step (ξ-⟨,⟩₁ M↪M′)
...    | done VM with progress N
...        | step N↪N′               =  step (ξ-⟨,⟩₂ N↪N′)
...        | done VN                 =  done V-⟨ VM , VN ⟩
progress (proj _ L) with progress L
...    | step L↪L′                   =  step (ξ-proj L↪L′)
progress (proj _ {inj₁ refl} N) | done V-⟨ VM , VN ⟩ =  step β-proj₁
progress (proj _ {inj₂ refl} N) | done V-⟨ VM , VN ⟩ =  step β-proj₂

data _⇝_ {Γ A} : (Γ ⊢ A) → (Γ ⊢ A) → Set where

  _∎ : (M : Γ ⊢ A)
      ------
    → M ⇝ M

  _↪⟨_⟩_ : (L : Γ ⊢ A) {M N : Γ ⊢ A}
    → L ↪ M
    → M ⇝ N
      ------
    → L ⇝ N

data Steps {A} : ∅ ⊢ A → Set where

  steps : {L N : ∅ ⊢ A}
    → L ⇝ N
      ----------
    → Steps L

eval' : ∀ {A} → (L : ∅ ⊢ A) → SN L → Steps L
eval' L (sn f) with progress L
... | done VL                           =  steps (L ∎)
... | step {M} L↪M with eval' M (f L↪M)
...    | steps M⇝N                      =  steps (L ↪⟨ L↪M ⟩ M⇝N)

eval : ∀ {A} → (L : ∅ ⊢ A) → Steps L
eval L = eval' L (strong-norm L)

test : ∅ ⊢ ⊤
test = (ƛ (proj _ {inj₂ refl} (` Z)) · proj ⊤ {inj₁ refl} (` Z)) · ⟨ ⋆ , ƛ ` Z ⟩