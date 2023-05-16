module StrongNorm where

open import Function.Base using (_∘_; case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; cong₂; refl; sym) renaming (subst to transport)
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
infixr 5 _⨟_

ids : ∀{Γ} → Subst Γ Γ
ids x = ` x

↑ : ∀{Γ A} → Subst Γ (Γ , A)
↑ x = ` (S x)

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

_⨟_ : ∀{Γ Δ Σ} → Subst Γ Δ → Subst Δ Σ → Subst Γ Σ
σ ⨟ ρ = ⟪ ρ ⟫ ∘ σ

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


postulate
  subst-commute : ∀{Γ Δ A B}{N : Γ , B ⊢ A}{M : Γ ⊢ B}{σ : Subst Γ Δ}
    → (⟪ exts σ ⟫ N) [ ⟪ σ ⟫ M ] ≡ ⟪ σ ⟫ (N [ M ])

  rename-subst : ∀{Γ Δ Δ′ A B}{M : Γ , B ⊢ A}{N : Δ′ ⊢ B}{ρ : Rename Γ Δ}{σ : Subst Δ Δ′}
    → ⟪ N • σ ⟫ (rename (ext ρ) M) ≡ ⟪ N • (σ ∘ ρ) ⟫ M

  rename-subst-commute : ∀{Γ Δ A B}{N : Γ , A ⊢ B}{M : Γ ⊢ A}{ρ : Rename Γ Δ}
    → (rename (ext ρ) N) [ rename ρ M ] ≡ rename ρ (N [ M ])

  subst-split : ∀{Γ Δ Δ₁ A B}{N : Γ , A ⊢ B}{M : Δ₁ ⊢ A}{σ : Subst Γ Δ}{ρ : Rename Δ Δ₁}
    → ⟪ M • (ids ∘ ρ) ⟫ (⟪ exts σ ⟫ N) ≡ ⟪ M • (⟪ ids ∘ ρ ⟫ ∘ σ) ⟫ N
  
  rename-subst-ids : ∀{Γ Δ A}{N : Γ ⊢ A}{ρ : Rename Γ Δ}
    → ⟪ ids ∘ ρ ⟫ N ≡ rename ρ N
  
  subst-id : ∀{Γ} {A} {M : Γ ⊢ A}
    → ⟪ ids ⟫ M ≡ M


data SN {Γ A} (t : Γ ⊢ A) : Set where
  sn : (∀ {t'} → t ↪ t' → SN t') → SN t

data SN* {Γ A} (P : Γ ⊢ A → Set) (t : Γ ⊢ A) : Set where
  sn* : P t → (∀ {t'} → t ↪ t' → SN* P t') → SN* P t


open import Data.Unit using (tt) renaming (⊤ to Top)

⟦_⟧ : ∀ {Γ A} → Γ ⊢ A → Set
⟦ (ƛ t) ⟧ = ∀ {Δ}{ρ : Rename _ Δ}{u} → SN* ⟦_⟧ u → SN* ⟦_⟧ (⟪ u • (ids ∘ ρ) ⟫ t)
⟦ ⟨ a , b ⟩ ⟧ = SN* ⟦_⟧ a ⊗ SN* ⟦_⟧ b
⟦ t ⟧ = Top

_⊨_ : ∀{Δ} → (Γ : Context) → (σ : Subst Γ Δ) → Set
Γ ⊨ σ = ∀{A} (v : Γ ∋ A) → SN* ⟦_⟧ (σ {A} v)


SN*-SN : ∀ {Γ A} {t : Γ ⊢ A} → SN* ⟦_⟧ t → SN t
SN*-SN (sn* Lt SNt) = sn (λ step → SN*-SN (SNt step))


⊨ids : ∀{Γ} → Γ ⊨ ids
⊨ids _ = sn* tt (λ ())

⊨_•_ : ∀{Γ Δ A} {σ : Subst Δ Γ} {t : Γ ⊢ A} → SN* ⟦_⟧ t → Δ ⊨ σ → (Δ , A) ⊨ (t • σ)
(⊨ t • σ) Z = t
(⊨ t • σ) (S v) = σ v


↪[] : ∀ {Γ Δ A}{t t' : Γ ⊢ A}{σ : Subst Γ Δ} → t ↪ t' → subst σ t ↪ subst σ t'
↪[] (ξ-·₁ step) = ξ-·₁ (↪[] step)
↪[] (ξ-·₂ step) = ξ-·₂ (↪[] step)
↪[] {Δ = Δ} {σ = σ} (β {N = N} {W = W})
  rewrite cong₂ (_↪_) {x = (ƛ subst (exts σ) N) · subst σ W} refl (sym (subst-commute {N = N} {M = W} {σ = σ}))
    = β
↪[] (ζ step) = ζ (↪[] step)
↪[] (ξ-⟨,⟩₁ step) = ξ-⟨,⟩₁ (↪[] step)
↪[] (ξ-⟨,⟩₂ step) = ξ-⟨,⟩₂ (↪[] step)
↪[] (ξ-proj step) = ξ-proj (↪[] step)
↪[] β-proj₁ = β-proj₁
↪[] β-proj₂ = β-proj₂

SN*↪ : ∀ {Γ A}{t t' : Γ ⊢ A} → t ↪ t' → SN* ⟦_⟧ t → SN* ⟦_⟧ t'
SN*↪ step (sn* _ SNt) = SNt step

lemma-ƛ : ∀ {Γ A B} → {t : Γ , B ⊢ A} → ⟦ ƛ t ⟧ → SN* ⟦_⟧ t → SN* ⟦_⟧ (ƛ t)
lemma-ƛ Lƛ (sn* Lt SNt) = sn* Lƛ (λ {(ζ step) → lemma-ƛ (λ {u} SNu → SN*↪ (↪[] step) (Lƛ SNu)) (SNt step)})

rename↪ : ∀ {Γ Δ A}{t : Γ ⊢ A}{σ : Rename Γ Δ}{t'} → (rename σ t) ↪ t' → ∃ λ t'' → (t ↪ t'') ⊗ (rename σ t'' ≡ t')
rename↪ {t = ƛ t} (ζ step) with rename↪ step
... | ﹙ _ , ﹙ t↪t'' , refl ﹚ ﹚ = ﹙ _ , ﹙ ζ t↪t'' , refl ﹚ ﹚
rename↪ {t = ` v · b} (ξ-·₂ step) with rename↪ step
... | ﹙ b'' , ﹙ b↪b'' , refl ﹚ ﹚ = ﹙ ` v · b'' , ﹙ ξ-·₂ b↪b'' , refl ﹚ ﹚
rename↪ {t = (ƛ a) · b} (ξ-·₁ (ζ step)) with rename↪ step 
... | ﹙ a'' , ﹙ a↪a'' , refl ﹚ ﹚ = ﹙ (ƛ a'') · b , ﹙ ξ-·₁ (ζ a↪a'') , refl ﹚ ﹚
rename↪ {t = (ƛ a) · b} (ξ-·₂ step) with rename↪ step 
... | ﹙ b'' , ﹙ b↪b'' , refl ﹚ ﹚ = ﹙ (ƛ a) · b'' , ﹙ ξ-·₂ b↪b'' , refl ﹚ ﹚
rename↪ {t = (ƛ a) · b} β = ﹙ a [ b ] , ﹙ β , sym (rename-subst-commute {N = a} {M = b}) ﹚ ﹚
rename↪ {t = f · a · b} (ξ-·₁ step) with rename↪ step
... | ﹙ fa'' , ﹙ fa↪fa'' , refl ﹚ ﹚ = ﹙ fa'' · b , ﹙ ξ-·₁ fa↪fa'' , refl ﹚ ﹚
rename↪ {t = f · a · b} (ξ-·₂ step) with rename↪ step
... | ﹙ b'' , ﹙ b↪b'' , refl ﹚ ﹚ = ﹙ f · a · b'' , ﹙ ξ-·₂ b↪b'' , refl ﹚ ﹚
rename↪ {t = ⟨ a , b ⟩} (ξ-⟨,⟩₁ step) with rename↪ step
... | ﹙ a'' , ﹙ a↪a'' , refl ﹚ ﹚ = ﹙ ⟨ a'' , b ⟩ , ﹙ ξ-⟨,⟩₁ a↪a'' , refl ﹚ ﹚
rename↪ {t = ⟨ a , b ⟩} (ξ-⟨,⟩₂ step) with rename↪ step
... | ﹙ b'' , ﹙ b↪b'' , refl ﹚ ﹚ = ﹙ ⟨ a , b'' ⟩ , ﹙ ξ-⟨,⟩₂ b↪b'' , refl ﹚ ﹚
rename↪ {t = proj _ ⟨ a , b ⟩} β-proj₁ = ﹙ a , ﹙ β-proj₁ , refl ﹚ ﹚
rename↪ {t = proj _ ⟨ a , b ⟩} β-proj₂ = ﹙ b , ﹙ β-proj₂ , refl ﹚ ﹚
rename↪ {t = proj _ t} (ξ-proj step) with rename↪ step
rename↪ {A = _} {proj _ {inj₁ x} t} (ξ-proj step) | ﹙ t'' , ﹙ t↪t'' , refl ﹚ ﹚ = ﹙ proj _ t'' , ﹙ ξ-proj t↪t'' , refl ﹚ ﹚
rename↪ {A = _} {proj _ {inj₂ y} t} (ξ-proj step) | ﹙ t'' , ﹙ t↪t'' , refl ﹚ ﹚ = ﹙ proj _ t'' , ﹙ ξ-proj t↪t'' , refl ﹚ ﹚
rename↪ {t = proj _ f · a} (ξ-·₁ step) with rename↪ step
... | ﹙ f'' , ﹙ f↪f'' , refl ﹚ ﹚ = ﹙ f'' · a , ﹙ ξ-·₁ f↪f'' , refl ﹚ ﹚
rename↪ {t = proj _ f · a} (ξ-·₂ step) with rename↪ step
... | ﹙ a'' , ﹙ a↪a'' , refl ﹚ ﹚ = ﹙ proj _ f · a'' , ﹙ ξ-·₂ a↪a'' , refl ﹚ ﹚


SN*-rename : ∀{Γ Δ A} {t : Γ ⊢ A} → (ρ : Rename Γ Δ) → SN* ⟦_⟧ t → SN* ⟦_⟧ (rename ρ t)

⟦⟧-rename : ∀{Γ Δ A} {t : Γ ⊢ A} → (ρ : Rename Γ Δ) → ⟦ t ⟧ → ⟦ rename ρ t ⟧
⟦⟧-rename {t = ` v} ρ tt = tt
⟦⟧-rename {t = a · b} ρ tt = tt
⟦⟧-rename {A = A ⇒ B} {t = ƛ n} ρ Ln {_}{ρ₁}{u}
    rewrite cong (SN* ⟦_⟧) (rename-subst {M = n} {N = u} {ρ = ρ} {σ = (ids ∘ ρ₁)})
  = λ SNu → Ln {_} {ρ₁ ∘ ρ} SNu
⟦⟧-rename {t = ⋆} ρ x = tt
⟦⟧-rename {t = ⟨ a , b ⟩} ρ ﹙ SN*a , SN*b ﹚ = ﹙ SN*-rename ρ SN*a , SN*-rename ρ SN*b ﹚
⟦⟧-rename {t = proj _ t} ρ x = tt


SN*-rename ρ (sn* Lt SNt) = sn* (⟦⟧-rename ρ Lt) λ step → case (rename↪ step) of λ {﹙ t' , ﹙ t↪t' , refl ﹚ ﹚ → SN*-rename ρ (SNt t↪t')}

⊨exts : ∀{Γ Δ A} {σ : Subst Γ Δ} → Γ ⊨ σ → (Γ , A) ⊨ (exts σ)
⊨exts σ Z = sn* tt (λ ())
⊨exts σ (S v) = SN*-rename S_ (σ v)

⊨rename : ∀{Γ Δ Δ₁} {σ : Subst Γ Δ} → Γ ⊨ σ → (ρ : Rename Δ Δ₁) → Γ ⊨ (⟪ ids ∘ ρ ⟫ ∘ σ)
⊨rename {σ = σ} Lσ ρ v rewrite cong (SN* ⟦_⟧) (rename-subst-ids {N = σ v} {ρ = ρ}) = SN*-rename ρ (Lσ v)


lemma-· : ∀ {Γ A B} → {a : Γ ⊢ A ⇒ B} {b : Γ ⊢ A} → SN* ⟦_⟧ a → SN* ⟦_⟧ b → SN* ⟦_⟧ (a · b)

lemma-·-aux : ∀ {Γ A B} {a : Γ ⊢ B ⇒ A} {b : Γ ⊢ B} {t' : Γ ⊢ A} → SN* ⟦_⟧ a → SN* ⟦_⟧ b → a · b ↪ t' → SN* ⟦_⟧ t'
lemma-·-aux (sn* La SNa) SN*b (ξ-·₁ step) = lemma-· (SNa step) SN*b
lemma-·-aux SN*a (sn* Lb SNb) (ξ-·₂ step) = lemma-· SN*a (SNb step)
lemma-·-aux (sn* La SNa) SN*b β = La SN*b

lemma-· SN*a SN*b = sn* tt λ step → lemma-·-aux SN*a SN*b step


lemma-⟨,⟩ : ∀ {Γ A B} → {a : Γ ⊢ A} {b : Γ ⊢ B} → SN* ⟦_⟧ a → SN* ⟦_⟧ b → SN* ⟦_⟧ (⟨ a , b ⟩)

lemma-⟨,⟩-aux : ∀ {Γ A B} {a : Γ ⊢ A} {b : Γ ⊢ B} {t' : Γ ⊢ A × B} → SN* ⟦_⟧ a → SN* ⟦_⟧ b → ⟨ a , b ⟩ ↪ t' → SN* ⟦_⟧ t'
lemma-⟨,⟩-aux (sn* La SNa) SN*b (ξ-⟨,⟩₁ step) = lemma-⟨,⟩ (SNa step) SN*b
lemma-⟨,⟩-aux SN*a (sn* Lb SNb) (ξ-⟨,⟩₂ step) = lemma-⟨,⟩ SN*a (SNb step)

lemma-⟨,⟩ SN*a SN*b = sn* ﹙ SN*a , SN*b ﹚ λ step → lemma-⟨,⟩-aux SN*a SN*b step

lemma-proj : ∀ {Γ A B C p} → {t : Γ ⊢ A × B} → SN* ⟦_⟧ t → SN* ⟦_⟧ (proj C {p} t)
lemma-proj {p = inj₁ refl} (sn* Lt SNt) = sn* tt λ {(ξ-proj step) → lemma-proj (SNt step)
                                                   ; β-proj₁      → proj₁ Lt}
lemma-proj {p = inj₂ refl} (sn* Lt SNt) = sn* tt λ {(ξ-proj step) → lemma-proj (SNt step)
                                                   ; β-proj₂      → proj₂ Lt}


adequacy : ∀ {Γ Δ A} {σ : Subst Γ Δ} → (t : Γ ⊢ A) → Γ ⊨ σ → SN* ⟦_⟧ (⟪ σ ⟫ t)
adequacy (` v) σ = σ v
adequacy ⋆ σ = sn* tt (λ ())
adequacy ⟨ a , b ⟩ σ = lemma-⟨,⟩ (adequacy a σ) (adequacy b σ)
adequacy (proj _ x) σ = lemma-proj (adequacy x σ)
adequacy (a · b) σ = lemma-· (adequacy a σ) (adequacy b σ)
adequacy {A = A ⇒ B} {σ = σ} (ƛ n) Lσ =
  lemma-ƛ
    (λ { {ρ = ρ}{u = u} SNu →
      transport (SN* ⟦_⟧) (sym (subst-split {N = n})) (adequacy n (⊨ SNu • (⊨rename Lσ ρ)))}) -- {u • (⟪ ids ∘ ρ ⟫ ∘ σ)}
    (adequacy n (⊨exts Lσ))

SN-substitute : ∀ {Γ Δ A}{σ : Subst Γ Δ}{t : Γ ⊢ A} → SN (subst σ t) → SN t
SN-substitute (sn SNtσ) = sn (λ step → SN-substitute (SNtσ (↪[] step)))

strong-norm : ∀ {Γ A} (t : Γ ⊢ A) → SN t
strong-norm t = SN-substitute (SN*-SN (adequacy t ⊨ids))

strong-norm2 : ∀ {Γ A} (t : Γ ⊢ A) → SN t
strong-norm2 t rewrite cong SN (sym (subst-id {M = t})) = SN*-SN (adequacy t ⊨ids) 