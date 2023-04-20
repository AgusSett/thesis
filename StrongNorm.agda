module StrongNorm where
open import Function.Base using (_∘_)

infix  4 _⊢_
infix  4 _∋_
infixl 5 _,_

infixr 7 _⇒_

infix  5 ƛ_
infixl 7 _·_
infix  9 `_
infix  9 S_


data Type : Set where
  _⇒_ : Type → Type → Type
  τ   : Type


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

  ƛ_  : ∀ {Γ A B}
    → Γ , A ⊢ B
      ---------
    → Γ ⊢ A ⇒ B

  _·_ : ∀ {Γ A B}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
      ---------
    → Γ ⊢ B


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

data SN {Γ A} (t : Γ ⊢ A) : Set where
  sn : (∀ {t'} → t ↪ t' → SN t') → SN t

L : ∀ {Γ A} → (t : Γ ⊢ A) → Set
L (ƛ t) = ∀ {u} → L u → L (t [ u ])
L t = SN t

Ls : ∀{Γ Δ} → (σ : Subst Γ Δ) → Set
Ls σ = ∀{A v} → L (σ {A} v)

asd : ∀{Γ} → Ls {Γ} {Γ} ids
asd = sn (λ ())

fth : ∀ {Γ A} → {t : Γ ⊢ A} → L t
lemma : ∀ {Γ A} → {t : Γ ⊢ A} → L t → SN t

test : ∀ {Γ A B} {t : Γ , B ⊢ A} → SN t → SN (ƛ t)
test (sn snt) = sn λ {(ζ st) → test (snt st)}

test2 : ∀ {Γ A B} {t : Γ ⊢ A ⇒ B} {t' : Γ ⊢ A} → L t → L t' → SN t → SN t' → SN (t · t')
test2 {t = t} {t' = t'} lt lt' (sn a) (sn b) =
    sn λ {(ξ-·₁ st) → test2 {! fth !} lt' (a st) (sn b)
        ; (ξ-·₂ st) → {!   !}
        ;  β → {! lemma (lt lt') !}}


lemma {t = ` x} l = l
lemma {t = a · b} l = l
lemma {t = ƛ t} l = test (lemma (fth))


fth {t = ` x} = sn (λ ())
fth {t = a · b} = test2 (fth) (fth) (lemma (fth)) (lemma (fth))
fth {t = ƛ n} = λ lu → {!   !}

caca : ∀ {Γ Δ A} {σ : Subst Γ Δ} {t : Δ ⊢ A} → L t → Ls σ → Ls (t • σ)
caca lt lσ {_} {Z} = lt
caca lt lσ {_} {S v} = lσ

fth2 : ∀ {Γ Δ A} → {t : Γ ⊢ A} → {σ : Subst Γ Δ} → Ls σ → L (⟪ σ ⟫ t)
fth2 {t = ` x₁} x = {!   !}
fth2 {t = t · t₁} x = {!   !}
fth2 {t = ƛ N} {σ} lσ {M} = λ lu → {!  fth2 {_} {_} {_} {N} {M • σ} (caca lu lσ)  !}