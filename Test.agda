{-# OPTIONS --without-K #-}

-- strong normalization for STLC, adapted from
--   https://www.ps.uni-saarland.de/~schaefer/thesis/html/semantics.f.strongnorm.html
-- checked with Agda 2.6.0.1

open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Unit
open import Data.Sum
open import Function

_&_ = cong; infixl 9 _&_
_⁻¹ = sym; infix 6 _⁻¹
_◾_ = trans; infixr 4 _◾_

coe : {A B : Set} → A ≡ B → A → B
coe refl a = a

infixl 8 _⊗_
_⊗_ : ∀ {A B : Set}{f g : A → B}{a a'} → f ≡ g → a ≡ a' → f a ≡ g a'
refl ⊗ refl = refl

-- Syntax
--------------------------------------------------------------------------------

infixr 4 _⇒_
infixr 4 _,_
infixr 5 _⊠_

data Ty : Set where
  ι   : Ty
  _⇒_ : Ty → Ty → Ty
  _⊠_ : Ty → Ty → Ty

data Con : Set where
  ∙   : Con
  _,_ : Con → Ty → Con

data _∈_ (A : Ty) : Con → Set where
  vz : ∀ {Γ} → A ∈ (Γ , A)
  vs : ∀ {B Γ} → A ∈ Γ → A ∈ (Γ , B)

data Tm Γ : Ty → Set where
  var : ∀ {A} → A ∈ Γ → Tm Γ A
  lam : ∀ {A B} → Tm (Γ , A) B → Tm Γ (A ⇒ B)
  app : ∀ {A B} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
  ⟨_,_⟩ : ∀ {A B} → Tm Γ A → Tm Γ B → Tm Γ (A ⊠ B)
  p₁ : ∀ {A B} → Tm Γ (A ⊠ B) → Tm Γ A
  p₂ : ∀ {A B} → Tm Γ (A ⊠ B) → Tm Γ B
  []≡ : ∀ {A B} → Tm Γ (A ⊠ B) → Tm Γ (B ⊠ A)

-- Order-preserving embedding
--------------------------------------------------------------------------------

data OPE : Con → Con → Set where
  ∙    : OPE ∙ ∙
  drop : ∀ {A Γ Δ} → OPE Γ Δ → OPE (Γ , A) Δ
  keep : ∀ {A Γ Δ} → OPE Γ Δ → OPE (Γ , A) (Δ , A)

idₑ : ∀ {Γ} → OPE Γ Γ
idₑ {∙}     = ∙
idₑ {Γ , A} = keep (idₑ {Γ})

wk : ∀ {A Γ} → OPE (Γ , A) Γ
wk = drop idₑ

_∘ₑ_ : ∀ {Γ Δ Σ} → OPE Δ Σ → OPE Γ Δ → OPE Γ Σ
σ      ∘ₑ ∙      = σ
σ      ∘ₑ drop δ = drop (σ ∘ₑ δ)
drop σ ∘ₑ keep δ = drop (σ ∘ₑ δ)
keep σ ∘ₑ keep δ = keep (σ ∘ₑ δ)

idlₑ : ∀ {Γ Δ}(σ : OPE Γ Δ) → idₑ ∘ₑ σ ≡ σ
idlₑ ∙        = refl
idlₑ (drop σ) = drop & idlₑ σ
idlₑ (keep σ) = keep & idlₑ σ

idrₑ : ∀ {Γ Δ}(σ : OPE Γ Δ) → σ ∘ₑ idₑ ≡ σ
idrₑ ∙        = refl
idrₑ (drop σ) = drop & idrₑ σ
idrₑ (keep σ) = keep & idrₑ σ

assₑ :
  ∀ {Γ Δ Σ Ξ}(σ : OPE Σ Ξ)(δ : OPE Δ Σ)(ν : OPE Γ Δ)
  → (σ ∘ₑ δ) ∘ₑ ν ≡ σ ∘ₑ (δ ∘ₑ ν)
assₑ σ        δ        ∙        = refl
assₑ σ        δ        (drop ν) = drop & assₑ σ δ ν
assₑ σ        (drop δ) (keep ν) = drop & assₑ σ δ ν
assₑ (drop σ) (keep δ) (keep ν) = drop & assₑ σ δ ν
assₑ (keep σ) (keep δ) (keep ν) = keep & assₑ σ δ ν

∈ₑ : ∀ {A Γ Δ} → OPE Γ Δ → A ∈ Δ → A ∈ Γ
∈ₑ ∙        v      = v
∈ₑ (drop σ) v      = vs (∈ₑ σ v)
∈ₑ (keep σ) vz     = vz
∈ₑ (keep σ) (vs v) = vs (∈ₑ σ v)

∈-idₑ : ∀ {A Γ}(v : A ∈ Γ) → ∈ₑ idₑ v ≡ v
∈-idₑ vz     = refl
∈-idₑ (vs v) = vs & ∈-idₑ v

∈-∘ₑ : ∀ {A Γ Δ Σ}(σ : OPE Δ Σ)(δ : OPE Γ Δ)(v : A ∈ Σ) → ∈ₑ (σ ∘ₑ δ) v ≡ ∈ₑ δ (∈ₑ σ v)
∈-∘ₑ ∙        ∙        v      = refl
∈-∘ₑ σ        (drop δ) v      = vs & ∈-∘ₑ σ δ v
∈-∘ₑ (drop σ) (keep δ) v      = vs & ∈-∘ₑ σ δ v
∈-∘ₑ (keep σ) (keep δ) vz     = refl
∈-∘ₑ (keep σ) (keep δ) (vs v) = vs & ∈-∘ₑ σ δ v

Tmₑ : ∀ {A Γ Δ} → OPE Γ Δ → Tm Δ A → Tm Γ A
Tmₑ σ (var v)   = var (∈ₑ σ v)
Tmₑ σ (lam t)   = lam (Tmₑ (keep σ) t)
Tmₑ σ (app f a) = app (Tmₑ σ f) (Tmₑ σ a)
Tmₑ σ ⟨ x , x₁ ⟩ = ⟨ Tmₑ σ x , Tmₑ σ x₁ ⟩
Tmₑ σ (p₁ x) = p₁ (Tmₑ σ x)
Tmₑ σ (p₂ x) = p₂ (Tmₑ σ x)
Tmₑ σ ([]≡ x) = []≡ (Tmₑ σ x)

cong-⟨,⟩ : ∀ {Γ A B} {a c : Tm Γ A} {b d : Tm Γ B} → a ≡ c → b ≡ d → ⟨ a , b ⟩ ≡ ⟨ c , d ⟩
cong-⟨,⟩ refl refl = refl

Tm-idₑ : ∀ {A Γ}(t : Tm Γ A) → Tmₑ idₑ t ≡ t
Tm-idₑ (var v)   = var & ∈-idₑ v
Tm-idₑ (lam t)   = lam & Tm-idₑ t
Tm-idₑ (app f a) = app & Tm-idₑ f ⊗ Tm-idₑ a
Tm-idₑ ⟨ x , x₁ ⟩ = cong-⟨,⟩ (Tm-idₑ x) (Tm-idₑ x₁)
Tm-idₑ (p₁ x) = p₁ & (Tm-idₑ x)
Tm-idₑ (p₂ x) = p₂ & (Tm-idₑ x)
Tm-idₑ ([]≡ x) = []≡ & (Tm-idₑ x)

Tm-∘ₑ : ∀ {A Γ Δ Σ}(σ : OPE Δ Σ)(δ : OPE Γ Δ)(t : Tm Σ A) → Tmₑ (σ ∘ₑ δ) t ≡ Tmₑ δ (Tmₑ σ t)
Tm-∘ₑ σ δ (var v)   = var & ∈-∘ₑ σ δ v
Tm-∘ₑ σ δ (lam t)   = lam & Tm-∘ₑ (keep σ) (keep δ) t
Tm-∘ₑ σ δ (app f a) = app & Tm-∘ₑ σ δ f ⊗ Tm-∘ₑ σ δ a
Tm-∘ₑ σ δ ⟨ x , x₁ ⟩ = cong-⟨,⟩ (Tm-∘ₑ σ δ x) (Tm-∘ₑ σ δ x₁)
Tm-∘ₑ σ δ (p₁ x) = p₁ & (Tm-∘ₑ σ δ x)
Tm-∘ₑ σ δ (p₂ x) = p₂ & (Tm-∘ₑ σ δ x)
Tm-∘ₑ σ δ ([]≡ x) = []≡ & (Tm-∘ₑ σ δ x)

-- Substitution
--------------------------------------------------------------------------------

infixr 6 _ₑ∘ₛ_ _ₛ∘ₑ_ _∘ₛ_

data Sub (Γ : Con) : Con → Set where
  ∙   : Sub Γ ∙
  _,_ : ∀ {A : Ty}{Δ : Con} → Sub Γ Δ → Tm Γ A → Sub Γ (Δ , A)

_ₛ∘ₑ_ : ∀ {Γ Δ Σ} → Sub Δ Σ → OPE Γ Δ → Sub Γ Σ
∙       ₛ∘ₑ δ = ∙
(σ , t) ₛ∘ₑ δ = σ ₛ∘ₑ δ , Tmₑ δ t

_ₑ∘ₛ_ : ∀ {Γ Δ Σ} → OPE Δ Σ → Sub Γ Δ → Sub Γ Σ
∙      ₑ∘ₛ δ       = δ
drop σ ₑ∘ₛ (δ , t) = σ ₑ∘ₛ δ
keep σ ₑ∘ₛ (δ , t) = σ ₑ∘ₛ δ , t

dropₛ : ∀ {A Γ Δ} → Sub Γ Δ → Sub (Γ , A) Δ
dropₛ σ = σ ₛ∘ₑ wk

keepₛ : ∀ {A Γ Δ} → Sub Γ Δ → Sub (Γ , A) (Δ , A)
keepₛ σ = dropₛ σ , var vz

∈ₛ : ∀ {A Γ Δ} → Sub Γ Δ → A ∈ Δ → Tm Γ A
∈ₛ (σ , t) vz     = t
∈ₛ (σ  , t)(vs v) = ∈ₛ σ v

Tmₛ : ∀ {A Γ Δ} → Sub Γ Δ → Tm Δ A → Tm Γ A
Tmₛ σ (var v)   = ∈ₛ σ v
Tmₛ σ (lam t)   = lam (Tmₛ (keepₛ σ) t)
Tmₛ σ (app f a) = app (Tmₛ σ f) (Tmₛ σ a)
Tmₛ σ ⟨ x , x₁ ⟩ = ⟨ Tmₛ σ x , Tmₛ σ x₁ ⟩
Tmₛ σ (p₁ x) = p₁ (Tmₛ σ x)
Tmₛ σ (p₂ x) = p₂ (Tmₛ σ x)
Tmₛ σ ([]≡ x) = []≡ (Tmₛ σ x)

idₛ : ∀ {Γ} → Sub Γ Γ
idₛ {∙}     = ∙
idₛ {Γ , A} = (idₛ {Γ} ₛ∘ₑ drop idₑ) , var vz

_∘ₛ_ : ∀ {Γ Δ Σ} → Sub Δ Σ → Sub Γ Δ → Sub Γ Σ
∙       ∘ₛ δ = ∙
(σ , t) ∘ₛ δ = σ ∘ₛ δ , Tmₛ δ t

assₛₑₑ :
  ∀ {Γ Δ Σ Ξ}(σ : Sub Σ Ξ)(δ : OPE Δ Σ)(ν : OPE Γ Δ)
  → (σ ₛ∘ₑ δ) ₛ∘ₑ ν ≡ σ ₛ∘ₑ (δ ∘ₑ ν)
assₛₑₑ ∙       δ ν = refl
assₛₑₑ (σ , t) δ ν = _,_ & assₛₑₑ σ δ ν ⊗ (Tm-∘ₑ δ ν t ⁻¹)

assₑₛₑ :
  ∀ {Γ Δ Σ Ξ}(σ : OPE Σ Ξ)(δ : Sub Δ Σ)(ν : OPE Γ Δ)
  → (σ ₑ∘ₛ δ) ₛ∘ₑ ν ≡ σ ₑ∘ₛ (δ ₛ∘ₑ ν)
assₑₛₑ ∙        δ       ν = refl
assₑₛₑ (drop σ) (δ , t) ν = assₑₛₑ σ δ ν
assₑₛₑ (keep σ) (δ , t) ν = (_, Tmₑ ν t) & assₑₛₑ σ δ ν

idlₑₛ : ∀ {Γ Δ}(σ : Sub Γ Δ) → idₑ ₑ∘ₛ σ ≡ σ
idlₑₛ ∙       = refl
idlₑₛ (σ , t) = (_, t) & idlₑₛ σ

idrₑₛ : ∀ {Γ Δ}(σ : OPE Γ Δ) → σ ₑ∘ₛ idₛ ≡ idₛ ₛ∘ₑ σ
idrₑₛ ∙        = refl
idrₑₛ (drop σ) =
  assₑₛₑ σ idₛ wk ⁻¹ ◾ dropₛ & idrₑₛ σ ◾ assₛₑₑ idₛ σ wk ◾ (idₛ ₛ∘ₑ_) & (drop & idrₑ σ)
idrₑₛ (keep σ) =
  (_, var vz) & (assₑₛₑ σ idₛ wk ⁻¹ ◾ (_ₛ∘ₑ wk) & idrₑₛ σ
  ◾ assₛₑₑ idₛ σ wk ◾ (idₛ ₛ∘ₑ_) & (drop & (idrₑ σ ◾ idlₑ σ ⁻¹))
  ◾ assₛₑₑ idₛ wk (keep σ) ⁻¹)

∈-ₑ∘ₛ : ∀ {A Γ Δ Σ}(σ : OPE Δ Σ)(δ : Sub Γ Δ)(v : A ∈ Σ) → ∈ₛ (σ ₑ∘ₛ δ) v ≡ ∈ₛ δ (∈ₑ σ v)
∈-ₑ∘ₛ ∙        δ       v      = refl
∈-ₑ∘ₛ (drop σ) (δ , t) v      = ∈-ₑ∘ₛ σ δ v
∈-ₑ∘ₛ (keep σ) (δ , t) vz     = refl
∈-ₑ∘ₛ (keep σ) (δ , t) (vs v) = ∈-ₑ∘ₛ σ δ v

Tm-ₑ∘ₛ : ∀ {A Γ Δ Σ}(σ : OPE Δ Σ)(δ : Sub Γ Δ)(t : Tm Σ A) → Tmₛ (σ ₑ∘ₛ δ) t ≡ Tmₛ δ (Tmₑ σ t)
Tm-ₑ∘ₛ σ δ (var v) = ∈-ₑ∘ₛ σ δ v
Tm-ₑ∘ₛ σ δ (lam t) =
  lam & ((λ x → Tmₛ (x , var vz) t) & assₑₛₑ σ δ wk ◾ Tm-ₑ∘ₛ (keep σ) (keepₛ δ) t)
Tm-ₑ∘ₛ σ δ (app f a) = app & Tm-ₑ∘ₛ σ δ f ⊗ Tm-ₑ∘ₛ σ δ a
Tm-ₑ∘ₛ σ δ ⟨ x , x₁ ⟩ = cong-⟨,⟩ (Tm-ₑ∘ₛ σ δ x) (Tm-ₑ∘ₛ σ δ x₁)
Tm-ₑ∘ₛ σ δ (p₁ x) = p₁ & (Tm-ₑ∘ₛ σ δ x)
Tm-ₑ∘ₛ σ δ (p₂ x) = p₂ & (Tm-ₑ∘ₛ σ δ x)
Tm-ₑ∘ₛ σ δ ([]≡ x) = []≡ & (Tm-ₑ∘ₛ σ δ x)

∈-ₛ∘ₑ : ∀ {A Γ Δ Σ}(σ : Sub Δ Σ)(δ : OPE Γ Δ)(v : A ∈ Σ) → ∈ₛ (σ ₛ∘ₑ δ) v ≡ Tmₑ δ (∈ₛ σ v)
∈-ₛ∘ₑ (σ , _) δ vz     = refl
∈-ₛ∘ₑ (σ , _) δ (vs v) = ∈-ₛ∘ₑ σ δ v

Tm-ₛ∘ₑ : ∀ {A Γ Δ Σ}(σ : Sub Δ Σ)(δ : OPE Γ Δ)(t : Tm Σ A) → Tmₛ (σ ₛ∘ₑ δ) t ≡ Tmₑ δ (Tmₛ σ t)
Tm-ₛ∘ₑ σ δ (var v)   = ∈-ₛ∘ₑ σ δ v
Tm-ₛ∘ₑ σ δ (lam t)   =
  lam &
      ((λ x → Tmₛ (x , var vz) t) &
          (assₛₑₑ σ δ wk
        ◾ (σ ₛ∘ₑ_) & (drop & (idrₑ δ ◾ idlₑ δ ⁻¹))
        ◾ assₛₑₑ σ wk (keep δ) ⁻¹)
    ◾ Tm-ₛ∘ₑ (keepₛ σ) (keep δ) t)
Tm-ₛ∘ₑ σ δ (app f a) = app & Tm-ₛ∘ₑ σ δ f ⊗ Tm-ₛ∘ₑ σ δ a
Tm-ₛ∘ₑ σ δ ⟨ x , x₁ ⟩ = cong-⟨,⟩ (Tm-ₛ∘ₑ σ δ x) (Tm-ₛ∘ₑ σ δ x₁)
Tm-ₛ∘ₑ σ δ (p₁ x) = p₁ & (Tm-ₛ∘ₑ σ δ x)
Tm-ₛ∘ₑ σ δ (p₂ x) = p₂ & (Tm-ₛ∘ₑ σ δ x)
Tm-ₛ∘ₑ σ δ ([]≡ x) = []≡ & (Tm-ₛ∘ₑ σ δ x)

assₛₑₛ :
  ∀ {Γ Δ Σ Ξ}(σ : Sub Σ Ξ)(δ : OPE Δ Σ)(ν : Sub Γ Δ)
  → (σ ₛ∘ₑ δ) ∘ₛ ν ≡ σ ∘ₛ (δ ₑ∘ₛ ν)
assₛₑₛ ∙       δ ν = refl
assₛₑₛ (σ , t) δ ν = _,_ & assₛₑₛ σ δ ν ⊗ (Tm-ₑ∘ₛ δ ν t ⁻¹)

assₛₛₑ :
  ∀ {Γ Δ Σ Ξ}(σ : Sub Σ Ξ)(δ : Sub Δ Σ)(ν : OPE Γ Δ)
  → (σ ∘ₛ δ) ₛ∘ₑ ν ≡ σ ∘ₛ (δ ₛ∘ₑ ν)
assₛₛₑ ∙       δ ν = refl
assₛₛₑ (σ , t) δ ν = _,_ & assₛₛₑ σ δ ν ⊗ (Tm-ₛ∘ₑ δ ν t ⁻¹)

∈-idₛ : ∀ {A Γ}(v : A ∈ Γ) → ∈ₛ idₛ v ≡ var v
∈-idₛ vz     = refl
∈-idₛ (vs v) = ∈-ₛ∘ₑ idₛ wk v ◾ Tmₑ wk & ∈-idₛ v ◾ (var ∘ vs) & ∈-idₑ v

∈-∘ₛ : ∀ {A Γ Δ Σ}(σ : Sub Δ Σ)(δ : Sub Γ Δ)(v : A ∈ Σ) → ∈ₛ (σ ∘ₛ δ) v ≡ Tmₛ δ (∈ₛ σ v)
∈-∘ₛ (σ , _) δ vz     = refl
∈-∘ₛ (σ , _) δ (vs v) = ∈-∘ₛ σ δ v

Tm-idₛ : ∀ {A Γ}(t : Tm Γ A) → Tmₛ idₛ t ≡ t
Tm-idₛ (var v)   = ∈-idₛ v
Tm-idₛ (lam t)   = lam & Tm-idₛ t
Tm-idₛ (app f a) = app & Tm-idₛ f ⊗ Tm-idₛ a
Tm-idₛ ⟨ x , x₁ ⟩ = cong-⟨,⟩ (Tm-idₛ x) (Tm-idₛ x₁)
Tm-idₛ (p₁ x) = p₁ & (Tm-idₛ x)
Tm-idₛ (p₂ x) = p₂ & (Tm-idₛ x)
Tm-idₛ ([]≡ x) = []≡ & (Tm-idₛ x)

Tm-∘ₛ : ∀ {A Γ Δ Σ}(σ : Sub Δ Σ)(δ : Sub Γ Δ)(t : Tm Σ A) → Tmₛ (σ ∘ₛ δ) t ≡ Tmₛ δ (Tmₛ σ t)
Tm-∘ₛ σ δ (var v)   = ∈-∘ₛ σ δ v
Tm-∘ₛ σ δ (lam t)   =
  lam &
      ((λ x → Tmₛ (x , var vz) t) &
          (assₛₛₑ σ δ wk
        ◾ (σ ∘ₛ_) & (idlₑₛ  (dropₛ δ) ⁻¹) ◾ assₛₑₛ σ wk (keepₛ δ) ⁻¹)
    ◾ Tm-∘ₛ (keepₛ σ) (keepₛ δ) t)
Tm-∘ₛ σ δ (app f a) = app & Tm-∘ₛ σ δ f ⊗ Tm-∘ₛ σ δ a
Tm-∘ₛ σ δ ⟨ x , x₁ ⟩ = cong-⟨,⟩ (Tm-∘ₛ σ δ x) (Tm-∘ₛ σ δ x₁)
Tm-∘ₛ σ δ (p₁ x) = p₁ & (Tm-∘ₛ σ δ x)
Tm-∘ₛ σ δ (p₂ x) = p₂ & (Tm-∘ₛ σ δ x)
Tm-∘ₛ σ δ ([]≡ x) = []≡ & (Tm-∘ₛ σ δ x)

idrₛ : ∀ {Γ Δ}(σ : Sub Γ Δ) → σ ∘ₛ idₛ ≡ σ
idrₛ ∙       = refl
idrₛ (σ , t) = _,_ & idrₛ σ ⊗ Tm-idₛ t

idlₛ : ∀ {Γ Δ}(σ : Sub Γ Δ) → idₛ ∘ₛ σ ≡ σ
idlₛ ∙       = refl
idlₛ (σ , t) = (_, t) & (assₛₑₛ idₛ wk (σ , t) ◾ (idₛ ∘ₛ_) & idlₑₛ σ ◾ idlₛ σ)

-- Reduction
--------------------------------------------------------------------------------

data _~>_ {Γ} : ∀ {A} → Tm Γ A → Tm Γ A → Set where
  β    : ∀ {A B}(t : Tm (Γ , A) B) t'  → app (lam t) t' ~> Tmₛ (idₛ , t') t
  β-p₁ : ∀ {A B}{a : Tm Γ A}{b : Tm Γ B} → p₁ ⟨ a , b ⟩ ~> a
  β-p₂ : ∀ {A B}{a : Tm Γ A}{b : Tm Γ B} → p₂ ⟨ a , b ⟩ ~> b
  lam  : ∀ {A B}{t t' : Tm (Γ , A) B}     → t ~> t' →  lam t   ~> lam t'
  app₁ : ∀ {A B}{f}{f' : Tm Γ (A ⇒ B)}{a} → f ~> f' →  app f a ~> app f' a
  app₂ : ∀ {A B}{f : Tm Γ (A ⇒ B)} {a a'} → a ~> a' →  app f a ~> app f  a'
  ⟨,⟩₁ : ∀ {A B}{a}{a' : Tm Γ A}{b : Tm Γ B} → a ~> a' →  ⟨ a , b ⟩ ~> ⟨ a' , b ⟩
  ⟨,⟩₂ : ∀ {A B}{b}{b' : Tm Γ B}{a : Tm Γ A} → b ~> b' →  ⟨ a , b ⟩ ~> ⟨ a , b' ⟩
  pr₁ : ∀ {A B}{p}{p' : Tm Γ (A ⊠ B)} → p ~> p' → p₁ p ~> p₁ p'
  pr₂ : ∀ {A B}{p}{p' : Tm Γ (A ⊠ B)} → p ~> p' → p₂ p ~> p₂ p'
  β≡ : ∀ {A B}{p}{p' : Tm Γ (A ⊠ B)} → p ~> p' → []≡ p ~> []≡ p'
infix 3 _~>_

data _⇄_ {Γ} : ∀ {A} → Tm Γ A → Tm Γ A → Set where
  β⇄   : ∀ {A B}{a : Tm Γ A}{b : Tm Γ B} → []≡ ⟨ a , b ⟩ ⇄ ⟨ b , a ⟩
  lam  : ∀ {A B}{t t' : Tm (Γ , A) B}     → t ⇄ t' →  lam t ⇄ lam t'
  app₁ : ∀ {A B}{f}{f' : Tm Γ (A ⇒ B)}{a} → f ⇄ f' →  app f a ⇄ app f' a
  app₂ : ∀ {A B}{f : Tm Γ (A ⇒ B)} {a a'} → a ⇄ a' →  app f a ⇄ app f  a'
  ⟨,⟩₁ : ∀ {A B}{a}{a' : Tm Γ A}{b : Tm Γ B} → a ⇄ a' →  ⟨ a , b ⟩ ⇄ ⟨ a' , b ⟩
  ⟨,⟩₂ : ∀ {A B}{b}{b' : Tm Γ B}{a : Tm Γ A} → b ⇄ b' →  ⟨ a , b ⟩ ⇄ ⟨ a , b' ⟩
  pr₁ : ∀ {A B}{p}{p' : Tm Γ (A ⊠ B)} → p ⇄ p' → p₁ p ⇄ p₁ p'
  pr₂ : ∀ {A B}{p}{p' : Tm Γ (A ⊠ B)} → p ⇄ p' → p₂ p ⇄ p₂ p'
  β≡ : ∀ {A B}{p}{p' : Tm Γ (A ⊠ B)} → p ⇄ p' → []≡ p ⇄ []≡ p'
infix 3 _⇄_

~>ₛ : ∀ {Γ Δ A}{t t' : Tm Γ A}(σ : Sub Δ Γ) → t ~> t' → Tmₛ σ t ~> Tmₛ σ t'
~>ₛ σ (β t t') =
  coe ((app (lam (Tmₛ (keepₛ σ) t)) (Tmₛ σ t') ~>_) &
      (Tm-∘ₛ (keepₛ σ) (idₛ , Tmₛ σ t') t ⁻¹
    ◾ (λ x → Tmₛ (x , Tmₛ σ t') t) &
        (assₛₑₛ σ wk (idₛ , Tmₛ σ t')
      ◾ ((σ ∘ₛ_) & idlₑₛ idₛ ◾ idrₛ σ) ◾ idlₛ σ ⁻¹)
    ◾ Tm-∘ₛ (idₛ , t') σ t))
  (β (Tmₛ (keepₛ σ) t) (Tmₛ σ t'))
~>ₛ σ (lam  step) = lam  (~>ₛ (keepₛ σ) step)
~>ₛ σ (app₁ step) = app₁ (~>ₛ σ step)
~>ₛ σ (app₂ step) = app₂ (~>ₛ σ step)
~>ₛ σ β-p₁ = β-p₁
~>ₛ σ β-p₂ = β-p₂
~>ₛ σ (⟨,⟩₁ x) = ⟨,⟩₁ (~>ₛ σ x)
~>ₛ σ (⟨,⟩₂ x) = ⟨,⟩₂ (~>ₛ σ x)
~>ₛ σ (pr₁ x) = pr₁ (~>ₛ σ x)
~>ₛ σ (pr₂ x) = pr₂ (~>ₛ σ x)
~>ₛ σ (β≡ x) = β≡ (~>ₛ σ x)

⇄ₛ : ∀ {Γ Δ A}{t t' : Tm Γ A}(σ : Sub Δ Γ) → t ⇄ t' → Tmₛ σ t ⇄ Tmₛ σ t'
⇄ₛ σ (β⇄) = β⇄
⇄ₛ σ (lam  step) = lam  (⇄ₛ (keepₛ σ) step)
⇄ₛ σ (app₁ step) = app₁ (⇄ₛ σ step)
⇄ₛ σ (app₂ step) = app₂ (⇄ₛ σ step)
⇄ₛ σ (⟨,⟩₁ x) = ⟨,⟩₁ (⇄ₛ σ x)
⇄ₛ σ (⟨,⟩₂ x) = ⟨,⟩₂ (⇄ₛ σ x)
⇄ₛ σ (pr₁ x) = pr₁ (⇄ₛ σ x)
⇄ₛ σ (pr₂ x) = pr₂ (⇄ₛ σ x)
⇄ₛ σ (β≡ x) = β≡ (⇄ₛ σ x)


Tmₑ~> :
  ∀ {Γ Δ A}{t : Tm Γ A}{σ : OPE Δ Γ}{t'}
  → Tmₑ σ t ~> t' → ∃ λ t'' → (t ~> t'') × (Tmₑ σ t'' ≡ t')
Tmₑ~> {t = var x} ()
Tmₑ~> {t = lam t} (lam step) with Tmₑ~> step
... | t'' , (p , refl) = lam t'' , lam p , refl
Tmₑ~> {t = app (var v) a} (app₁ ())
Tmₑ~> {t = app (var v) a} (app₂ step) with Tmₑ~> step
... | t'' , (p , refl) = app (var v) t'' , app₂ p , refl
Tmₑ~> {t = app (app f a) a'}  (app₁ step) with Tmₑ~> step
... | t'' , (p , refl) = app t'' a' , app₁ p , refl
Tmₑ~> {t = app (app f a) a''} (app₂ step) with Tmₑ~> step
... | t'' , (p , refl) = app (app f a) t'' , app₂ p , refl
Tmₑ~> {t = app (lam f) a} {σ} (β _ _) =
  Tmₛ (idₛ , a) f , β _ _ ,
      Tm-ₛ∘ₑ (idₛ , a) σ f ⁻¹
    ◾ (λ x →  Tmₛ (x , Tmₑ σ a) f) & (idrₑₛ σ ⁻¹)
    ◾ Tm-ₑ∘ₛ (keep σ) (idₛ , Tmₑ σ a) f
Tmₑ~> {t = app (lam f) a} (app₁ (lam step)) with Tmₑ~> step
... | t'' , (p , refl) = app (lam t'') a , app₁ (lam p) , refl
Tmₑ~> {t = app (lam f) a} (app₂ step) with Tmₑ~> step
... | t'' , (p , refl) = app (lam f) t'' , app₂ p , refl
Tmₑ~> {t = app (p₁ x) a} (app₁ step) with Tmₑ~> step
... | t'' , (p , refl) = (app t'' a) , (app₁ p , refl)
Tmₑ~> {t = app (p₁ x) a} (app₂ step) with Tmₑ~> step
... | t'' , (p , refl) = (app (p₁ x) t'') , (app₂ p , refl)
Tmₑ~> {t = app (p₂ x) a} (app₁ step) with Tmₑ~> step
... | t'' , (p , refl) = (app t'' a) , (app₁ p , refl)
Tmₑ~> {t = app (p₂ x) a} (app₂ step) with Tmₑ~> step
... | t'' , (p , refl) = (app (p₂ x) t'') , (app₂ p , refl)
Tmₑ~> {t = ⟨ a , b ⟩} (⟨,⟩₁ step) with Tmₑ~> step
... | t'' , (p , refl) = ⟨ t'' , b ⟩ , ⟨,⟩₁ p , refl
Tmₑ~> {t = ⟨ a , b ⟩} (⟨,⟩₂ step) with Tmₑ~> step
... | t'' , (p , refl) = ⟨ a , t'' ⟩ , ⟨,⟩₂ p , refl
Tmₑ~> {t = p₁ ⟨ a , b ⟩} β-p₁ = a , β-p₁ , refl
Tmₑ~> {t = p₁ t} (pr₁ step) with Tmₑ~> step
... | t'' , (p , refl) = (p₁ t'') , (pr₁ p , refl)
Tmₑ~> {t = p₂ ⟨ a , b ⟩} β-p₂ = b , β-p₂ , refl
Tmₑ~> {t = p₂ t} (pr₂ step) with Tmₑ~> step
... | t'' , (p , refl) = (p₂ t'') , (pr₂ p , refl)
Tmₑ~> {t = []≡ t} (β≡ step) with Tmₑ~> step
... | t'' , (p , refl) = ([]≡ t'') , (β≡ p , refl)

Tmₑ⇄ :
  ∀ {Γ Δ A}{t : Tm Γ A}{σ : OPE Δ Γ}{t'}
  → Tmₑ σ t ⇄ t' → ∃ λ t'' → (t ⇄ t'') × (Tmₑ σ t'' ≡ t')
Tmₑ⇄ {t = var x} ()
Tmₑ⇄ {t = lam t} (lam step) with Tmₑ⇄ step
... | t'' , (p , refl) = lam t'' , lam p , refl
Tmₑ⇄ {t = app x a} (app₁ step) with Tmₑ⇄ step
... | t'' , (p , refl) = (app t'' a) , (app₁ p , refl)
Tmₑ⇄ {t = app x a} (app₂ step) with Tmₑ⇄ step
... | t'' , (p , refl) = (app x t'') , (app₂ p , refl)
Tmₑ⇄ {t = ⟨ a , b ⟩} (⟨,⟩₁ step) with Tmₑ⇄ step
... | t'' , (p , refl) = ⟨ t'' , b ⟩ , ⟨,⟩₁ p , refl
Tmₑ⇄ {t = ⟨ a , b ⟩} (⟨,⟩₂ step) with Tmₑ⇄ step
... | t'' , (p , refl) = ⟨ a , t'' ⟩ , ⟨,⟩₂ p , refl
Tmₑ⇄ {t = p₁ t} (pr₁ step) with Tmₑ⇄ step
... | t'' , (p , refl) = (p₁ t'') , (pr₁ p , refl)
Tmₑ⇄ {t = p₂ t} (pr₂ step) with Tmₑ⇄ step
... | t'' , (p , refl) = (p₂ t'') , (pr₂ p , refl)
Tmₑ⇄ {t = []≡ t} (β≡ step) with Tmₑ⇄ step
... | t'' , (p , refl) = ([]≡ t'') , (β≡ p , refl)
Tmₑ⇄ {t = []≡ ⟨ a , b ⟩} β⇄ = ⟨ b , a ⟩ , β⇄ , refl

-- Strong normalization
--------------------------------------------------------------------------------

-- strong normalization predicate
data SN {Γ A} (t : Tm Γ A) : Set where
  sn : (∀ {t'} → t ~> t' ⊎ t ⇄ t' → SN t') → SN t

-- SN annotated all the way down with a predicate on terms
data SN* {A} (P : ∀ {Γ} → Tm Γ A → Set) {Γ}(t : Tm Γ A) : Set where
  sn* : P t → (∀ {t'} → t ~> t' ⊎ t ⇄ t' → SN* P t') → SN* P t

SN*-SN : ∀ {Γ A}{P : ∀ {Γ} → Tm Γ A → Set}{t : Tm Γ A} → SN* P t → SN t
SN*-SN (sn* p q) = sn (λ st → SN*-SN (q st))


Tmᴾ : ∀ {A Γ} → Tm Γ A → Set
Tmᴾ {Γ = Γ} (lam t) =
  ∀ {Δ}(σ : OPE Δ Γ){u} → SN* Tmᴾ u → SN* Tmᴾ (Tmₛ (idₛ ₛ∘ₑ σ , u) t)
Tmᴾ {Γ = Γ} (⟨ a , b ⟩) = SN* Tmᴾ a × SN* Tmᴾ b
Tmᴾ _ = ⊤

-- the actual induction predicate used in the "fundamental theorem"
P : ∀ {A Γ} → Tm Γ A → Set
P = SN* Tmᴾ

Pₑ : ∀ {Γ Δ A}(σ : OPE Γ Δ){t : Tm Δ A} → P t → P (Tmₑ σ t)

Tmᴾₑ : ∀ {Γ Δ A}(σ : OPE Γ Δ){t : Tm Δ A} → Tmᴾ t → Tmᴾ (Tmₑ σ t)
Tmᴾₑ σ {lam t} tᴾ =
  λ δ {u} uᴾ → coe (P & ((λ x → Tmₛ (x , u) t) &
                   ((assₛₑₑ idₛ σ δ ⁻¹ ◾ (_ₛ∘ₑ δ) & idrₑₛ σ ⁻¹) ◾ assₑₛₑ σ idₛ δ)
                     ◾ Tm-ₑ∘ₛ _ _ t))
                   (tᴾ (σ ∘ₑ δ) uᴾ)
Tmᴾₑ σ {var _} tᴾ = tt
Tmᴾₑ σ {app _ _} tᴾ = tt
Tmᴾₑ σ {⟨ a , b ⟩} (aᴾ , bᴾ) = Pₑ σ aᴾ , Pₑ σ bᴾ
Tmᴾₑ σ {p₁ x} tᴾ = tt
Tmᴾₑ σ {p₂ x} tᴾ = tt
Tmᴾₑ σ {[]≡ x} tᴾ = tt

P~> : ∀ {Γ A}{t t' : Tm Γ A} → t ~> t' ⊎ t ⇄ t' → P t → P t'
P~> st (sn* p q) = q st

Pₑ σ (sn* p q) =
  sn* (Tmᴾₑ σ p) λ {(inj₁ st) → case Tmₑ~> st of λ {(t'' , st' , refl) → Pₑ σ (q (inj₁ st'))};
                    (inj₂ st) → case Tmₑ⇄ st of λ {(t'' , st' , refl) → Pₑ σ (q (inj₂ st'))}}

P-lam : ∀ {Γ A B}{t : Tm (Γ , A) B} → Tmᴾ (lam t) → P t → P (lam t)
P-lam lamtᴾ (sn* p q) =
  sn* lamtᴾ (λ {(inj₁ (lam st)) → P-lam (λ σ uᴾ → P~> (inj₁ (~>ₛ _ st)) (lamtᴾ σ uᴾ) ) (q (inj₁ st)) ;
                (inj₂ (lam st)) → P-lam (λ σ uᴾ → P~> (inj₂ (⇄ₛ _ st)) (lamtᴾ σ uᴾ) ) (q (inj₂ st))})

P-app : ∀ {Γ A B}{t : Tm Γ (A ⇒ B)}{u : Tm Γ A} → P t → P u → P (app t u)
P-app =
  ind-help
    (λ t u → P (app t u))
    (λ { {t} {u} (sn* tp tq) uᴾ f g →
      sn* tt (λ {(inj₁ (β t t'))  → coe ((λ x → P (Tmₛ (x , u) t)) & (idrₑₛ _ ⁻¹ ◾ idlₑₛ _))
                                (tp idₑ uᴾ) ;
                (inj₁ (app₁ st)) → f (inj₁ st) ;
                (inj₁ (app₂ st)) → g (inj₁ st) ;
                (inj₂ (app₁ st)) → f (inj₂ st) ;
                (inj₂ (app₂ st)) → g (inj₂ st)})})
  where
    ind-help : ∀ {Γ A B}(R : Tm Γ A → Tm Γ B → Set)
             → (∀ {t u} → P t → P u
                 → (∀ {t'} → t ~> t' ⊎ t ⇄ t' → R t' u)
                 → (∀ {u'} → u ~> u' ⊎ u ⇄ u' → R t u')
                → R t u)
             → ∀ {t u} → P t → P u → R t u
    ind-help R f (sn* tp tq) (sn* up uq) =
      f (sn* tp tq) (sn* up uq)
        (λ st → ind-help R f (tq st) (sn* up uq))
        (λ st → ind-help R f (sn* tp tq) (uq st))

P-⟨,⟩ : ∀ {Γ A B}{t : Tm Γ A}{u : Tm Γ B} → P t → P u → P (⟨ t , u ⟩)
P-⟨,⟩ =
  ind-help
    (λ t u → P (⟨ t , u ⟩))
    (λ { {t} {u} tᴾ uᴾ f g →
      sn* (tᴾ , uᴾ) (λ {(inj₁ (⟨,⟩₁ st)) → f (inj₁ st) ;
                        (inj₁ (⟨,⟩₂ st)) → g (inj₁ st) ;
                        (inj₂ (⟨,⟩₁ x)) → f (inj₂ x) ;
                        (inj₂ (⟨,⟩₂ x)) → g (inj₂ x)})})
  where
    ind-help : ∀ {Γ A B}(R : Tm Γ A → Tm Γ B → Set)
             → (∀ {t u} → P t → P u
                 → (∀ {t'} → t ~> t' ⊎ t ⇄ t' → R t' u)
                 → (∀ {u'} → u ~> u' ⊎ u ⇄ u' → R t u')
                → R t u)
             → ∀ {t u} → P t → P u → R t u
    ind-help R f (sn* tp tq) (sn* up uq) =
      f (sn* tp tq) (sn* up uq)
        (λ st → ind-help R f (tq st) (sn* up uq))
        (λ st → ind-help R f (sn* tp tq) (uq st))

P₁ : ∀ {Γ A B}{a : Tm Γ A}{b : Tm Γ B} → P ⟨ a , b ⟩ → P a
P₁ (sn* tp tq) = proj₁ tp

P₂ : ∀ {Γ A B}{a : Tm Γ A}{b : Tm Γ B} → P ⟨ a , b ⟩ → P b
P₂ (sn* tp tq) = proj₂ tp

λ⟨,⟩⇄⟨λ,λ⟩ : ∀ {Γ A B C}{a : Tm (Γ , C) A}{b : Tm (Γ , C) B} → P (lam ⟨ a , b ⟩) → P ⟨ lam a , lam b ⟩
λ⟨,⟩⇄⟨λ,λ⟩ {a = a} {b = b} (sn* tp tq) =
  sn* (P-lam (λ σ x → case tp σ x of λ {(sn* x _) → proj₁ x}) (P₁ (coe (P & (cong-⟨,⟩ (Tm-idₛ a) (Tm-idₛ b))) (tp wk {var vz} (sn* tt (λ {(inj₁ ()) ; (inj₂ ())}))))) ,
       P-lam (λ σ x → case tp σ x of λ {(sn* x _) → proj₂ x}) (P₂ (coe (P & (cong-⟨,⟩ (Tm-idₛ a) (Tm-idₛ b))) (tp wk {var vz} (sn* tt (λ {(inj₁ ()) ; (inj₂ ())}))))))
    λ {(inj₁ (⟨,⟩₁ (lam st))) → λ⟨,⟩⇄⟨λ,λ⟩ (tq (inj₁ (lam (⟨,⟩₁ st))))
     ; (inj₁ (⟨,⟩₂ (lam st))) → λ⟨,⟩⇄⟨λ,λ⟩ (tq (inj₁ (lam (⟨,⟩₂ st))))
     ; (inj₂ (⟨,⟩₁ (lam st))) → λ⟨,⟩⇄⟨λ,λ⟩ (tq (inj₂ (lam (⟨,⟩₁ st))))
     ; (inj₂ (⟨,⟩₂ (lam st))) → λ⟨,⟩⇄⟨λ,λ⟩ (tq (inj₂ (lam (⟨,⟩₂ st))))}

⟨a,b⟩⇄⟨b,a⟩ : ∀ {Γ A B}{a : Tm Γ A}{b : Tm Γ B} → P ⟨ a , b ⟩ → P ⟨ b , a ⟩
⟨a,b⟩⇄⟨b,a⟩ (sn* (ap , bp) tq) =
  sn* (bp , ap) (λ {(inj₁ (⟨,⟩₁ st)) → ⟨a,b⟩⇄⟨b,a⟩ (tq (inj₁ (⟨,⟩₂ st)))
                  ; (inj₁ (⟨,⟩₂ st)) → ⟨a,b⟩⇄⟨b,a⟩ (tq (inj₁ (⟨,⟩₁ st)))
                  ; (inj₂ (⟨,⟩₁ st)) → ⟨a,b⟩⇄⟨b,a⟩ (tq (inj₂ (⟨,⟩₂ st)))
                  ; (inj₂ (⟨,⟩₂ st)) → ⟨a,b⟩⇄⟨b,a⟩ (tq (inj₂ (⟨,⟩₁ st)))})

P-[] : ∀ {Γ A B}{t : Tm Γ (A ⊠ B)} → P t → P ([]≡ t)
P-[] (sn* tp tq) = sn* tt λ {(inj₁ (β≡ st)) → P-[] (tq (inj₁ st))
                           ; (inj₂ β⇄) → ⟨a,b⟩⇄⟨b,a⟩ (sn* tp tq)
                           ; (inj₂ (β≡ st)) → P-[] (tq (inj₂ st))}

P-p₁ : ∀ {Γ A B}{t : Tm Γ (A ⊠ B)} → P t → P (p₁ t)
P-p₁ (sn* tp tq) = sn* tt λ {(inj₁ (β-p₁)) → proj₁ tp
                           ; (inj₁ (pr₁ st)) → P-p₁ (tq (inj₁ st))
                           ; (inj₂ (pr₁ st)) → P-p₁ (tq (inj₂ st))}

P-p₂ : ∀ {Γ A B}{t : Tm Γ (A ⊠ B)} → P t → P (p₂ t)
P-p₂ (sn* tp tq) = sn* tt λ {(inj₁ (β-p₂)) → proj₂ tp
                           ; (inj₁ (pr₂ st)) → P-p₂ (tq (inj₁ st))
                           ; (inj₂ (pr₂ st)) → P-p₂ (tq (inj₂ st))}

data Subᴾ {Γ} : ∀ {Δ} → Sub Γ Δ → Set where
  ∙   : Subᴾ ∙
  _,_ : ∀ {A Δ}{σ : Sub Γ Δ}{t : Tm Γ A}(σᴾ : Subᴾ σ)(tᴾ : P t) → Subᴾ (σ , t)

Subᴾₑ : ∀ {Γ Δ Σ}{σ : Sub Δ Σ}(δ : OPE Γ Δ) → Subᴾ σ → Subᴾ (σ ₛ∘ₑ δ)
Subᴾₑ σ ∙        = ∙
Subᴾₑ σ (δ , tᴾ) = Subᴾₑ σ δ , Pₑ σ tᴾ

-- "fundamental theorem"

fth : ∀ {Γ A}(t : Tm Γ A) → ∀ {Δ}{σ : Sub Δ Γ} → Subᴾ σ → P (Tmₛ σ t)
fth (var vz) (σᴾ , tᴾ) = tᴾ
fth (var (vs x)) (σᴾ , tᴾ) = fth (var x) σᴾ
fth (lam t) {Δ}{σ} σᴾ =
  P-lam (λ δ {u} uᴾ →
          coe (P & ((λ x → Tmₛ (x , u) t)&
                       ((((_ₛ∘ₑ δ) & (idrₛ σ ⁻¹) ◾ assₛₛₑ σ idₛ δ)
                       ◾ (σ ∘ₛ_) & idlₑₛ (idₛ ₛ∘ₑ δ) ⁻¹)
                       ◾ assₛₑₛ σ wk (idₛ ₛ∘ₑ δ , u) ⁻¹) ◾ Tm-∘ₛ _ _ t))
              (fth t (Subᴾₑ δ σᴾ , uᴾ)))
        (fth t (Subᴾₑ wk σᴾ , sn* tt (λ {(inj₁ ()) ; (inj₂ ())})))
fth (app t u) σᴾ = P-app (fth t σᴾ) (fth u σᴾ)
fth ⟨ a , b ⟩ σᴾ = P-⟨,⟩ (fth a σᴾ) (fth b σᴾ)
fth (p₁ x) σᴾ = P-p₁ (fth x σᴾ)
fth (p₂ x) σᴾ = P-p₂ (fth x σᴾ)
fth ([]≡ x) σᴾ = P-[] (fth x σᴾ)

idₛᴾ : ∀ {Γ} → Subᴾ (idₛ {Γ})
idₛᴾ {∙}     = ∙
idₛᴾ {Γ , A} = Subᴾₑ wk idₛᴾ , sn* tt (λ {(inj₁ ()) ; (inj₂ ())})

strongNorm : ∀ {Γ A}(t : Tm Γ A) → SN t
strongNorm t = coe (SN & Tm-idₛ t) (SN*-SN (fth t idₛᴾ))
    