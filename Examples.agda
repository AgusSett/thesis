module Examples where

open import Type
open import Term
open import Subs hiding (⟪_⟫)
open import IsoType
open import IsoTerm
open import Reduction
open import Progress
open import Eval
open import StrongNorm using (SN; sn)
open import Relation.Binary.PropositionalEquality renaming (_≡_ to _≋_) hiding (sym; [_])
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)


------------------------------------------------------------------------
-- Type
------------------------------------------------------------------------

fun : Type
fun = ⊤ ⇒ ⊤

prod : Type
prod = fun × ⊤

------------------------------------------------------------------------
-- Context & Term
------------------------------------------------------------------------

_ : ∅ , ⊤ ⇒ ⊤ ⊢ ⊤ ⇒ ⊤
_ = ƛ (` S Z · (` S Z · ` Z)) -- λ x . y (y x)

_ : ∅ ⊢ (⊤ ⇒ ⊤) ⇒ ⊤ ⇒ ⊤
_ = ƛ ƛ (` S Z · (` S Z · ` Z)) -- λ y . λ x . y (y x)

T₁ : ∅ , ⊤ ⊢ fun
T₁ = ƛ ` Z -- λ x . x

T₂ : ∅ , ⊤ ⊢ prod
T₂ = ⟨ T₁ , ⋆ ⟩ -- ⟨ λ x . x , ⋆ ⟩

T₃ : ∅ , ⊤ ⊢ ⊤
T₃ = (π fun {inj₁ refl} T₂) · ` Z -- (π (⊤→⊤) ⟨ λ x . x , ⋆ ⟩) y

swap× : ∀ {A B} → ∅ ⊢ A × B ⇒ B × A
swap× {A} {B} = ƛ ⟨ π B {inj₂ refl} (` Z) , π A {inj₁ refl} (` Z) ⟩ -- λ x . ⟨ π B x , π A x ⟩

------------------------------------------------------------------------
-- Substitution
------------------------------------------------------------------------

M₀ : ∅ , ⊤ ⇒ ⊤ ⊢ ⊤ ⇒ ⊤
M₀ = ƛ (` S Z · (` S Z · ` Z)) -- λ 1 (1 0)

M₁ : ∅ , ⊤ ⇒ ⊤ , ⊤ ⊢ ⊤ ⇒ ⊤
M₁ = ƛ (` S S Z · (` S S Z · ` Z)) -- λ 2 (2 0)

_ : rename S_ M₀ ≋ M₁
_ = refl


M₂ : ∅ , ⊤ ⇒ ⊤ ⊢ ⊤ ⇒ ⊤
M₂ = ƛ ` S Z · (` S Z · ` Z) -- λ 1 (1 0)

M₃ : ∅ ⊢ ⊤ ⇒ ⊤
M₃ = ƛ ` Z -- λ 0

M₄ : ∅ ⊢ ⊤ ⇒ ⊤
M₄ = ƛ (ƛ ` Z) · ((ƛ ` Z) · ` Z) -- λ (λ 0) ((λ 0) 0)

_ : M₂ [ M₃ ] ≋ M₄
_ = refl

M₅ : ∅ , ⊤ ⇒ ⊤ , ⊤ ⊢ (⊤ ⇒ ⊤) ⇒ ⊤
M₅ = ƛ ` Z · ` S Z -- λ 0 1

M₆ : ∅ , ⊤ ⇒ ⊤ ⊢ ⊤
M₆ = ` Z · ⋆ -- 0 ⋆

M₇ : ∅ , ⊤ ⇒ ⊤ ⊢ (⊤ ⇒ ⊤) ⇒ ⊤
M₇ = ƛ (` Z · (` S Z · ⋆)) -- λ 0 (1 ⋆)

_ : M₅ [ M₆ ] ≋ M₇
_ = refl

------------------------------------------------------------------------
-- Reduction
------------------------------------------------------------------------

_ : T₃ ↪ T₁ · ` Z
_ = ξ-·₁ β-π₁

------------------------------------------------------------------------
-- IsoType
------------------------------------------------------------------------

_ : (⊤ × ⊤) ⇒ ⊤ ≡ ⊤ ⇒ ⊤ ⇒ ⊤
_ = sym curry

_ : ∀ {A B} → A × B ⇒ ⊤ ≡ B × A ⇒ ⊤
_ = cong⇒₁ comm

_ : ∀ {Γ A B} → Γ ⊢ (A × B ⇒ B × A)
_ = [ cong⇒₂ comm ]≡ (ƛ ` Z)

_ : ∀ {Γ A B C} → Γ , C ⊢ (C × (A × B ⇒ A)) × (A × B ⇒ B)
_ = [ asso ]≡ ⟨ ` Z , [ sym dist ]≡ (ƛ ` Z) ⟩

_ : ∀ {Γ A B} → Γ ⊢ (A × B ⇒ B × A)
_ = [ dist ]≡ ([ comm ]≡ ([ sym dist ]≡ (ƛ ` Z)))

_ : ∀ {Γ A B} → Γ ⊢ (A × B) ⇒ ⊤
_ = (([ sym curry ]≡ ([ cong⇒₁ comm ]≡ ([ curry ]≡ ([ curry ]≡ (ƛ ƛ ƛ ` Z))))) · ⋆)

T₄ : ∀ {A B} → ∅ ⊢ (A ⇒ B ⇒ A) × (A ⇒ B ⇒ B)
T₄ = [ sym dist ]≡ (ƛ [ sym dist ]≡ (ƛ ⟨ ` (S Z) , ` Z ⟩))

T₅ : ∀ {Γ} → Γ ⊢ ⊤
T₅ = π _ {inj₁ refl} ([ sym dist ]≡ ([ curry ]≡ (ƛ ƛ ⟨ ` (S Z) , ` Z ⟩))) · ⟨ ⋆ , ⋆ ⟩

------------------------------------------------------------------------
-- IsoTerm
------------------------------------------------------------------------

_ : [ comm ]≡ T₂ ⇄ ⟨ ⋆ , ƛ ` Z ⟩
_ = comm

_ : ⟨ ⋆ , [ comm ]≡ T₂ ⟩ ⇄ ⟨ ⋆ , ⟨ ⋆ , ƛ ` Z ⟩ ⟩
_ = ξ-⟨,⟩₂ comm

_ : ∀ {A B} → T₄ {A} {B} ⇄ [ sym dist ]≡ (ƛ ⟨ ƛ ` (S Z) , ƛ ` Z ⟩)
_ = ξ-≡ (ζ sym-dist-ƛ)

------------------------------------------------------------------------
-- StrongNorm
------------------------------------------------------------------------

SN⋆ : ∀ {Γ} → SN {Γ} ⋆
SN⋆ = sn λ {(inj₁ ())
          ; (inj₂ ())}

SN⟨,⟩ : ∀ {Γ A} → SN {Γ , A} ⟨ ⋆ , ` Z ⟩
SN⟨,⟩ = sn λ {(inj₁ (ξ-⟨,⟩₁ ()))
            ; (inj₁ (ξ-⟨,⟩₂ ()))
            ; (inj₂ (ξ-⟨,⟩₁ ()))
            ; (inj₂ (ξ-⟨,⟩₂ ()))}

SNπ : ∀ {Γ A} → SN {Γ , A} (π ⊤ {inj₁ refl} ⟨ ⋆ , ` Z ⟩)
SNπ = sn λ {(inj₁ (ξ-π (ξ-⟨,⟩₁ ())))
          ; (inj₁ (ξ-π (ξ-⟨,⟩₂ ())))
          ; (inj₁ β-π₁) → SN⋆
          ; (inj₂ (ξ-π (ξ-⟨,⟩₁ ())))
          ; (inj₂ (ξ-π (ξ-⟨,⟩₂ ())))}

------------------------------------------------------------------------
-- Progress
------------------------------------------------------------------------

_ : progress T₃ ≋ step↪ (ξ-·₁ β-π₁)
_ = refl

_ :  ∀ {A B} → progress (T₄ {A} {B}) ≋ step⇄ (ξ-≡ (ζ sym-dist-ƛ))
_ = refl

_ : progress T₂ ≋ done N-⟨ N-ƛ , N-⋆ ⟩
_ = refl

------------------------------------------------------------------------
-- Evaluation
------------------------------------------------------------------------

T₅⇝⋆ : ∀ {Γ} → T₅ {Γ} ⇝* ⋆
T₅⇝⋆ =
    π _ ([ sym dist ]≡ ([ curry ]≡ (ƛ (ƛ ⟨ ` (S Z) , ` Z ⟩)))) · ⟨ ⋆ , ⋆ ⟩
      ⇄⟨ ξ-·₁ (ξ-π (ξ-≡ curry)) ⟩
    π _ ([ sym dist ]≡ (ƛ ⟨ π ⊤ (` Z) , π ⊤ (` Z) ⟩)) · ⟨ ⋆ , ⋆ ⟩
      ⇄⟨ ξ-·₁ (ξ-π sym-dist-ƛ) ⟩
    π _ ⟨ ƛ π ⊤ (` Z) , ƛ π ⊤ (` Z) ⟩ · ⟨ ⋆ , ⋆ ⟩
      ↪⟨ ξ-·₁ β-π₁ ⟩
    (ƛ π ⊤ (` Z)) · ⟨ ⋆ , ⋆ ⟩
      ↪⟨ β-ƛ ⟩
    π ⊤ ⟨ ⋆ , ⋆ ⟩
      ↪⟨ β-π₁ ⟩
    ⋆
  ∎

-- Ω = (λx:T.xx)(λx:T.xx) : T
Ω : ∅ ⊢ ⊤
Ω = (ƛ [ sym abs ]≡ (` Z) · ` Z) · ([ abs ]≡ (ƛ [ sym abs ]≡ (` Z) · ` Z))

Ω⇝⋆ : Ω ⇝* ⋆
Ω⇝⋆ =
    Ω
      ⇄⟨ ξ-·₁ (ζ (ξ-·₁ sym-abs)) ⟩
    (ƛ (ƛ ` (S Z)) · ` Z) · ([ abs ]≡ (ƛ ([ sym abs ]≡ (` Z)) · ` Z))
      ↪⟨ ξ-·₁ (ζ β-ƛ) ⟩
    (ƛ ` Z) · ([ abs ]≡ (ƛ ([ sym abs ]≡ (` Z)) · ` Z))
      ⇄⟨ ξ-·₂ (ξ-≡ (ζ (ξ-·₁ sym-abs))) ⟩
    (ƛ ` Z) · ([ abs ]≡ (ƛ (ƛ ` (S Z)) · ` Z))
      ↪⟨ ξ-·₂ (ξ-≡ (ζ β-ƛ)) ⟩
    (ƛ ` Z) · ([ abs ]≡ (ƛ ` Z))
      ⇄⟨ ξ-·₂ abs ⟩
    (ƛ ` Z) · ⋆
      ↪⟨ β-ƛ ⟩
    ⋆
  ∎

_ : eval Ω ≋ steps Ω⇝⋆ V-⋆
_ = refl

Ω' : ∅ ⊢ ⊤
Ω' = (ƛ [ sym id-⇒ ]≡ (` Z) · ` Z) · ([ id-⇒ ]≡ (ƛ [ sym id-⇒ ]≡ (` Z) · ` Z))

-- pair encoding

⟨a,a⟩-π₁ : ∀ {A} → π {∅ , A , A} A ⟨ ` Z , ` S Z ⟩ ⇝* ` Z
⟨a,a⟩-π₁ {A} =
  begin
    π A ⟨ ` Z , ` S Z ⟩
      ↪⟨ β-π₁ ⟩
    ` Z
  ∎

⟨a,a⟩-π₂ : ∀ {A} → π {∅ , A , A} A ⟨ ` Z , ` S Z ⟩ ⇝* ` S Z
⟨a,a⟩-π₂ {A} =
  begin
    π A ⟨ ` Z , ` S Z ⟩
      ↪⟨ β-π₂ ⟩
    ` S Z
  ∎


⟦_⟧_ : ∀ {Γ B} → (r : Γ ⊢ B) → (A : Type) → Γ ⊢ (A ⇒ A) ⇒ B
⟦ r ⟧ A = ƛ rename S_ r

_⟪_⟫ : ∀ {Γ B} → (A : Type) → (r : Γ ⊢ (A ⇒ A) ⇒ B) → Γ ⊢ B
A ⟪ r ⟫ = r · (ƛ ` Z)

One : Type
One = ⊤

Two : Type
Two = ⊤ ⇒ ⊤

encode : ∀ {Γ A B} → (r : Γ ⊢ A) (s : Γ ⊢ B) → Γ ⊢ ((One ⇒ One) ⇒ A) × ((Two ⇒ Two) ⇒ B)
encode r s = ⟨ ⟦ r ⟧ One , ⟦ s ⟧ Two ⟩

π₁ : ∀ {Γ A B} → (Γ ⊢ ((One ⇒ One) ⇒ A) × ((Two ⇒ Two) ⇒ B)) → Γ ⊢ A
π₁ {A = A} x = One ⟪ π ((One ⇒ One) ⇒ A) {inj₁ refl} x ⟫

encode-π₁ : ∀ {A} → π₁ {∅ , A , A} (encode (` Z) (` S Z)) ⇝* ` Z
encode-π₁ {A} =
  begin
    π₁ (encode (` Z) (` S Z))
      ↪⟨ ξ-·₁ β-π₁ ⟩
    (ƛ ` (S Z)) · (ƛ ` Z)
      ↪⟨ β-ƛ ⟩
    ` Z
  ∎ 