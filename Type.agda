module Type where

infixr 7 _⇒_
infixr 9 _×_

data Type : Set where
  τ    : Type
  ⊤    : Type
  _⇒_ : Type → Type → Type
  _×_  : Type → Type → Type


{-
open import Relation.Binary.PropositionalEquality renaming (_≡_ to _≈_)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Product using (proj₁; proj₂; _,_) renaming (_×_ to _×1_)
open import Data.Sum 

cong-⇒ : ∀ {A B C D : Type} → A ⇒ B ≈ C ⇒ D → A ≈ C ×1 B ≈ D
cong-⇒ refl = refl , refl

cong-× : ∀ {A B C D : Type} → A × B ≈ C × D → A ≈ C ×1 B ≈ D
cong-× refl = refl , refl

_≟_ : ∀ (A B : Type) → Dec (A ≈ B)
τ ≟ τ = yes refl
τ ≟ ⊤ = no (λ ())
τ ≟ (B ⇒ B₁) = no (λ ())
τ ≟ (B × B₁) = no (λ ())
⊤ ≟ τ = no (λ ())
⊤ ≟ ⊤ = yes refl
⊤ ≟ (B ⇒ B₁) = no (λ ())
⊤ ≟ (B × B₁) = no (λ ())
(A ⇒ A₁) ≟ τ = no (λ ())
(A ⇒ A₁) ≟ ⊤ = no (λ ())
(A ⇒ B) ≟ (C ⇒ D) with A ≟ C | B ≟ D
((A ⇒ B) ≟ (.A ⇒ .B)) | yes refl | yes refl = yes refl
((A ⇒ B) ≟ (C ⇒ D))   | _        | no ¬p    = no (λ x → ¬p (proj₂ (cong-⇒ x)))
((A ⇒ B) ≟ (C ⇒ D))   | no ¬p    | _        = no (λ x → ¬p (proj₁ (cong-⇒ x)))
(A ⇒ A₁) ≟ (B × B₁) = no (λ ())
(A × A₁) ≟ τ = no (λ ())
(A × A₁) ≟ ⊤ = no (λ ())
(A × A₁) ≟ (B ⇒ B₁) = no (λ ())
(A × B) ≟ (C × D) with A ≟ C | B ≟ D
((A × B) ≟ (C × D)) | yes refl | yes refl = yes refl
((A × B) ≟ (C × D)) | _        | no ¬p    = no (λ x → ¬p (proj₂ (cong-× x)))
((A × B) ≟ (C × D)) | no ¬p    | _        = no (λ x → ¬p (proj₁ (cong-× x)))
-}