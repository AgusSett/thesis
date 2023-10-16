module IsoType where

open import Type

infix 4 _≡_

data _≡_ : Type → Type → Set where
  comm  : ∀ {A B} → A × B ≡ B × A
  asso  : ∀ {A B C} → A × (B × C) ≡ (A × B) × C
  dist  : ∀ {A B C} → (A ⇒ B) × (A ⇒ C) ≡ A ⇒ B × C
  curry : ∀ {A B C} → A ⇒ B ⇒ C ≡ (A × B) ⇒ C
  id-×  : ∀ {A} → A × ⊤ ≡ A
  id-⇒ : ∀ {A} → ⊤ ⇒ A ≡ A
  abs   : ∀ {A} → A ⇒ ⊤ ≡ ⊤

  sym     : ∀ {A B} → A ≡ B → B ≡ A
  cong⇒₁ : ∀ {A B C} → A ≡ B → A ⇒ C ≡ B ⇒ C
  cong⇒₂ : ∀ {A B C} → A ≡ B → C ⇒ A ≡ C ⇒ B
  cong×₁  : ∀ {A B C} → A ≡ B → A × C ≡ B × C
  cong×₂  : ∀ {A B C} → A ≡ B → C × A ≡ C × B
