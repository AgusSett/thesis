module IsoType where

open import Type

infix  4 _≡_

data _≡_ : Type → Type → Set where
  comm : ∀ {A B} → A × B ≡ B × A
  asso : ∀ {A B C} → A × (B × C) ≡ (A × B) × C
  dist : ∀ {A B C} → (A ⇒ B) × (A ⇒ C) ≡ A ⇒ B × C
  curry : ∀ {A B C} → A ⇒ B ⇒ C ≡ (A × B) ⇒ C
  unit : ∀ {A} → A × ⊤ ≡ A
  unit2 : ∀ {A} → ⊤ ⇒ A ≡ A
  unit3 : ∀ {A} → A ⇒ ⊤ ≡ ⊤
  sym : ∀ {A B} → A ≡ B → B ≡ A