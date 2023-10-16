module Type where

infixr 7 _⇒_
infixr 9 _×_

data Type : Set where
  τ    : Type
  ⊤    : Type
  _⇒_ : Type → Type → Type
  _×_  : Type → Type → Type
