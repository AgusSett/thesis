module IsoTerm where

open import IsoType
open import Type
open import Term

infix  4 _⇄_

-- (3) This realtion eliminates the [_]≡_ from the terms
data _⇄_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where
  comm : ∀ {Γ A B} → {r : Γ ⊢ A} → {s : Γ ⊢ B}
    → [ comm ]≡ ⟨ r , s ⟩ ⇄ ⟨ s , r ⟩
  asso : ∀ {Γ A B C} → {r : Γ ⊢ A} → {s : Γ ⊢ B} → {t : Γ ⊢ C}
    → [ asso ]≡ ⟨ r , ⟨ s , t ⟩ ⟩ ⇄ ⟨ ⟨ r , s ⟩ , t ⟩
  dist-ƛ : ∀ {Γ A B C} → {r : Γ , C ⊢ A} → {s : Γ , C ⊢ B}
    → [ dist ]≡ ⟨ ƛ r , ƛ s ⟩ ⇄ ƛ ⟨ r , s ⟩
  dist-· : ∀ {Γ A B C} → {r : Γ ⊢ C ⇒ A} → {s : Γ ⊢ C ⇒ B} → {t : Γ ⊢ C}
    → [ dist ]≡ ⟨ r , s ⟩ · t ⇄ ⟨ r · t , s · t ⟩
  curry : ∀ {Γ A B C} → {r : Γ ⊢ A ⇒ B ⇒ C} → {s : Γ ⊢ A} → {t : Γ ⊢ B}
    → [ curry ]≡ r · ⟨ s , t ⟩ ⇄ r · s · t
  curry2 : ∀ {Γ A B C} → {r : Γ ⊢ A × B ⇒ C} → {s : Γ ⊢ A} → {t : Γ ⊢ B}
    → [ sym curry ]≡ r · s · t ⇄ r · ⟨ s , t ⟩
--  unit : ∀ {Γ A} → {r : Γ ⊢ A}
--    → [ unit ]≡ ⟨ r , ⋆ ⟩ ⇄ r
--  unit2 : ∀ {Γ A} → {r : Γ ⊢ ⊤ ⇒ A}
--    → [ unit2 ]≡ r ⇄ r · ⋆
--  unit3 : ∀ {Γ A} → {r : Γ , A ⊢ ⊤}
--    → [ unit3 ]≡ (ƛ r) ⇄ ⋆

  sym : ∀ {Γ A B} → {r : Γ ⊢ A} → {s : Γ ⊢ B} → {iso : A ≡ B}
    → [ iso ]≡ r ⇄ s
    → [ sym iso ]≡ s ⇄ r
  
  ξ-·₁ : ∀ {Γ A B} {L L' : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
    → L ⇄ L'
    → L · M ⇄ L' · M

  ξ-·₂ : ∀ {Γ A B} {L : Γ ⊢ A ⇒ B} {M M' : Γ ⊢ A}
    → M ⇄ M'
    → L · M ⇄ L · M'
  
  ξ-⟨,⟩₁ : ∀ {Γ A B} {M M' : Γ ⊢ A} {N : Γ ⊢ B}
    → M ⇄ M'
    → ⟨ M , N ⟩ ⇄ ⟨ M' , N ⟩

  ξ-⟨,⟩₂ : ∀ {Γ A B} {M : Γ ⊢ A} {N N' : Γ ⊢ B}
    → N ⇄ N'
    → ⟨ M , N ⟩ ⇄ ⟨ M , N' ⟩

  ξ-proj : ∀ {Γ A B C p} {L L' : Γ ⊢ A × B}
    → L ⇄ L'
    → proj C {p} L ⇄ proj C {p} L'
  
  ξ-≡ : ∀ {Γ A B} {L L' : Γ ⊢ A} {iso : A ≡ B}
    → L ⇄ L'
    → ([ iso ]≡ L) ⇄ ([ iso ]≡ L')
  
  ξ-ƛ : ∀ {Γ A B} {L L' : Γ , B ⊢ A}
    → L ⇄ L'
    → ƛ L ⇄ ƛ L'

data Progress {Γ A} (M : Γ ⊢ A) : Set where

  step : ∀ {N : Γ ⊢ A}
    → M ⇄ N
      ----------
    → Progress M

  nothing : Progress M


symmetric : ∀ {Γ A} → (M : Γ ⊢ A) → Progress M
symmetric (` x)                             = nothing
symmetric ⋆                                 = nothing
symmetric ([ comm ]≡ ⟨ r , s ⟩)             = step comm
symmetric ([ asso ]≡ ⟨ r , ⟨ s , t ⟩ ⟩)     = step asso
symmetric ([ dist ]≡ ⟨ ƛ r , ƛ s ⟩)         = step dist-ƛ
symmetric ([ dist ]≡ ⟨ r , s ⟩ · t)         = step dist-·
symmetric ([ curry ]≡ r · ⟨ s , t ⟩)        = step curry
-- symmetric ([ unit ]≡ x) = {!   !}
-- symmetric ([ unit2 ]≡ x) = {!   !}
-- symmetric ([ unit3 ]≡ x) = {!   !}
symmetric ([ sym comm ]≡ ⟨ r , s ⟩)         = step (sym comm)
symmetric ([ sym asso ]≡ ⟨ ⟨ r , s ⟩ , t ⟩) = step (sym asso)
symmetric ([ sym dist ]≡ (ƛ ⟨ r , s ⟩))     = step (sym dist-ƛ)
symmetric ([ sym curry ]≡ r · s · t)        = step (curry2)
symmetric ([ iso ]≡ N) with symmetric N
...    | step N⇄M = step (ξ-≡ N⇄M)
...    | nothing = nothing
symmetric (ƛ N) with symmetric N
...    | step N⇄M = step (ξ-ƛ N⇄M)
...    | nothing = nothing
symmetric (L · M) with symmetric L
...    | step L⇄L'                          = step (ξ-·₁ L⇄L')
...    | nothing with symmetric M
...        | step M⇄M'                      = step (ξ-·₂ M⇄M')
...        | nothing                        = nothing
symmetric ⟨ M , N ⟩ with symmetric M
...    | step M⇄M'                          = step (ξ-⟨,⟩₁ M⇄M')
...    | nothing with symmetric N
...        | step N⇄N'                      = step (ξ-⟨,⟩₂ N⇄N')
...        | nothing                        = nothing
symmetric (proj C N) with symmetric N
...    | step N⇄N'                          = step (ξ-proj N⇄N')
...    | nothing                            = nothing 