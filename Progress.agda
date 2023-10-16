module Progress where

open import Term
open import Type
open import IsoType
open import IsoTerm
open import Reduction
open import Subs
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (refl)

data Progress {Γ A} (M : Γ ⊢ A) : Set where

  step⇄ : ∀ {N : Γ ⊢ A}
    → M ⇄ N
      ----------
    → Progress M
  
  step↪ : ∀ {N : Γ ⊢ A}
    → M ↪ N
      ----------
    → Progress M
  
  done :
      ⇑ M
      ----------
    → Progress M

progress : ∀ {Γ A} → (M : Γ ⊢ A) → Progress M
progress (` x) = done (^ (` x))
progress ⋆ = done N-⋆

progress ([ iso ]≡ N) with progress N
... | step⇄ N⇄N' = step⇄ (ξ-≡ N⇄N')
... | step↪ N↪N' = step↪ (ξ-≡ N↪N')
progress ([ comm ]≡ _)      | done N-⟨ NN , NM ⟩ = step⇄ comm
progress ([ sym comm ]≡ _)  | done N-⟨ NN , NM ⟩ = step⇄ (sym-comm)

progress ([ asso ]≡ _)      | done N-⟨ NN , N-⟨ NM₁ , NM₂ ⟩ ⟩  = step⇄ asso
progress ([ asso ]≡ _)      | done N-⟨ NN , NM ⟩               = step⇄ (asso-split)
progress ([ sym asso ]≡ _)  | done N-⟨ N-⟨ NN₁ , NN₂ ⟩ , NM ⟩  = step⇄ (sym-asso)
progress ([ sym asso ]≡ _)  | done N-⟨ NN , NM ⟩               = step⇄ (sym-asso-split)

progress ([ dist ]≡ _) | done N-⟨ N-ƛ , N-ƛ ⟩  = step⇄ dist-ƛ
progress ([ dist ]≡ _) | done N-⟨ N-ƛ , NM ⟩   = step⇄ (dist-ƛηᵣ)
progress ([ dist ]≡ _) | done N-⟨ NN , N-ƛ ⟩   = step⇄ (dist-ƛηₗ)
progress ([ dist ]≡ _) | done N-⟨ NN , NM ⟩    = step⇄ (dist-ƛηₗᵣ)
progress ([ sym dist ]≡ (ƛ ⟨ NN , NM ⟩))  | done N-ƛ = step⇄ (sym-dist-ƛ)
progress ([ sym dist ]≡ (ƛ NN))           | done N-ƛ = step⇄ (sym-dist-ƛ-split)


progress ([ curry ]≡ (ƛ ƛ _))  | done N-ƛ  = step⇄ curry
progress ([ curry ]≡ _)        | done N-ƛ  = step⇄ (curry-η)
progress ([ sym curry ]≡ _)    | done N-ƛ  = step⇄ uncurry

progress ([ id-× ]≡ _)       | done N-⟨ NN , NM ⟩  = step⇄ id-×
progress ([ id-⇒ ]≡ _)      | done NN             = step⇄ id-⇒
progress ([ sym id-× ]≡ N)   | done NN             = step⇄ (sym-id-×)
progress ([ sym id-⇒ ]≡ N)  | done NN             = step⇄ sym-id-⇒

progress ([ abs ]≡ N)      | done NN = step⇄ abs
progress ([ sym abs ]≡ N)  | done NN = step⇄ (sym-abs)

progress ([ cong⇒₁ iso ]≡ _) | done N-ƛ = step⇄ cong⇒₁
progress ([ cong⇒₂ iso ]≡ _) | done N-ƛ = step⇄ cong⇒₂
progress ([ cong×₁ iso ]≡ _) | done N-⟨ NN , NM ⟩ = step⇄ cong×₁
progress ([ cong×₂ iso ]≡ _) | done N-⟨ NN , NM ⟩ = step⇄ cong×₂
progress ([ sym (cong⇒₁ iso) ]≡ _) | done N-ƛ = step⇄ sym-cong⇒₁
progress ([ sym (cong⇒₂ iso) ]≡ _) | done N-ƛ = step⇄ sym-cong⇒₂
progress ([ sym (cong×₁ iso) ]≡ _) | done N-⟨ NN , NM ⟩ = step⇄ sym-cong×₁
progress ([ sym (cong×₂ iso) ]≡ _) | done N-⟨ NN , NM ⟩ = step⇄ sym-cong×₂

progress ([ sym (sym iso) ]≡ N) | done NN = step⇄ sym-sym
progress ([ iso ]≡ N) | done (^ NN) = done (^ [ iso ]≡ NN)

progress (ƛ N) with progress N
... | step⇄ N⇄N'  = step⇄ (ζ N⇄N')
... | step↪ N↪N'  = step↪ (ζ N↪N')
... | done NN      = done N-ƛ

progress (L · M) with progress L
... | step⇄ L⇄L'     = step⇄ (ξ-·₁ L⇄L')
... | step↪ L↪L'     = step↪ (ξ-·₁ L↪L')
progress (L · M) | done (^ NeuL) with progress M
...    | step⇄ M⇄M'  = step⇄ (ξ-·₂ M⇄M')
...    | step↪ M↪M'  = step↪ (ξ-·₂ M↪M')
...    | done NM     = done (^ (NeuL · NM))
progress ((ƛ _) · M) | done N-ƛ with progress M
...    | step⇄ M⇄M'  = step⇄ (ξ-·₂ M⇄M')
...    | step↪ M↪M'  = step↪ (ξ-·₂ M↪M')
...    | done NM     = step↪ β-ƛ

progress ⟨ M , N ⟩ with progress M
... | step⇄ M⇄M' = step⇄ (ξ-⟨,⟩₁ M⇄M')
... | step↪ M↪M' = step↪ (ξ-⟨,⟩₁ M↪M')
... | done NM with progress N
...    | step⇄ N⇄N'  = step⇄ (ξ-⟨,⟩₂ N⇄N')
...    | step↪ N↪N'  = step↪ (ξ-⟨,⟩₂ N↪N')
...    | done NN     = done N-⟨ NM , NN ⟩

progress (π _ {p} N) with progress N
... | step⇄ N⇄N'  = step⇄ (ξ-π N⇄N')
... | step↪ N↪N'  = step↪ (ξ-π N↪N')
... | done (^ x)  = done (^ π x)
progress (π _ {inj₁ refl} N) | done N-⟨ NN , NM ⟩ = step↪ β-π₁
progress (π _ {inj₂ refl} N) | done N-⟨ NN , NM ⟩ = step↪ β-π₂
