module StrongNorm where

open import Function.Base using (_∘_; case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; cong₂; refl; sym; trans) renaming (subst to transport)
open import Data.Product using (∃; proj₁; proj₂) renaming (_,_ to ﹙_,_﹚; _×_ to _⊗_)
open import Data.Sum

open import Term
open import Type
open import Reduction
open import IsoTerm
open import Subs


data SN {Γ A} (t : Γ ⊢ A) : Set where
  sn : (∀ {t'} → t ↪ t' ⊎ t ⇄ t' → SN t') → SN t

-- Esta definicion es igual a SN pero se agrega una propiedad P que se debe cumplir para t.

data SN* {Γ A} (P : Γ ⊢ A → Set) (t : Γ ⊢ A) : Set where
  sn* : P t → (∀ {t'} → t ↪ t' ⊎ t ⇄ t' → SN* P t') → SN* P t


open import Data.Unit using (tt) renaming (⊤ to Top)

{-
  Esta es la propiedad que vamos a usar en SN*
  La principal diferencia con la prueba de reducibility candidates es que predica sobre terminos en lugar
  de tipos y ademas tenemos
    ∀ u → ⟦ u ⟧ → ⟦ t [ u ] ⟧
  en lugar de
    ∀ u → ⟦ u ⟧ → ⟦ t · u ⟧

  Otra particularidad es aparece un rename ρ, ∀ ρ u → ⟦ u ⟧ → ⟦ (rename ρ t) [ u ] ⟧
  esto es necesario para poder hacer la prueba de Γ ⊨ σ → (Γ , A) ⊨ (exts σ), es decir,
  la extensión de una substitución adecuada también es una substitución adecuada.
-}

⟦_⟧ : ∀ {Γ A} → Γ ⊢ A → Set
⟦ (ƛ t) ⟧ = ∀ {Δ}{ρ : Rename _ Δ}{u} → SN* ⟦_⟧ u → SN* ⟦_⟧ (⟪ u • (ids ∘ ρ) ⟫ t)
⟦ ⟨ a , b ⟩ ⟧ = SN* ⟦_⟧ a ⊗ SN* ⟦_⟧ b
⟦ t ⟧ = Top

-- Definición de las substituciónes adecuadas

_⊨_ : ∀{Δ} → (Γ : Context) → (σ : Subst Γ Δ) → Set
Γ ⊨ σ = ∀{A} (v : Γ ∋ A) → SN* ⟦_⟧ (σ {A} v)


SN*-SN : ∀ {Γ A} {t : Γ ⊢ A} → SN* ⟦_⟧ t → SN t
SN*-SN (sn* Lt SNt) = sn (λ step → SN*-SN (SNt step))

{-
  Todo esto es necesario para probar ⊨exts
  El Rename ρ que aparecia en ⟦_⟧ es necesario para probar ⟦⟧-rename, ya que como ocurre en varias partes de
  la prueba, estamos obligados a probar una generalización para poder destrabar algún caso.

  ⊨exts va a ser necesario porque en adequacy (ƛ n) necesitamos SN n, en reducibility candidates no es necesario
  esto ya que usa 'atom' en ∀ u → ⟦ u ⟧ → ⟦ t [ u ] ⟧ para cerrar el termino t.
-}

rename↪ : ∀ {Γ Δ A}{t : Γ ⊢ A}{σ : Rename Γ Δ}{t'} → (rename σ t) ↪ t' → ∃ λ t'' → (t ↪ t'') ⊗ (rename σ t'' ≡ t')
rename↪ {t = ƛ t} (ζ step) with rename↪ step
... | ﹙ _ , ﹙ step , refl ﹚ ﹚ = ﹙ _ , ﹙ ζ step , refl ﹚ ﹚
rename↪ {t = (ƛ a) · b} β-ƛ = ﹙ a [ b ] , ﹙ β-ƛ , (rename-subst-commute {N = a} {M = b}) ﹚ ﹚
rename↪ {t = f · b} (ξ-·₂ step) with rename↪ step
... | ﹙ _ , ﹙ step , refl ﹚ ﹚ = ﹙ _ , ﹙ ξ-·₂ step , refl ﹚ ﹚
rename↪ {t = (ƛ a) · b} (ξ-·₁ (ζ step)) with rename↪ step 
... | ﹙ _ , ﹙ step , refl ﹚ ﹚ = ﹙ _ , ﹙ ξ-·₁ (ζ step) , refl ﹚ ﹚
rename↪ {t = f · a} (ξ-·₁ step) with rename↪ step
... | ﹙ _ , ﹙ step , refl ﹚ ﹚ = ﹙ _ , ﹙ ξ-·₁ step , refl ﹚ ﹚
rename↪ {t = ⟨ a , b ⟩} (ξ-⟨,⟩₁ step) with rename↪ step
... | ﹙ _ , ﹙ step , refl ﹚ ﹚ = ﹙ _ , ﹙ ξ-⟨,⟩₁ step , refl ﹚ ﹚
rename↪ {t = ⟨ a , b ⟩} (ξ-⟨,⟩₂ step) with rename↪ step
... | ﹙ _ , ﹙ step , refl ﹚ ﹚ = ﹙ _ , ﹙ ξ-⟨,⟩₂ step , refl ﹚ ﹚
rename↪ {t = proj _ ⟨ a , b ⟩} β-proj₁ = ﹙ a , ﹙ β-proj₁ , refl ﹚ ﹚
rename↪ {t = proj _ ⟨ a , b ⟩} β-proj₂ = ﹙ b , ﹙ β-proj₂ , refl ﹚ ﹚
rename↪ {t = proj _ t} (ξ-proj step) with rename↪ step
rename↪ {t = proj _ {inj₁ x} t} (ξ-proj _) | ﹙ _ , ﹙ step , refl ﹚ ﹚ = ﹙ _ , ﹙ ξ-proj step , refl ﹚ ﹚
rename↪ {t = proj _ {inj₂ y} t} (ξ-proj _) | ﹙ _ , ﹙ step , refl ﹚ ﹚ = ﹙ _ , ﹙ ξ-proj step , refl ﹚ ﹚
rename↪ {t = [ _ ]≡ t} (ξ-≡ step) with rename↪ step
... | ﹙ _ , ﹙ step , refl ﹚ ﹚ = ﹙ _ , ﹙ ξ-≡ step , refl ﹚ ﹚


SN*-rename : ∀{Γ Δ A} {t : Γ ⊢ A} → (ρ : Rename Γ Δ) → SN* ⟦_⟧ t → SN* ⟦_⟧ (rename ρ t)

⟦⟧-rename : ∀{Γ Δ A} {t : Γ ⊢ A} → (ρ : Rename Γ Δ) → ⟦ t ⟧ → ⟦ rename ρ t ⟧
⟦⟧-rename {t = ` v} ρ tt = tt
⟦⟧-rename {t = a · b} ρ tt = tt
⟦⟧-rename {A = A ⇒ B} {t = ƛ n} ρ Ln {_}{ρ₁}{u}
    rewrite cong (SN* ⟦_⟧) (rename-subst {Σ = ∅} {M = n} {N = u} {ρ = ρ} {σ = (ids ∘ ρ₁)})
  = λ SNu → Ln {_} {ρ₁ ∘ ρ} SNu
⟦⟧-rename {t = ⋆} ρ tt = tt
⟦⟧-rename {t = ⟨ a , b ⟩} ρ ﹙ SN*a , SN*b ﹚ = ﹙ SN*-rename ρ SN*a , SN*-rename ρ SN*b ﹚
⟦⟧-rename {t = proj _ t} ρ tt = tt
⟦⟧-rename {t = [ _ ]≡ t} ρ tt = tt

SN*-rename ρ (sn* Lt SNt) = sn* (⟦⟧-rename ρ Lt) λ { (inj₁ step) → case (rename↪ step) of λ { ﹙ t' , ﹙ t↪t' , refl ﹚ ﹚ → SN*-rename ρ (SNt (inj₁ t↪t')) }
                                                   ; (inj₂ step) → {!   !} }

asd : ∀ {Γ A B} {t : Γ , A ⊢ A ⇒ B} → SN* ⟦_⟧ t → SN* ⟦_⟧ (ƛ t · ` Z)
asd (sn* Lt SNt) = sn* (λ SNu → {! Lt  !}) λ {(inj₁ (ζ (ξ-·₁ x))) → {!   !}
                                            ; (inj₁ (ζ β-ƛ)) → {!   !}
                                            ; (inj₂ eta) → {!   !}
                                            ; (inj₂ (ζ y)) → {!   !}}

⊨exts : ∀{Γ Δ A} {σ : Subst Γ Δ} → Γ ⊨ σ → (Γ , A) ⊨ (exts σ)
⊨exts σ Z = sn* tt (λ {(inj₂ eta) → {!   !}
                     ; (inj₂ split) → {!   !}})
⊨exts σ (S v) = SN*-rename S_ (σ v)

⊨rename : ∀{Γ Δ Δ₁} {σ : Subst Γ Δ} → Γ ⊨ σ → (ρ : Rename Δ Δ₁) → Γ ⊨ (⟪ ids ∘ ρ ⟫ ∘ σ)
⊨rename {σ = σ} Lσ ρ v rewrite cong (SN* ⟦_⟧) (rename-subst-ids {Σ = ∅} {N = σ v} {ρ = ρ}) = SN*-rename ρ (Lσ v)

-------


↪SN* : ∀ {Γ A}{t t' : Γ ⊢ A} → t ↪ t' → SN* ⟦_⟧ t → SN* ⟦_⟧ t'
↪SN* step (sn* _ SNt) = SNt step

lemma-ƛ : ∀ {Γ A B} → {t : Γ , B ⊢ A} → ⟦ ƛ t ⟧ → SN* ⟦_⟧ t → SN* ⟦_⟧ (ƛ t)
lemma-ƛ {t = t} Lƛ (sn* _ SNt) = sn* Lƛ (λ {(ζ step) → lemma-ƛ (λ {u} SNu → ↪SN* (↪[] step) (Lƛ SNu)) (SNt step)})


lemma-· : ∀ {Γ A B} → {a : Γ ⊢ A ⇒ B} {b : Γ ⊢ A} → SN* ⟦_⟧ a → SN* ⟦_⟧ b → SN* ⟦_⟧ (a · b)
lemma-· SN*a SN*b = sn* tt λ step → aux SN*a SN*b step
  where aux : ∀ {Γ A B} {a : Γ ⊢ B ⇒ A} {b : Γ ⊢ B} {t' : Γ ⊢ A} → SN* ⟦_⟧ a → SN* ⟦_⟧ b → a · b ↪ t' → SN* ⟦_⟧ t'
        aux (sn* La SNa) SN*b (ξ-·₁ step) = lemma-· (SNa step) SN*b
        aux SN*a (sn* Lb SNb) (ξ-·₂ step) = lemma-· SN*a (SNb step)
        aux (sn* La SNa) SN*b β-ƛ = La SN*b 


lemma-⟨,⟩ : ∀ {Γ A B} → {a : Γ ⊢ A} {b : Γ ⊢ B} → SN* ⟦_⟧ a → SN* ⟦_⟧ b → SN* ⟦_⟧ (⟨ a , b ⟩)
lemma-⟨,⟩ SN*a SN*b = sn* ﹙ SN*a , SN*b ﹚ λ step → aux SN*a SN*b step
  where aux : ∀ {Γ A B} {a : Γ ⊢ A} {b : Γ ⊢ B} {t' : Γ ⊢ A × B} → SN* ⟦_⟧ a → SN* ⟦_⟧ b → ⟨ a , b ⟩ ↪ t' → SN* ⟦_⟧ t'
        aux (sn* La SNa) SN*b (ξ-⟨,⟩₁ step) = lemma-⟨,⟩ (SNa step) SN*b
        aux SN*a (sn* Lb SNb) (ξ-⟨,⟩₂ step) = lemma-⟨,⟩ SN*a (SNb step)


lemma-proj : ∀ {Γ A B C p} → {t : Γ ⊢ A × B} → SN* ⟦_⟧ t → SN* ⟦_⟧ (proj C {p} t)
lemma-proj SN*t = sn* tt (aux SN*t)
  where aux : ∀ {Γ A B C p t'} → {t : Γ ⊢ A × B} → SN* ⟦_⟧ t → (proj C {p} t) ↪ t' → SN* ⟦_⟧ t'
        aux (sn* Lt SNt) (ξ-proj step) = lemma-proj (SNt step)
        aux (sn* ﹙ SN*t' , _ ﹚ SNt) β-proj₁ = SN*t'
        aux (sn* ﹙ _ , SN*t' ﹚ SNt) β-proj₂ = SN*t'

lemma-≡ : ∀ {Γ A B iso} → {t : Γ ⊢ A} → SN* ⟦_⟧ t → SN* {A = B} ⟦_⟧ ([ iso ]≡ t)
lemma-≡ SN*t = sn* tt (aux SN*t)
  where aux : ∀ {Γ A iso t'} → {t : Γ ⊢ A} → SN* ⟦_⟧ t → ([ iso ]≡ t) ↪ t' → SN* ⟦_⟧ t'
        aux (sn* Lt SNt) (ξ-≡ step) = lemma-≡ (SNt step)

-- ids es una substitución adecuada

⊨ids : ∀{Γ} → Γ ⊨ ids
⊨ids _ = sn* tt (λ ())

-- cons entre una substitución adecuada y un termino SN* es también una substitución adecuada

⊨_•_ : ∀{Γ Δ A} {σ : Subst Δ Γ} {t : Γ ⊢ A} → SN* ⟦_⟧ t → Δ ⊨ σ → (Δ , A) ⊨ (t • σ)
(⊨ t • σ) Z = t
(⊨ t • σ) (S v) = σ v


adequacy : ∀ {Γ Δ A} {σ : Subst Γ Δ} → (t : Γ ⊢ A) → Γ ⊨ σ → SN* ⟦_⟧ (⟪ σ ⟫ t)
adequacy (` v) σ = σ v
adequacy ⋆ σ = sn* tt (λ ())
adequacy ⟨ a , b ⟩ σ = lemma-⟨,⟩ (adequacy a σ) (adequacy b σ)
adequacy (proj _ x) σ = lemma-proj (adequacy x σ)
adequacy (a · b) σ = lemma-· (adequacy a σ) (adequacy b σ)
adequacy ([ iso ]≡ n) σ = lemma-≡ (adequacy n σ)
adequacy {σ = σ} (ƛ n) Lσ =
  lemma-ƛ
    (λ { {ρ = ρ}{u = u} SNu →
      transport (SN* ⟦_⟧)
        (subst-split {Σ = ∅} {N = n})
        (adequacy n (⊨ SNu • (⊨rename Lσ ρ)))}) -- {u • (⟪ ids ∘ ρ ⟫ ∘ σ)}
    (adequacy n (⊨exts Lσ))

SN-substitute : ∀ {Γ Δ A}{σ : Subst Γ Δ}{t : Γ ⊢ A} → SN (subst σ t) → SN t
SN-substitute (sn SNtσ) = sn (λ step → SN-substitute (SNtσ (↪[] step)))

strong-norm : ∀ {Γ A} (t : Γ ⊢ A) → SN t
strong-norm t = SN-substitute (SN*-SN (adequacy t ⊨ids))

-------------------------


test : ∅ ⊢ ⊤
test = (ƛ (proj _ {inj₂ refl} (` Z)) · proj ⊤ {inj₁ refl} (` Z)) · ⟨ ⋆ , ƛ ` Z ⟩