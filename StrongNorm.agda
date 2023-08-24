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
rename↪ {t = π _ ⟨ a , b ⟩} β-π₁ = ﹙ a , ﹙ β-π₁ , refl ﹚ ﹚
rename↪ {t = π _ ⟨ a , b ⟩} β-π₂ = ﹙ b , ﹙ β-π₂ , refl ﹚ ﹚
rename↪ {t = π _ t} (ξ-π step) with rename↪ step
rename↪ {t = π _ {inj₁ x} t} (ξ-π _) | ﹙ _ , ﹙ step , refl ﹚ ﹚ = ﹙ _ , ﹙ ξ-π step , refl ﹚ ﹚
rename↪ {t = π _ {inj₂ y} t} (ξ-π _) | ﹙ _ , ﹙ step , refl ﹚ ﹚ = ﹙ _ , ﹙ ξ-π step , refl ﹚ ﹚
rename↪ {t = [ _ ]≡ t} (ξ-≡ step) with rename↪ step
... | ﹙ _ , ﹙ step , refl ﹚ ﹚ = ﹙ _ , ﹙ ξ-≡ step , refl ﹚ ﹚


SN*-rename : ∀{Γ Δ A} {t : Γ ⊢ A} → (ρ : Rename Γ Δ) → SN* ⟦_⟧ t → SN* ⟦_⟧ (rename ρ t)

⟦⟧-rename : ∀{Γ Δ A} {t : Γ ⊢ A} → (ρ : Rename Γ Δ) → ⟦ t ⟧ → ⟦ rename ρ t ⟧
⟦⟧-rename {A = A ⇒ B} {t = ƛ n} ρ Ln {_}{ρ₁}{u}
  rewrite rename-subst {Σ = ∅} {M = n} {N = u} {ρ = ρ} {σ = (ids ∘ ρ₁)}
    = λ SNu → Ln {_} {ρ₁ ∘ ρ} SNu
⟦⟧-rename {t = ⟨ a , b ⟩} ρ ﹙ SN*a , SN*b ﹚ = ﹙ SN*-rename ρ SN*a , SN*-rename ρ SN*b ﹚
⟦⟧-rename {t = ` v} ρ tt      = tt
⟦⟧-rename {t = a · b} ρ tt    = tt
⟦⟧-rename {t = ⋆} ρ tt        = tt
⟦⟧-rename {t = π _ t} ρ tt    = tt
⟦⟧-rename {t = [ _ ]≡ t} ρ tt = tt

SN*-rename ρ (sn* Lt SNt) =
  sn* (⟦⟧-rename ρ Lt) λ { (inj₁ step) → case (rename↪ step) of λ { ﹙ _ , ﹙ t↪t' , refl ﹚ ﹚ → SN*-rename ρ (SNt (inj₁ t↪t')) }
                         ; (inj₂ step) → case (rename⇄ step) of λ { ﹙ _ , ﹙ t⇄t' , refl ﹚ ﹚ → SN*-rename ρ (SNt (inj₂ t⇄t')) } }


⊨exts : ∀{Γ Δ A} {σ : Subst Γ Δ} → Γ ⊨ σ → (Γ , A) ⊨ (exts σ)
⊨exts σ Z = sn* tt (λ {(inj₁ ()) ; (inj₂ ())})
⊨exts σ (S v) = SN*-rename S_ (σ v)

⊨rename : ∀{Γ Δ Δ₁} {σ : Subst Γ Δ} → Γ ⊨ σ → (ρ : Rename Δ Δ₁) → Γ ⊨ (⟪ ids ∘ ρ ⟫ ∘ σ)
⊨rename {σ = σ} Lσ ρ v rewrite cong (SN* ⟦_⟧) (rename-subst-ids {Σ = ∅} {N = σ v} {ρ = ρ}) = SN*-rename ρ (Lσ v)

-------

↪SN* : ∀ {Γ A}{t t' : Γ ⊢ A} → t ↪ t' → SN* ⟦_⟧ t → SN* ⟦_⟧ t'
↪SN* step (sn* _ SNt) = SNt (inj₁ step)
⇄SN* : ∀ {Γ A}{t t' : Γ ⊢ A} → t ⇄ t' → SN* ⟦_⟧ t → SN* ⟦_⟧ t'
⇄SN* step (sn* _ SNt) = SNt (inj₂ step)

lemma-ƛ : ∀ {Γ A B} → {t : Γ , B ⊢ A} → ⟦ ƛ t ⟧ → SN* ⟦_⟧ t → SN* ⟦_⟧ (ƛ t)
lemma-ƛ {t = t} Lƛ (sn* _ SNt) =
  sn* Lƛ (λ { (inj₁ (ζ step)) → lemma-ƛ (λ SNu → ↪SN* (↪[] step) (Lƛ SNu)) (SNt (inj₁ step)) -- SN* ⟦_⟧ (⟪ σ ⟫ t) → ⟪ σ ⟫ t ↪ ⟪ σ ⟫ t' → SN* ⟦_⟧ (⟪ σ ⟫ t')
            ; (inj₂ (ζ step)) → lemma-ƛ (λ SNu → ⇄SN* (⇄[] step) (Lƛ SNu)) (SNt (inj₂ step)) })


lemma-⟨,⟩ : ∀ {Γ A B} → {a : Γ ⊢ A} {b : Γ ⊢ B} → SN* ⟦_⟧ a → SN* ⟦_⟧ b → SN* ⟦_⟧ (⟨ a , b ⟩)
lemma-⟨,⟩ SN*a SN*b = sn* ﹙ SN*a , SN*b ﹚ λ step → aux SN*a SN*b step
  where aux : ∀ {Γ A B} {a : Γ ⊢ A} {b : Γ ⊢ B} {t' : Γ ⊢ A × B} → SN* ⟦_⟧ a → SN* ⟦_⟧ b → ⟨ a , b ⟩ ↪ t' ⊎ ⟨ a , b ⟩ ⇄ t' → SN* ⟦_⟧ t'
        aux (sn* La SNa) SN*b (inj₁ (ξ-⟨,⟩₁ step)) = lemma-⟨,⟩ (SNa (inj₁ step)) SN*b
        aux SN*a (sn* Lb SNb) (inj₁ (ξ-⟨,⟩₂ step)) = lemma-⟨,⟩ SN*a (SNb (inj₁ step))
        aux (sn* La SNa) SN*b (inj₂ (ξ-⟨,⟩₁ step)) = lemma-⟨,⟩ (SNa (inj₂ step)) SN*b
        aux SN*a (sn* Lb SNb) (inj₂ (ξ-⟨,⟩₂ step)) = lemma-⟨,⟩ SN*a (SNb (inj₂ step))


lemma-π : ∀ {Γ A B C p} → {t : Γ ⊢ A × B} → SN* ⟦_⟧ t → SN* ⟦_⟧ (π C {p} t)
lemma-π SN*t = sn* tt (aux SN*t)
  where aux : ∀ {Γ A B C p t'} → {t : Γ ⊢ A × B} → SN* ⟦_⟧ t → (π C {p} t) ↪ t' ⊎ π C {p} t ⇄ t' → SN* ⟦_⟧ t'
        aux (sn* Lt SNt)             (inj₁ (ξ-π step)) = lemma-π (SNt (inj₁ step))
        aux (sn* ﹙ SN*t' , _ ﹚ SNt) (inj₁ β-π₁)       = SN*t'
        aux (sn* ﹙ _ , SN*t' ﹚ SNt) (inj₁ β-π₂)       = SN*t'
        aux (sn* Lt SNt)             (inj₂ (ξ-π step)) = lemma-π (SNt (inj₂ step))

open import IsoType using (dist; curry)

lemma-· : ∀ {Γ A B} → {a : Γ ⊢ A ⇒ B} {b : Γ ⊢ A} → SN* ⟦_⟧ a → SN* ⟦_⟧ b → SN* ⟦_⟧ (a · b)
lemma-· SN*a SN*b = sn* tt λ step → aux SN*a SN*b step
  where aux : ∀ {Γ A B} {a : Γ ⊢ B ⇒ A} {b : Γ ⊢ B} {t' : Γ ⊢ A} → SN* ⟦_⟧ a → SN* ⟦_⟧ b → a · b ↪ t' ⊎ a · b ⇄ t' → SN* ⟦_⟧ t'
        aux (sn* La SNa) SN*b (inj₁ (ξ-·₁ step)) = lemma-· (SNa (inj₁ step)) SN*b
        aux SN*a (sn* Lb SNb) (inj₁ (ξ-·₂ step)) = lemma-· SN*a (SNb (inj₁ step))
        aux (sn* La SNa) SN*b (inj₁ β-ƛ)         = La SN*b 
        aux (sn* La SNa) SN*b (inj₂ (ξ-·₁ step)) = lemma-· (SNa (inj₂ step)) SN*b
        aux SN*a (sn* Lb SNb) (inj₂ (ξ-·₂ step)) = lemma-· SN*a (SNb (inj₂ step))

lemma-var :  ∀ {Γ A}{v : Γ ∋ A} → SN* {Γ}{A} ⟦_⟧ (` v)
lemma-var = sn* tt (λ {(inj₁ ()) ; (inj₂ ())})

lemma-top :  ∀ {Γ} → SN* {Γ} ⟦_⟧ ⋆
lemma-top = sn* tt (λ {(inj₁ ()) ; (inj₂ ())})

open import Subs using (
  Z-weaken; subst-cong⇒₁-split; subst-weaken; rename-subst-ids;
  subst-uncurry-split; subst-curry-split; subst-shift-curry-split)

lemma-sub : ∀ {Γ A B} → {t : Γ , B ⊢ A} → SN* ⟦_⟧ (ƛ t) → SN* ⟦_⟧ t
lemma-sub {t = t} (sn* Lt SNt) =
  transport (SN* ⟦_⟧) -- SN* ⟦_⟧ ⟪ ` Z • ids ∘ S_ ⟫ t ≡ SN* ⟦_⟧ t
    (Z-weaken {Σ = ∅} {N = t})
    (Lt {ρ = S_} {u = ` Z} lemma-var)

lemma-S : ∀ {Γ Δ A B} → {t : Γ ⊢ A} {u : Δ ⊢ B} → SN* ⟦_⟧ t → (ρ : Rename Γ Δ) → SN* ⟦_⟧ (⟪ u • (λ x → ids (ρ x)) ⟫ (rename S_ t))
lemma-S {t = t} SNt ρ =
  transport (SN* ⟦_⟧) -- SN* ⟦_⟧ ⟪ u • ids ∘ ρ ⟫ (rename S_ t) ≡ SN* ⟦_⟧ (rename ρ t)
    (trans (sym (rename-subst-ids {Σ = ∅})) (sym (subst-weaken {Σ = ∅} {N = t})))
    (SN*-rename ρ SNt)

lemma-curry : ∀ {Γ Δ A B C} → {t : Γ , A , B ⊢ C} {u : Δ ⊢ A × B} → ⟦ ƛ ƛ t ⟧ → SN* ⟦_⟧ u → (ρ : Rename Γ Δ) → SN* ⟦_⟧ (⟪ u • (λ x → ids (ρ x)) ⟫ (⟪ σ-curry ⟫ t))
lemma-curry {A = A} {B = B} {t = t} {u = u} Lt SNu ρ =
  case Lt {ρ = ρ} {u = π A {inj₁ refl} u} (lemma-π SNu) of λ {(sn* Lr _) →
    transport (SN* ⟦_⟧)
      (subst-curry-split {Σ = ∅} {N = t})
      (Lr {ρ = λ x → x} {u = π B {inj₂ refl} u} (lemma-π SNu))}

lemma-uncurry : ∀ {Γ Δ A B C} → {t : Γ , A × B ⊢ C} {u : Δ ⊢ A} → ⟦ ƛ t ⟧ → SN* ⟦_⟧ u → (ρ : Rename Γ Δ) → SN* ⟦_⟧ (⟪ u • (λ x → ids (ρ x)) ⟫ (ƛ ⟪ σ-uncurry ⟫ t))
lemma-uncurry {A = A} {B = B} {t = t} {u = u} Lt SNu ρ =
  lemma-ƛ
    (λ {_}{ρ₁}{u₁} SNu₁ → aux {t = t} Lt SNu SNu₁ ρ ρ₁)
    (transport (SN* ⟦_⟧) (Z-weaken {Σ = ∅}) (aux {t = t} Lt SNu (lemma-var {v = Z}) ρ S_))
  where aux : ∀ {Γ Δ Δ₁ A B C} → {t : Γ , A × B ⊢ C}{u₁ : Δ ⊢ A}{u₂ : Δ₁ ⊢ B} → ⟦ ƛ t ⟧ → SN* ⟦_⟧ u₁ → SN* ⟦_⟧ u₂ → (ρ₁ : Rename Γ Δ) → (ρ₂ : Rename Δ Δ₁) → SN* ⟦_⟧ (⟪ u₂ • ids ∘ ρ₂ ⟫ (⟪ exts (u₁ • ids ∘ ρ₁) ⟫ (⟪ σ-uncurry ⟫ t)))
        aux {t = t} Lt SNu₁ SNu₂ ρ₁ ρ₂ =
          transport (SN* ⟦_⟧)
            (sym (subst-uncurry-split {Σ = ∅} {N = t}))
            (Lt (lemma-⟨,⟩ (SN*-rename ρ₂ SNu₁) SNu₂))

lemma-≡ : ∀ {Γ A B iso} → {t : Γ ⊢ A} → SN* ⟦_⟧ t → SN* {A = B} ⟦_⟧ ([ iso ]≡ t)
lemma-≡ SN*t = sn* tt (aux SN*t)
  where aux : ∀ {Γ A iso t'} → {t : Γ ⊢ A} → SN* ⟦_⟧ t → ([ iso ]≡ t) ↪ t' ⊎ ([ iso ]≡ t) ⇄ t' → SN* ⟦_⟧ t'
        aux (sn* _ SNt) (inj₁ (ξ-≡ step)) = lemma-≡ (SNt (inj₁ step))
        aux (sn* _ SNt) (inj₂ (ξ-≡ step)) = lemma-≡ (SNt (inj₂ step))
        ---
        aux (sn* ﹙ SNr , SNs ﹚ _) (inj₂ comm)     = lemma-⟨,⟩ SNs SNr
        aux (sn* ﹙ SNr , SNs ﹚ _) (inj₂ sym-comm) = lemma-⟨,⟩ SNs SNr
        ---
        aux (sn* ﹙ SNr , sn* ﹙ SNs , SNt ﹚ _ ﹚ _) (inj₂ asso)     = lemma-⟨,⟩ (lemma-⟨,⟩ SNr SNs) SNt
        aux (sn* ﹙ sn* ﹙ SNr , SNs ﹚ _ , SNt ﹚ _) (inj₂ sym-asso) = lemma-⟨,⟩ SNr (lemma-⟨,⟩ SNs SNt)
        aux (sn* ﹙ SNr , SNs ﹚ _) (inj₂ asso-split)     = lemma-⟨,⟩ (lemma-⟨,⟩ SNr (lemma-π SNs)) (lemma-π SNs)
        aux (sn* ﹙ SNr , SNs ﹚ _) (inj₂ sym-asso-split) = lemma-⟨,⟩ (lemma-π SNr) (lemma-⟨,⟩ (lemma-π SNr) SNs)
        ---
        aux (sn* ﹙ (sn* Lr SNr) , (sn* Ls SNs) ﹚ _) (inj₂ dist-ƛ) =
          lemma-ƛ
            (λ SNu → lemma-⟨,⟩ (Lr SNu) (Ls SNu))
            (lemma-⟨,⟩ (lemma-sub (sn* Lr SNr)) (lemma-sub (sn* Ls SNs)))
        aux (sn* ﹙ SNr , SNs ﹚ _) (inj₂ dist-ƛηₗᵣ) =
          lemma-ƛ
            (λ { {ρ = ρ} SNu → lemma-⟨,⟩ (lemma-· (lemma-S SNr ρ) SNu) (lemma-· (lemma-S SNs ρ) SNu)})
            (lemma-⟨,⟩ (lemma-· (SN*-rename S_ SNr) lemma-var) (lemma-· (SN*-rename S_ SNs) lemma-var))
        aux (sn* ﹙ (sn* Lr SNr) , SNs ﹚ _) (inj₂ dist-ƛηᵣ) =
          lemma-ƛ
            (λ { {ρ = ρ} SNu → lemma-⟨,⟩ (Lr SNu) (lemma-· (lemma-S SNs ρ) SNu)})
            (lemma-⟨,⟩ (lemma-sub (sn* Lr SNr)) (lemma-· (SN*-rename S_ SNs) lemma-var))
        aux (sn* ﹙ SNr , (sn* Ls SNs) ﹚ _) (inj₂ dist-ƛηₗ) =
          lemma-ƛ
            (λ { {ρ = ρ} SNu → lemma-⟨,⟩ (lemma-· (lemma-S SNr ρ) SNu) (Ls SNu)})
            (lemma-⟨,⟩ (lemma-· (SN*-rename S_ SNr) lemma-var) (lemma-sub (sn* Ls SNs)))
        aux (sn* Lt SNt) (inj₂ sym-dist-ƛ) = case lemma-sub (sn* Lt SNt) of λ {(sn* ﹙ SNr , SNs ﹚ _)
          → lemma-⟨,⟩
              (lemma-ƛ (λ SNu → case Lt SNu of λ {(sn* ﹙ SNr , _ ﹚ _) → SNr}) SNr)
              (lemma-ƛ (λ SNu → case Lt SNu of λ {(sn* ﹙ _ , SNs ﹚ _) → SNs}) SNs)}
        aux (sn* Lt SNt) (inj₂ sym-dist-ƛ-split) =
          lemma-⟨,⟩
            (lemma-ƛ (λ SNu → lemma-π (Lt SNu)) (lemma-π (lemma-sub (sn* Lt SNt))))
            (lemma-ƛ (λ SNu → lemma-π (Lt SNu)) (lemma-π (lemma-sub (sn* Lt SNt))))
        ---
        aux (sn* Lt _) (inj₂ (curry {A = A}{B = B}{r = r})) =
          lemma-ƛ
            -- SN* ⟦_⟧ (⟪ u • ids ∘ ρ ⟫ (⟪ σ-curry r ⟫)
            (λ {_}{ρ}{u} SNu → lemma-curry {t = r} Lt SNu ρ)
            -- SN* ⟦_⟧ (⟪ ` Z • ids ∘ S_ ⟫ (⟪ σ-curry r ⟫))
            (transport (SN* ⟦_⟧) (Z-weaken {Σ = ∅} {N = ⟪ σ-curry ⟫ r}) (lemma-curry {t = r} {u = ` Z} Lt lemma-var S_))
        aux (sn* Lt _) (inj₂ (curry-η {A = A}{B = B}{r = r})) =
          lemma-ƛ
            (λ {_}{ρ}{u} SNu →
              -- SN* ⟦_⟧ (⟪ u • ids ∘ ρ ⟫ (⟪ σ-curry (rename S_ r) ⟫) · π B u)
              lemma-·
                (transport (SN* ⟦_⟧) (subst-shift-curry-split {N = r}) (Lt {ρ = ρ} {u = π A {inj₁ refl} u} (lemma-π SNu)))
                (lemma-π SNu))
            -- SN* ⟦_⟧ (⟪ σ-curry (rename S_ r) ⟫ · π B (` Z))
            (lemma-·
              (transport (SN* ⟦_⟧) (sym (subst-weaken {Σ = ∅} {N = r})) (Lt {ρ = S_} {u = π A (` Z)} (lemma-π lemma-var)))
              (lemma-π lemma-var))
        aux (sn* Lt _) (inj₂ (uncurry {r = r})) =
          lemma-ƛ
            -- SN* ⟦_⟧ (⟪ u • ids ∘ ρ ⟫ (ƛ ⟪ σ-uncurry r ⟫))
            (λ {_}{ρ}{u} SNu → lemma-uncurry {t = r} Lt SNu ρ)
            -- SN* ⟦_⟧ (ƛ ⟪ σ-uncurry r ⟫)
            (transport (SN* ⟦_⟧) (Z-weaken {Σ = ∅}) (lemma-uncurry {t = r} {u = ` Z} Lt lemma-var S_))
        ---
        aux (sn* ﹙ SN*r , _ ﹚ _) (inj₂ id-×)     = SN*r
        aux SNt                  (inj₂ sym-id-×) = lemma-⟨,⟩ SNt lemma-top
        ---
        aux SNt (inj₂ id-⇒)     = lemma-· SNt lemma-top
        aux SNt (inj₂ sym-id-⇒) =
          lemma-ƛ
            (λ { {_}{ρ} _ → lemma-S SNt ρ })
            (SN*-rename S_ SNt)
        ---
        aux SNt (inj₂ abs)     = lemma-top
        aux SNt (inj₂ sym-abs) =
          lemma-ƛ
            (λ { {ρ = ρ} _ → lemma-S SNt ρ })
            (SN*-rename S_ SNt)
        ---
        aux SNt (inj₂ sym-sym) = lemma-≡ SNt
        ---
        aux (sn* Lt _) (inj₂ (cong⇒₁ {r = r}{iso = iso})) =
          lemma-ƛ
            (λ { {ρ = ρ} {u = u} SNu →
              transport (SN* ⟦_⟧)
                (sym (subst-cong⇒₁-split {Σ = ∅} {N = r}))
                (Lt {ρ = ρ} {u = [ IsoType.sym iso ]≡ (u)} (lemma-≡ SNu)) })
            (Lt {ρ = S_} {u = [ IsoType.sym iso ]≡ (` Z)} (lemma-≡ lemma-var))
        aux (sn* Lt _) (inj₂ (sym-cong⇒₁ {r = r}{iso = iso})) =
          lemma-ƛ
            (λ { {ρ = ρ} {u = u} SNu →
              transport (SN* ⟦_⟧)
                (sym (subst-cong⇒₁-split {Σ = ∅} {N = r}))
                (Lt {ρ = ρ} {u = [ iso ]≡ (u)} (lemma-≡ SNu)) })
            (Lt {ρ = S_} {u = [ iso ]≡ (` Z)} (lemma-≡ lemma-var))
        ---
        aux (sn* Lt SNt) (inj₂ cong⇒₂)     = lemma-ƛ (λ x → lemma-≡ (Lt x)) (lemma-≡ (lemma-sub (sn* Lt SNt)))
        aux (sn* Lt SNt) (inj₂ sym-cong⇒₂) = lemma-ƛ (λ x → lemma-≡ (Lt x)) (lemma-≡ (lemma-sub (sn* Lt SNt)))
        ---
        aux (sn* ﹙ SN*r , SN*s ﹚ _) (inj₂ cong×₁)     = lemma-⟨,⟩ (lemma-≡ SN*r) SN*s
        aux (sn* ﹙ SN*r , SN*s ﹚ _) (inj₂ sym-cong×₁) = lemma-⟨,⟩ (lemma-≡ SN*r) SN*s
        ---
        aux (sn* ﹙ SN*r , SN*s ﹚ _) (inj₂ cong×₂)     = lemma-⟨,⟩ SN*r (lemma-≡ SN*s)
        aux (sn* ﹙ SN*r , SN*s ﹚ _) (inj₂ sym-cong×₂) = lemma-⟨,⟩ SN*r (lemma-≡ SN*s)

-- ids es una substitución adecuada

⊨ids : ∀{Γ} → Γ ⊨ ids
⊨ids _ = lemma-var

-- cons entre una substitución adecuada y un termino SN* es también una substitución adecuada

⊨_•_ : ∀{Γ Δ A} {σ : Subst Δ Γ} {t : Γ ⊢ A} → SN* ⟦_⟧ t → Δ ⊨ σ → (Δ , A) ⊨ (t • σ)
(⊨ t • σ)  Z    = t
(⊨ t • σ) (S v) = σ v


adequacy : ∀ {Γ Δ A} {σ : Subst Γ Δ} → (t : Γ ⊢ A) → Γ ⊨ σ → SN* ⟦_⟧ (⟪ σ ⟫ t)
adequacy (` v) Lσ         = Lσ v
adequacy ⋆ Lσ             = lemma-top
adequacy ⟨ a , b ⟩ Lσ     = lemma-⟨,⟩ (adequacy a Lσ) (adequacy b Lσ)
adequacy (π _ x) Lσ       = lemma-π (adequacy x Lσ)
adequacy (a · b) Lσ       = lemma-· (adequacy a Lσ) (adequacy b Lσ)
adequacy ([ iso ]≡ n) Lσ  = lemma-≡ (adequacy n Lσ)
adequacy {σ = σ} (ƛ n) Lσ =
  lemma-ƛ
    (λ { {ρ = ρ}{u = u} SNu →
      transport (SN* ⟦_⟧)
        (subst-split {Σ = ∅} {N = n})
        (adequacy n (⊨ SNu • (⊨rename Lσ ρ)))}) -- {u • (⟪ ids ∘ ρ ⟫ ∘ σ)}
    (adequacy n (⊨exts Lσ))

SN-substitute : ∀ {Γ Δ A}{σ : Subst Γ Δ}{t : Γ ⊢ A} → SN (subst σ t) → SN t
SN-substitute (sn SNtσ) = sn (λ {(inj₁ step) → SN-substitute (SNtσ (inj₁ (↪[] step)))
                               ; (inj₂ step) → SN-substitute (SNtσ (inj₂ (⇄[] step)))})

strong-norm : ∀ {Γ A} (t : Γ ⊢ A) → SN t
strong-norm t = SN-substitute (SN*-SN (adequacy t ⊨ids))
