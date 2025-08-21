open import Data.Bool
open import Data.Product using (Σ ; _×_ ; _,_ ; -,_ ; proj₁ ; proj₂ )
open import Data.Product.Properties using (≡-dec)
open import Function using (_∘_)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable using (yes; no; Dec)
open import Relation.Nullary.Negation.Core

module OneLevelTypesIndexed2 (B : Set) (≟B : DecidableEquality B) where

------------------------------------------------------------
-- Boxity
------------------------------------------------------------

data Boxity : Set where
  [0] : Boxity
  [1] : Boxity

variable b b₁ b₂ b₃ b₄ : Boxity

Boxity-≟ : DecidableEquality Boxity
Boxity-≟ [0] [0] = yes refl
Boxity-≟ [0] [1] = no λ ()
Boxity-≟ [1] [0] = no λ ()
Boxity-≟ [1] [1] = yes refl

------------------------------------------------------------
-- Path-dependent equality
------------------------------------------------------------

-- Based on https://martinescardo.github.io/dependent-equality-lecture/DependentEquality.html

_≡⟦_⟧_ : {A : Set} {B : A → Set} {a₀ a₁ : A}
       → B a₀ → a₀ ≡ a₁ → B a₁ → Set
b₀ ≡⟦ refl ⟧ b₁   =   b₀ ≡ b₁

undep : {A : Set} {B : A → Set} {a : A} {x y : B a} → _≡⟦_⟧_ {A} {B} x _ y → x ≡ y
undep p = p

------------------------------------------------------------
-- Types
------------------------------------------------------------

data Ty : Boxity → Set where
  □_ : Ty [0] → Ty [1]
  base : B → Ty [0]
  _⇒_ : {b₁ b₂ : Boxity} → Ty b₁ → Ty b₂ → Ty [0]

infixr 2 _⇒_
infix 30 □_

□-inj : {τ₁ τ₂ : Ty [0]} → (□ τ₁ ≡ □ τ₂) → (τ₁ ≡ τ₂)
□-inj refl = refl

base-inj : {b₁ b₂ : B} → base b₁ ≡ base b₂ → b₁ ≡ b₂
base-inj refl = refl

⇒-inj : {σ₁ : Ty b₁} {σ₂ : Ty b₂} {τ₁ : Ty b₁} {τ₂ : Ty b₂} → (σ₁ ⇒ σ₂) ≡ (τ₁ ⇒ τ₂) → (σ₁ ≡ τ₁) × (σ₂ ≡ τ₂)
⇒-inj refl = refl , refl

------------------------------------------------------------
-- Type equality is decidable
------------------------------------------------------------

-- Boxity-heterogeneous decision principle, which decides equality of
-- boxities and types at the same time using a path-dependent equality
Ty-≟′ : (σ : Ty b₁) → (τ : Ty b₂) → Dec (Σ (b₁ ≡ b₂) λ p → _≡⟦_⟧_ {_} {Ty} σ p τ)
Ty-≟′ (□ σ) (□ τ) with Ty-≟′ σ τ
... | yes (refl , refl) = yes (refl , refl)
... | no σ≢τ = no λ { (refl , refl) → σ≢τ (refl , refl) }
Ty-≟′ (base S) (base T) with ≟B S T
... | yes refl = yes (refl , refl)
... | no S≢T = no λ { (refl , refl) → S≢T refl }
Ty-≟′ (_⇒_ {b₁} {b₂} σ₁ σ₂) (_⇒_ {b₃} {b₄} τ₁ τ₂) with Boxity-≟ b₁ b₃ | Boxity-≟ b₂ b₄ | Ty-≟′ σ₁ τ₁ | Ty-≟′ σ₂ τ₂
... | no b₁≢b₃ | _ | _ | _ = no λ { (refl , refl) → b₁≢b₃ refl }
... | yes _ | no b₂≢b₄ | _ | _ = no λ { (refl , refl) → b₂≢b₄ refl }
... | yes _ | yes _ | no σ₁≢τ₁ | _ = no λ { (refl , refl) → σ₁≢τ₁ (refl , refl) }
... | yes _ | yes _ | yes _ | no σ₂≢τ₂ = no λ { (refl , refl) → σ₂≢τ₂ (refl , refl) }
... | yes _ | yes _ | yes (refl , refl) | yes (refl , refl) = yes (refl , refl)
Ty-≟′ (□ _) (base _) = no λ ()
Ty-≟′ (□ _) (_ ⇒ _) = no λ ()
Ty-≟′ (base _) (□ _) = no λ ()
Ty-≟′ (base _) (_ ⇒ _) = no λ { (refl , ()) }
Ty-≟′ (_ ⇒ _) (□ _) = no λ ()
Ty-≟′ (_ ⇒ _) (base _) = no λ { (refl , ()) }

-- Boxity-homogeneous decision principle
Ty-≟ : DecidableEquality (Ty b)
Ty-≟ {b} σ τ with Ty-≟′ σ τ
... | no σ≢τ = no (λ σ≡τ → σ≢τ ( refl , σ≡τ))
... | yes (refl , σ≡τ) = yes σ≡τ

ΣTy-≟ : DecidableEquality (Σ Boxity Ty)
ΣTy-≟ (b₁ , σ) (b₂ , τ) with Ty-≟′ σ τ
... | no σ≢τ = no λ { refl → σ≢τ (refl , refl) }
... | yes (refl , refl) = yes refl

------------------------------------------------------------
-- Box erasure
------------------------------------------------------------

⌊_⌋ : Ty b → Ty [0]
⌊ □ τ ⌋ = ⌊ τ ⌋
⌊ base x ⌋ = base x
⌊ σ ⇒ τ ⌋ = ⌊ σ ⌋ ⇒ ⌊ τ ⌋

------------------------------------------------------------
-- Subtyping on one level indexed types
------------------------------------------------------------

data _<:_ : Ty b₁ → Ty b₂ → Set where
  rfl : ∀ {τ : Ty b} → τ <: τ
  tr : {σ : Ty b₁} {τ : Ty b₂} {υ : Ty b₃} → σ <: τ → τ <: υ → σ <: υ
  arr : {τ₁ : Ty b₁} {τ₂ : Ty b₂} {σ₁ : Ty b₃} {σ₂ : Ty b₄} → (τ₁ <: σ₁) → (σ₂ <: τ₂) → (σ₁ ⇒ σ₂) <: (τ₁ ⇒ τ₂)
  box : ∀ {σ τ} → (σ <: τ) → (□ σ <: □ τ)
  pure : ∀ {τ} → τ <: □ τ
  ap : ∀ {σ τ} → □ (σ ⇒ τ) <: (□ σ ⇒ □ τ)

infix 1 _<:_

--------------------------------------------------
-- Subtypes have the same shape

<:→⌊⌋ : {σ : Ty b₁} {τ : Ty b₂} → σ <: τ → ⌊ σ ⌋ ≡ ⌊ τ ⌋
<:→⌊⌋ rfl = refl
<:→⌊⌋ (tr σ<:τ τ<:υ) = trans (<:→⌊⌋ σ<:τ) (<:→⌊⌋ τ<:υ)
<:→⌊⌋ (arr τ₁<:σ₁ σ₂<:τ₂) = cong₂ _⇒_ (sym (<:→⌊⌋ τ₁<:σ₁)) (<:→⌊⌋ σ₂<:τ₂)
<:→⌊⌋ (box σ<:τ) = <:→⌊⌋ σ<:τ
<:→⌊⌋ pure = refl
<:→⌊⌋ ap = refl
