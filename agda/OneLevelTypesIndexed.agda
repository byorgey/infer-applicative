open import Data.Product using (Σ ; _×_ ; _,_ ; -,_ ; proj₁ ; proj₂)
open import Data.Product.Properties using (≡-dec)
open import Function using (_∘_)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Relation.Nullary.Decidable using (yes; no; Dec)

module OneLevelTypesIndexed (B : Set) (≟B : DecidableEquality B) where

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
-- Types
------------------------------------------------------------

ΣTy : Set
data Ty : Boxity → Set

ΣTy = Σ Boxity Ty

data Ty where
  □_ : Ty [0] → Ty [1]
  base : B → Ty [0]
  _⇒_ : ΣTy → ΣTy → Ty [0]

infixr 2 _⇒_
infix 30 □_

_⇒′_ : {b₁ b₂ : Boxity} → Ty b₁ → Ty b₂ → Ty [0]
_⇒′_ {b₁} {b₂} σ τ = (b₁ , σ) ⇒ (b₂ , τ)

□-inj : {τ₁ τ₂ : Ty [0]} → (□ τ₁ ≡ □ τ₂) → (τ₁ ≡ τ₂)
□-inj refl = refl

base-inj : {b₁ b₂ : B} → base b₁ ≡ base b₂ → b₁ ≡ b₂
base-inj refl = refl

⇒-inj : {σ₁ σ₂ τ₁ τ₂ : ΣTy} → (σ₁ ⇒ σ₂) ≡ (τ₁ ⇒ τ₂) → (σ₁ ≡ τ₁) × (σ₂ ≡ τ₂)
⇒-inj refl = refl , refl

------------------------------------------------------------
-- Type equality is decidable
------------------------------------------------------------

ΣTy-≟ : DecidableEquality ΣTy
{-# TERMINATING #-}
Ty-≟ : ∀ {a} → DecidableEquality (Ty a)

ΣTy-≟ = ≡-dec Boxity-≟ Ty-≟

Ty-≟ (□ σ) (□ τ) with Ty-≟ σ τ
... | yes refl = yes refl
... | no σ≢τ = no (σ≢τ ∘ □-inj)
Ty-≟ (base x) (base y) with ≟B x y
... | no x≢y = no (x≢y ∘ base-inj)
... | yes refl = yes refl
Ty-≟ (σ₁ ⇒ σ₂) (τ₁ ⇒ τ₂) with ΣTy-≟ σ₁ τ₁ | ΣTy-≟ σ₂ τ₂
... | no σ₁≢τ₁ | _ = no (σ₁≢τ₁ ∘ proj₁ ∘ ⇒-inj)
... | yes _ | no σ₂≢τ₂ = no (σ₂≢τ₂ ∘ proj₂ ∘ ⇒-inj)
... | yes refl | yes refl = yes refl
Ty-≟ (base _) (_ ⇒ _) = no λ ()
Ty-≟ (_ ⇒ _) (base _) = no λ ()

------------------------------------------------------------
-- Subtyping on one level indexed types
------------------------------------------------------------

data _<:_ : Ty b₁ → Ty b₂ → Set where
  rfl : {τ : Ty b} → τ <: τ
  tr : {σ : Ty b₁} {τ : Ty b₂} {υ : Ty b₃} → σ <: τ → τ <: υ → σ <: υ
  arr : {τ₁ : Ty b₁} {τ₂ : Ty b₂} {σ₁ : Ty b₃} {σ₂ : Ty b₄} → (τ₁ <: σ₁) → (σ₂ <: τ₂) → (σ₁ ⇒′ σ₂) <: (τ₁ ⇒′ τ₂)
  box : {σ τ : Ty [0]} → (σ <: τ) → (□ σ <: □ τ)
  pure : {τ : Ty [0]} → τ <: □ τ
  ap : {σ τ : Ty [0]} → □ (σ ⇒′ τ) <: (□ σ ⇒′ □ τ)

