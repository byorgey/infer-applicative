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
