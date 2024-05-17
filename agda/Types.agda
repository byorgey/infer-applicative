open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Binary using (DecidableEquality)
open import Relation.Nullary.Decidable using (yes ; no)

module Types (B : Set) (DecB : DecidableEquality B) where

data Ty : Set where
  base : B → Ty
  _⇒_ : Ty → Ty → Ty
  □_ : Ty → Ty

infix 2 _⇒_
infix 30 □_

base-inj : {b₁ b₂ : B} → base b₁ ≡ base b₂ → b₁ ≡ b₂
base-inj refl = refl

⇒-inj : {τ₁₁ τ₁₂ τ₂₁ τ₂₂ : Ty} → ((τ₁₁ ⇒ τ₁₂) ≡ (τ₂₁ ⇒ τ₂₂)) → (τ₁₁ ≡ τ₂₁) × (τ₁₂ ≡ τ₂₂)
⇒-inj refl = refl , refl

□-inj : {τ₁ τ₂ : Ty} → (□ τ₁ ≡ □ τ₂) → (τ₁ ≡ τ₂)
□-inj refl = refl

------------------------------------------------------------
-- Type equality is decidable
------------------------------------------------------------

≡Ty-Dec : DecidableEquality Ty
≡Ty-Dec (base b₁) (base b₂) with DecB b₁ b₂
... | no b₁≢b₂ = no λ eq → b₁≢b₂ (base-inj eq)
... | yes b₁≡b₂ = yes (cong base b₁≡b₂)
≡Ty-Dec (base _) (_ ⇒ _) = no (λ ())
≡Ty-Dec (base _) (□ _) = no (λ ())
≡Ty-Dec (_ ⇒ _) (base _) = no (λ ())
≡Ty-Dec (σ₁ ⇒ τ₁) (σ₂ ⇒ τ₂) with ≡Ty-Dec σ₁ σ₂ | ≡Ty-Dec τ₁ τ₂
... | no σ₁≢σ₂ | _ = no (λ eq → σ₁≢σ₂ (proj₁ (⇒-inj eq)))
... | yes _ | no τ₁≢τ₂ = no (λ eq → τ₁≢τ₂ (proj₂ (⇒-inj eq)))
... | yes σ₁≡σ₂ | yes τ₁≡τ₂ = yes (cong₂ _⇒_ σ₁≡σ₂ τ₁≡τ₂)
≡Ty-Dec (_ ⇒ _) (□ _) = no (λ ())
≡Ty-Dec (□ _) (base _) = no (λ ())
≡Ty-Dec (□ _) (_ ⇒ _) = no (λ ())
≡Ty-Dec (□ τ₁) (□ τ₂) with ≡Ty-Dec τ₁ τ₂
... | no τ₁≢τ₂ = no (λ eq → τ₁≢τ₂ (□-inj eq))
... | yes τ₁≡τ₂ = yes (cong □_ τ₁≡τ₂)

------------------------------------------------------------
-- Box erasure
------------------------------------------------------------

⌊_⌋ : Ty → Ty
⌊ base b ⌋ = base b
⌊ σ ⇒ τ ⌋ = ⌊ σ ⌋ ⇒ ⌊ τ ⌋
⌊ □ τ ⌋ = ⌊ τ ⌋
