open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Binary using (DecidableEquality)
open import Relation.Nullary.Decidable using (yes ; no)
open import Data.Integer
open import Data.Integer.Properties
open ≤-Reasoning
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver
open import Data.Nat using (zero)

module Types (B : Set) (DecB : DecidableEquality B) where

data Ty : Set where
  base : B → Ty
  _⇒_ : Ty → Ty → Ty
  □_ : Ty → Ty

infixr 2 _⇒_
infix 30 □_

variable
  σ τ υ : Ty

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
-- Box erasure + box count
------------------------------------------------------------

⌊_⌋ : Ty → Ty
⌊ base b ⌋ = base b
⌊ σ ⇒ τ ⌋ = ⌊ σ ⌋ ⇒ ⌊ τ ⌋
⌊ □ τ ⌋ = ⌊ τ ⌋

-- Boxity is a made-up measure on types that is designed so that
-- σ <: τ → boxity σ ≤ boxity τ
boxity : Ty → ℤ
boxity (base _) = + zero
boxity (σ ⇒ τ) = + 3 * (boxity τ) - boxity σ
boxity (□ τ) = suc (boxity τ)

-- The definition of boxity was chosen carefully so that the boxity of
-- (□ σ ⇒ □ τ) is strictly greater than (in fact, exactly one more
-- than) the boxity of □ (σ ⇒ τ).
boxity-ap : (σ τ : Ty) → boxity (□ σ ⇒ □ τ) ≡ + 1 + boxity (□ (σ ⇒ τ))
boxity-ap σ τ = begin-equality
  boxity (□ σ ⇒ □ τ)
                     ≡⟨⟩
  (+ 3 * (+ 1 + boxity τ) - (+ 1 + boxity σ))
                     ≡⟨ solve 2
                          (λ i j →
                             con (+ 3) :* (con (+ 1) :+ i) :- (con (+ 1) :+ j) :=
                             con (+ 1) :+ (con (+ 1) :+ ((con (+ 3) :* i :- j))))
                          refl (boxity τ) (boxity σ) ⟩
  + 1 + (+ 1 + (+ 3 * boxity τ - boxity σ))
                     ≡⟨⟩
  + 1 + boxity (□ (σ ⇒ τ))
  ∎

≡suc⇒< : {i j : ℤ} → i ≡ suc j → j < i
≡suc⇒< {i} eq = suc[i]≤j⇒i<j (≤-reflexive (sym eq))

boxity-ap-< : (σ τ : Ty) → boxity (□ (σ ⇒ τ)) < boxity (□ σ ⇒ □ τ)
boxity-ap-< σ τ = ≡suc⇒< (boxity-ap σ τ)
