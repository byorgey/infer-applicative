open import Data.Product
open import Data.Sum
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable using (yes; no)

module OneLevelTypesIndexed (B : Set) (DecB : DecidableEquality B) where

data Boxity : Set where
  b0 : Boxity
  b1 : Boxity

data Ty : Boxity → Set where
  □_ : Ty b0 → Ty b1
  base : B → Ty b0
  _⇒_ : {a b : Boxity} → Ty a → Ty b → Ty b0

infixr 2 _⇒_
infix 30 □_

base-inj : {b₁ b₂ : B} → base b₁ ≡ base b₂ → b₁ ≡ b₂
base-inj refl = refl

-- ⇒-inj : {τ₁₁ τ₁₂ τ₂₁ τ₂₂ : Ty} → ((τ₁₁ ⇒ τ₁₂) ≡ (τ₂₁ ⇒ τ₂₂)) → (τ₁₁ ≡ τ₂₁) × (τ₁₂ ≡ τ₂₂)
-- ⇒-inj refl = refl , refl

□-inj : {τ₁ τ₂ : Ty b0} → (□ τ₁ ≡ □ τ₂) → (τ₁ ≡ τ₂)
□-inj refl = refl

------------------------------------------------------------
-- Type equality is decidable
------------------------------------------------------------

SomeTy : Set
SomeTy = Σ Boxity Ty

some : {b : Boxity} → Ty b → SomeTy
some {b} σ = b , σ

≡Ty-Dec : {b : Boxity} → DecidableEquality (Ty b)
≡SomeTy-Dec : DecidableEquality SomeTy

≡Ty-Dec (□ σ) (□ τ) with ≡Ty-Dec σ τ
... | yes p = yes (cong □_ p)
... | no τ₁≢τ₂ = no λ eq → τ₁≢τ₂ (□-inj eq)
≡Ty-Dec (base x) (base y) with DecB x y
... | no x≢y = no λ eq → x≢y (base-inj eq)
... | yes x≡y = yes (cong base x≡y)
≡Ty-Dec (σ₁ ⇒ σ₂) (τ₁ ⇒ τ₂) with ≡SomeTy-Dec (some σ₁) (some τ₁) | ≡SomeTy-Dec (some σ₂) (some τ₂)
... | res1 | res2 = {!!}
-- ... | no σ₁≢τ₁ | _ = no (λ eq → σ₁≢τ₁ (proj₁ ?))
-- ... | yes _ | no τ₁≢τ₂ = no (λ eq → τ₁≢τ₂ (proj₂ ?))
-- ... | yes σ₁≡σ₂ | yes τ₁≡τ₂ = yes (cong₂ _⇒_ σ₁≡σ₂ τ₁≡τ₂)
≡Ty-Dec (base _) (_ ⇒ _) = no (λ ())
≡Ty-Dec (_ ⇒ _) (base _) = no (λ ())

-- ≡SomeTy-Dec (b0 , snd) (b0 , snd₁) = {!!}
-- ≡SomeTy-Dec (b0 , base x) (b1 , □ snd₁) = {!!}
-- ≡SomeTy-Dec (b0 , (snd ⇒ snd₂)) (b1 , snd₁) = {!!}
-- ≡SomeTy-Dec (b1 , snd) (b0 , snd₁) = {!!}
-- ≡SomeTy-Dec (b1 , □ σ) (b1 , □ τ) 

-- ≡Ty-Dec : DecidableEquality Ty
-- ≡UTy-Dec (base b₁) (base b₂)  with DecB b₁ b₂
-- ... | no b₁≢b₂ = no λ eq → b₁≢b₂ (base-inj eq)
-- ... | yes b₁≡b₂ = yes (cong base b₁≡b₂)
-- ≡UTy-Dec (σ₁ ⇒ τ₁) (σ₂ ⇒ τ₂) with ≡Ty-Dec σ₁ σ₂ | ≡Ty-Dec τ₁ τ₂
-- ... | no σ₁≢σ₂ | _ = no (λ eq → σ₁≢σ₂ (proj₁ (⇒-inj eq)))
-- ... | yes _ | no τ₁≢τ₂ = no (λ eq → τ₁≢τ₂ (proj₂ (⇒-inj eq)))
-- ... | yes σ₁≡σ₂ | yes τ₁≡τ₂ = yes (cong₂ _⇒_ σ₁≡σ₂ τ₁≡τ₂)
-- ≡UTy-Dec (base _) (_ ⇒ _) = no (λ ())
-- ≡UTy-Dec (_ ⇒ _) (base _) = no (λ ())

-- ≡Ty-Dec (□ τ₁) (□ τ₂) with ≡UTy-Dec τ₁ τ₂
-- ... | yes p = yes (cong □_ p)
-- ... | no τ₁≢τ₂ = no λ eq → τ₁≢τ₂ (□-inj eq)
-- ≡Ty-Dec (· τ₁) (· τ₂) with ≡UTy-Dec τ₁ τ₂
-- ... | yes p = yes (cong ·_ p)
-- ... | no τ₁≢τ₂ = no λ eq → τ₁≢τ₂ (·-inj eq)
-- ≡Ty-Dec (□ _) (· _) = no (λ ())
-- ≡Ty-Dec (· _) (□ _) = no (λ ())
