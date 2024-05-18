open import Data.Empty
open import Relation.Binary using (Decidable ; DecidableEquality)

module ApplicativeLaws (B : Set) (DecB : DecidableEquality B) where

import Types
import Subtyping
import Typing

open module TypesB = Types B DecB
open module SubtypingB = Subtyping B DecB
open module TypingB = Typing B DecB

emptySig : Signature
emptySig = record { C = ⊥ ; Cty = λ x → ⊥-elim x }

open module TypingJudgmentB = TypingJudgment emptySig

variable
  s t u : Term□ Γ τ

infix 4 _≈_

compose : Term□ Γ ((τ ⇒ υ) ⇒ (σ ⇒ τ) ⇒ σ ⇒ υ)
compose =  ƛ (ƛ (ƛ (var (vs (vs vz)) ∙ (var (vs vz) ∙ var vz))))

id : Term□ Γ (σ ⇒ σ)
id = ƛ (var vz)

_<*>_ : Term□ Γ (□ (σ ⇒ τ)) → Term□ Γ (□ σ) → Term□ Γ (□ τ)
f <*> x = (ap ∙ f) ∙ x

infixl 5 _<*>_

data _≈_ : Term□ Γ τ → Term□ Γ τ → Set₁ where
  rfl : s ≈ s
  tr : s ≈ t → t ≈ u → s ≈ u
  sym : s ≈ t → t ≈ s
  cng : {Γ₁ Γ₂ : Ctx} {s t : Term□ Γ₁ σ} → (f : Term□ Γ₁ σ → Term□ Γ₂ τ) → s ≈ t → f s ≈ f t

  -- pure id <*> v = v                            -- Identity
  idt : (pure ∙ id) <*> s ≈ s

  -- pure f <*> pure x = pure (f x)               -- Homomorphism
  hom : (pure ∙ s) <*> (pure ∙ t) ≈ pure ∙ (s ∙ t)

  -- u <*> pure y = pure ($ y) <*> u              -- Interchange
  int : s <*> (pure ∙ t) ≈ (pure ∙ ƛ (var vz ∙ wk vz t)) <*> s

  -- pure (.) <*> u <*> v <*> w = u <*> (v <*> w) -- Composition
  pur : (pure ∙ compose) <*> s <*> t <*> u ≈ s <*> (t <*> u)
