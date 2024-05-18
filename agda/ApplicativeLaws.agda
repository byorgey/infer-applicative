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

compose : Term□ Γ ((τ ⇒ υ) ⇒ (σ ⇒ τ) ⇒ σ ⇒ υ)
compose =  ƛ (ƛ (ƛ (var (vs (vs vz)) ∙ (var (vs vz) ∙ var vz))))

id : Term□ Γ (σ ⇒ σ)
id = ƛ (var vz)

_<*>_ : Term□ Γ (□ (σ ⇒ τ)) → Term□ Γ (□ σ) → Term□ Γ (□ τ)
f <*> x = (ap ∙ f) ∙ x

infixl 5 _<*>_

-- Term equivalence up to Applicative laws
infix 4 _≈_
data _≈_ : Term□ Γ τ → Term□ Γ τ → Set₁ where

  -- Equivalence and congruence laws
  rfl : s ≈ s
  tr : s ≈ t → t ≈ u → s ≈ u
  sym : s ≈ t → t ≈ s
  cng : {Γ₁ Γ₂ : Ctx} {s t : Term□ Γ₁ σ} → (f : Term□ Γ₁ σ → Term□ Γ₂ τ) → s ≈ t → f s ≈ f t

  -- η-expansion
  eta : {t : Term□ Γ (σ ⇒ τ)} → t ≈ (ƛ (wk vz t ∙ var vz))

  -- Applicative laws

  -- pure id <*> v = v                            -- Identity
  idt : (pure ∙ id) <*> s ≈ s

  -- pure f <*> pure x = pure (f x)               -- Homomorphism
  hom : (pure ∙ s) <*> (pure ∙ t) ≈ pure ∙ (s ∙ t)

  -- u <*> pure y = pure ($ y) <*> u              -- Interchange
  int : s <*> (pure ∙ t) ≈ (pure ∙ ƛ (var vz ∙ wk vz t)) <*> s

  -- pure (.) <*> u <*> v <*> w = u <*> (v <*> w) -- Composition
  pur : (pure ∙ compose) <*> s <*> t <*> u ≈ s <*> (t <*> u)

-- Set up equational reasoning proof machinery!


coerce-id : (reflpf : τ <: τ) (t : Term□ Γ τ) → reflpf ≪ t ≈ t
coerce-id rfl _ = rfl
coerce-id (tr τ<:σ σ<:τ) t = {!!}  -- need antisymmetry, then we can just use IH twice

-- use IH twice, then use η-equivalence.
-- This is going to be extremely tedious without equational reasoning machinery.
coerce-id (arr τ₁<:τ₁ τ₂<:τ₂) t = {!!}

-- Use IH, then this is just identity law.
coerce-id (box σ<:σ) t = {!!}


-- Prove that any two subtyping proofs cause t to be elaborated into equivalent terms.
foo : (pf1 pf2 : σ <: τ) → (pf1 ≪ t) ≈ (pf2 ≪ t)
foo rfl rfl = rfl
foo rfl (tr pf2 pf3) = {!!}  -- If tr x y : σ <: σ, then why does (tr x y) ≪ t ≈ t?
  -- Lemma: if σ <: τ and τ <: σ then σ ≡ τ , i.e. <: is antisymmetric?
foo rfl (arr pf2 pf3) = {!!}
foo rfl (box pf2) = {!!}
foo (tr pf1 pf2) rfl = {!!}
foo (tr pf1 pf2) (tr pf3 pf4) = {!!}
foo (tr pf1 pf2) (arr pf3 pf4) = {!!}
foo (tr pf1 pf2) (box pf3) = {!!}
foo (tr pf1 pf2) pure = {!!}
foo (tr pf1 pf2) ap = {!!}
foo (arr pf1 pf2) rfl = {!!}
foo (arr pf1 pf2) (tr pf3 pf4) = {!!}
foo (arr pf1 pf2) (arr pf3 pf4) = {!!}
foo (box pf1) rfl = {!!}
foo (box pf1) (tr pf2 pf3) = {!!}
foo (box pf1) (box pf2) = {!!}
foo (box pf1) pure = {!!}
foo pure (tr pf2 pf3) = {!!}
foo pure (box pf2) = {!!}
foo pure pure = {!!}
foo ap (tr pf2 pf3) = {!!}
foo ap ap = {!!}
