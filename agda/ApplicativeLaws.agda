open import Relation.Binary.Bundles using (Setoid)
open import Data.Empty
open import Relation.Binary using (Decidable ; DecidableEquality)
open import Level
open import Relation.Nullary.Negation

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
  refl : s ≈ s
  trans : s ≈ t → t ≈ u → s ≈ u
  sym : s ≈ t → t ≈ s
  cong : {Γ₁ Γ₂ : Ctx} {s t : Term□ Γ₁ σ} → (f : Term□ Γ₁ σ → Term□ Γ₂ τ) → s ≈ t → f s ≈ f t

  -- η-expansion
  η : {t : Term□ Γ (σ ⇒ τ)} → t ≈ (ƛ (wk vz t ∙ var vz))

  -- Applicative laws

  -- pure id <*> v = v                            -- Identity
  idt : (pure ∙ id) <*> s ≈ s

  -- pure f <*> pure x = pure (f x)               -- Homomorphism
  hom : (pure ∙ s) <*> (pure ∙ t) ≈ pure ∙ (s ∙ t)

  -- u <*> pure y = pure ($ y) <*> u              -- Interchange
  int : s <*> (pure ∙ t) ≈ (pure ∙ ƛ (var vz ∙ wk vz t)) <*> s

  -- pure (.) <*> u <*> v <*> w = u <*> (v <*> w) -- Composition
  pur : (pure ∙ compose) <*> s <*> t <*> u ≈ s <*> (t <*> u)

-- Set up equational reasoning proof machinery.

≈-Setoid : (Γ : Ctx) (τ : Ty) → Setoid _ _
≈-Setoid Γ τ = record
  { Carrier = Term□ Γ τ
  ; _≈_ = _≈_
  ; isEquivalence = record
    { refl = refl
    ; sym = sym
    ; trans = trans
    }
  }

import Relation.Binary.Reasoning.Setoid
module ≈-Reasoning (Γ : Ctx) (τ : Ty) = Relation.Binary.Reasoning.Setoid (≈-Setoid Γ τ)

coerce-id : {Γ : Ctx} {τ : Ty} (reflpf : τ <: τ) (t : Term□ Γ τ) → reflpf ≪ t ≈ t
coerce-id rfl _ = refl
coerce-id (tr τ<:σ σ<:τ) t = {!!}  -- need antisymmetry, then we can just use IH twice

-- use IH twice, then use η-equivalence.
coerce-id {Γ = Γ} {τ = τ} (arr τ₁<:τ₁ τ₂<:τ₂) t = begin
  arr τ₁<:τ₁ τ₂<:τ₂ ≪ t
                                          ≈⟨ refl ⟩
  ƛ (τ₂<:τ₂ ≪ (wk vz t ∙ (τ₁<:τ₁ ≪ var vz)))
                                          ≈⟨ cong (λ x → ƛ (τ₂<:τ₂ ≪ (wk vz t ∙ x))) (coerce-id τ₁<:τ₁ (var vz)) ⟩
  ƛ (τ₂<:τ₂ ≪ (wk vz t ∙ (var vz)))
                                          ≈⟨ cong ƛ (coerce-id τ₂<:τ₂ _) ⟩
  ƛ (wk vz t ∙ (var vz))
                                          ≈⟨ sym η ⟩
  t ∎
  where
    open ≈-Reasoning Γ τ

-- Use IH, then this is just identity law.
coerce-id {Γ = Γ} {τ = τ} (box σ<:σ) t = begin
  box σ<:σ ≪ t
                                          ≈⟨ refl ⟩
  (ap ∙ (pure ∙ ƛ (σ<:σ ≪ var vz))) ∙ t
                                          ≈⟨ cong (λ x → (ap ∙ (pure ∙ ƛ x)) ∙ t) (coerce-id σ<:σ (var vz)) ⟩
  (ap ∙ (pure ∙ ƛ (var vz))) ∙ t
                                          ≈⟨ idt ⟩
  t ∎
  where
    open ≈-Reasoning Γ τ

-- Prove that any two subtyping proofs cause t to be elaborated into equivalent terms.

-- Once again, transitivity is the worst.  =(
-- Maybe rewrite ≪ to work with σ ◃ τ instead??

foo : {Γ : Ctx} {σ τ : Ty} {t : Term□ Γ σ} → (pf1 pf2 : σ ◃ τ) → ((◃→<: pf1) ≪ t) ≈ ((◃→<: pf2) ≪ t)
foo rfl rfl = refl
foo rfl (box pf2) = begin
  _
                                          ≈⟨ sym idt ⟩
  (ap ∙ (pure ∙ ƛ (var vz))) ∙ _
                                          ≈⟨ cong (λ x → (ap ∙ (pure ∙ ƛ x)) ∙ _) (sym (coerce-id (◃→<: pf2) _)) ⟩
  (ap ∙ (pure ∙ ƛ (◃→<: pf2 ≪ var vz))) ∙ _
  ∎
  where
    open ≈-Reasoning _ _

foo rfl (arr pf2 pf3) = begin
  _
                                          ≈⟨ η ⟩
  ƛ (wk vz _ ∙ (var vz))
                                          ≈⟨ cong ƛ (sym (coerce-id (◃→<: pf3) _)) ⟩
  ƛ (◃→<: pf3 ≪ (wk vz _ ∙ (var vz)))
                                          ≈⟨ cong (λ x → ƛ (◃→<: pf3 ≪ (wk vz _ ∙ x))) (sym (coerce-id (◃→<: pf2) _)) ⟩
  ƛ (◃→<: pf3 ≪ (wk vz _ ∙ (◃→<: pf2 ≪ var vz)))
  ∎
  where
    open ≈-Reasoning _ _

foo rfl (pure pf2) = {!!}
foo rfl (ap pf2 pf3) = {!!}
foo rfl (ap□ pf2 pf3) = {!!}
foo (box pf1) rfl = {!!}
foo (box pf1) (box pf2) = cong (λ z → (ap ∙ (pure ∙ ƛ z)) ∙ _) (foo pf1 pf2)
foo (box pf1) (pure pf2) = {!!}
foo (box pf1) (ap pf2 pf3) = {!!}
foo (box pf1) (ap□ pf2 pf3) = {!!}
foo (arr pf1 pf2) rfl = {!!}
foo (arr pf1 pf2) (arr pf3 pf4) = {!!}
foo (arr pf1 pf2) (ap□ pf3 pf4) = {!!}
foo (pure pf1) rfl = {!!}
foo (pure pf1) (box pf2) = {!!}
foo (pure pf1) (pure pf2) = cong (_∙_ pure) (foo pf1 pf2)
foo (pure pf1) (ap pf2 pf3) = {!!}
foo (pure pf1) (ap□ pf2 pf3) = {!!}
foo (ap pf1 pf2) rfl = {!!}
foo (ap pf1 pf2) (box pf3) = {!!}
foo (ap pf1 pf2) (pure pf3) = {!!}
foo (ap pf1 pf2) (ap pf3 pf4) = {!!}
foo (ap pf1 pf2) (ap□ pf3 pf4) = {!!}
foo (ap□ pf1 pf2) rfl = {!!}
foo (ap□ pf1 pf2) (box pf3) = {!!}
foo (ap□ pf1 pf2) (arr pf3 pf4) = {!!}
foo (ap□ pf1 pf2) (pure pf3) = {!!}
foo (ap□ pf1 pf2) (ap pf3 pf4) = {!!}
foo (ap□ pf1 pf2) (ap□ pf3 pf4) = {!!}

-- foo rfl rfl = refl
-- foo rfl (tr pf2 pf3) = {!!}  -- If tr x y : σ <: σ, then why does (tr x y) ≪ t ≈ t?
-- foo rfl (arr pf2 pf3) = {!!}  -- antisymmetry
-- foo {Γ = Γ} {σ = σ} {t = t} rfl (box pf2) = begin
--   t
--                                           ≈⟨ sym idt ⟩
--   (ap ∙ (pure ∙ ƛ (var vz))) ∙ t
--                                           ≈⟨ cong (λ x → (ap ∙ (pure ∙ ƛ x)) ∙ t) (sym (coerce-id pf2 (var vz))) ⟩
--   (ap ∙ (pure ∙ ƛ (pf2 ≪ var vz))) ∙ t
--   ∎
--   where
--     open ≈-Reasoning Γ σ

-- foo (tr pf1 pf2) rfl = {!!}   -- antisymmetry
-- foo (tr pf1 pf2) (tr pf3 pf4) = {!!}  -- this one is terrible, the middle types aren't the same
-- foo (tr pf1 pf2) (arr pf3 pf4) = {!!}
-- foo (tr pf1 pf2) (box pf3) = {!!}
-- foo (tr pf1 pf2) pure = {!!}
-- foo (tr pf1 pf2) ap = {!!}
-- foo (arr pf1 pf2) rfl = {!!}
-- foo (arr pf1 pf2) (tr pf3 pf4) = {!!}
-- foo (arr pf1 pf2) (arr pf3 pf4) = {!!}
-- foo (box pf1) rfl = {!!}
-- foo (box pf1) (tr pf2 pf3) = {!!}
-- foo (box pf1) (box pf2) = cong (λ z → (ap ∙ (pure ∙ ƛ z)) ∙ _) (foo pf1 pf2)
-- foo (box pf1) pure = {!!}
-- foo pure (tr pf2 pf3) = {!!}
-- foo pure (box pf2) = {!!}
-- foo pure pure = refl
-- foo ap (tr pf2 pf3) = {!!}
-- foo ap ap = refl
