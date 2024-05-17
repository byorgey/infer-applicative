open import Relation.Binary using (Decidable ; DecidableEquality)
open import Data.Nat
open import Data.Fin using (Fin ; zero ; suc ; _↑ʳ_) renaming (_+_ to _+F_)
open import Data.Product
open import Relation.Binary.PropositionalEquality

module Typing (B : Set) (DecB : DecidableEquality B) where

variable
  n : ℕ

import Types
open module TypesB = Types B DecB

import Subtyping
open module SubtypingB = Subtyping B DecB

data Ctx : Set where
  ∅ : Ctx
  _,_ : Ctx → Ty → Ctx

infixr 4 _,_

variable
  Γ : Ctx
  σ τ : Ty

-- Approach to variables + weakening taken from
-- Keller + Alternkirch, "Normalization by hereditary substitutions"
-- https://www.cs.nott.ac.uk/~psztxa/publ/msfp10.pdf
data Var : Ctx → Ty → Set₁ where
  vz : Var (Γ , τ) τ
  vs : Var Γ τ → Var (Γ , σ) τ

-- _++_ : {m n : ℕ} → Ctx m → Ctx n → Ctx (n + m)
-- Γ₁ ++ ∅ = Γ₁
-- Γ₁ ++ (Γ₂ , τ) = (Γ₁ ++ Γ₂) , τ

-- extIndex : {m : ℕ} {n : ℕ} (Γ₁ : Ctx m) (Γ₂ : Ctx n) (i : Fin m) → Γ₁ ! i ≡ (Γ₁ ++ Γ₂) ! (n ↑ʳ i)
-- extIndex _ ∅ _ = refl
-- extIndex Γ₁ (Γ₂ , _) i = extIndex Γ₁ Γ₂ i

record Signature : Set₁ where
  field
    C : Set
    Cty : C → Ty

module TypingJudgment (Sig : Signature) where

  open Signature Sig

  -- Type-indexed terms, with applicative subtyping
  data Term : Ctx → Ty → Set₁ where
    sub : σ <: τ → Term Γ σ → Term Γ τ
    var : Var Γ τ → Term Γ τ
    ƛ : Ty → Term (Γ , σ) τ → Term Γ (σ ⇒ τ)
    _∙_ : Term Γ (σ ⇒ τ) → Term Γ σ → Term Γ τ
    con : (c : C) → Term Γ (Cty c)

  -- Type-indexed terms extended with extra `pure` and `ap` constants
  data Term□ : Ctx → Ty → Set₁ where
    var : Var Γ τ → Term□ Γ τ
    ƛ : Term□ (Γ , σ) τ → Term□ Γ (σ ⇒ τ)
    _∙_ : Term□ Γ (σ ⇒ τ) → Term□ Γ σ → Term□ Γ τ
    con : (c : C) → Term□ Γ (Cty c)
    pure : Term□ Γ (τ ⇒ □ τ)
    ap : Term□ Γ (□ (σ ⇒ τ) ⇒ (□ σ ⇒ □ τ))

  _-_ : (Γ : Ctx) → Var Γ σ → Ctx
  ∅ - ()
  (Γ , _) - vz = Γ
  (Γ , x) - vs v = (Γ - v) , x

--   -- weaken : {m n : ℕ} → {Γ₁ : Ctx m} {σ : Ty} (Γ₂ : Ctx n) → Term□ Γ₁ τ → Term□ ((Γ₁ , σ) ++ Γ₂) τ
--   -- weaken Γ₂ (var i) = {!!}
--   -- weaken Γ₂ (ƛ t) = {!!}
--   -- weaken Γ₂ (t ∙ t₁) = {!!}
--   -- weaken Γ₂ (con c) = {!!}
--   -- weaken Γ₂ pure = {!!}
--   -- weaken Γ₂ ap = {!!}

--   -- weaken {n = n} {Γ₁ = Γ₁} {Γ₂ = Γ₂} (var i) rewrite (extIndex Γ₁ Γ₂ i) = var (n ↑ʳ i)
--   -- weaken (ƛ t) = ƛ {!!}
--   -- weaken (t ∙ t₁) = {!!}
--   -- weaken (con c) = {!!}
--   -- weaken pure = {!!}
--   -- weaken ap = {!!}

--   -- weaken : Term□ Γ τ → Term□ (Γ , σ) τ
--   -- weaken (var i) = var (suc i)
--   -- weaken (ƛ t) = {!weaken t!}
--   -- weaken (t₁ ∙ t₂) = weaken t₁ ∙ weaken t₂
--   -- weaken (con c) = con c
--   -- weaken pure = pure
--   -- weaken ap = ap

--   -- Coercion insertion

--   coerce : σ <: τ → Term□ Γ σ → Term□ Γ τ
--   coerce rfl t = t
--   coerce (tr σ<:τ τ<:υ) t = coerce τ<:υ (coerce σ<:τ t)
--   -- η-expand at function types to apply the coercions --- could optimize this part
--   -- of course, especially if t is syntactically a lambda already
--   coerce (arr τ₁<:σ₁ σ₂<:τ₂) t = ƛ (coerce σ₂<:τ₂ ({!!} ∙ coerce τ₁<:σ₁ (var vz)))
--   -- essentially 'fmap coerce'
--   coerce (box σ<:τ) t = (ap ∙ (pure ∙ ƛ (coerce σ<:τ (var vz)))) ∙ t
--   coerce pure t = pure ∙ t
--   coerce ap t = ap ∙ t

--   -- elaborate : {t : Term n} {τ : Ty} → Γ ⊢□ t ∈ τ → Term□ Γ τ
--   -- elaborate (sub σ<:τ t) = coerce σ<:τ (elaborate t)
--   -- elaborate (var i) = var i
--   -- elaborate (lam s) = ƛ (elaborate s)
--   -- elaborate (app t₁ t₂) = elaborate t₁ ∙ elaborate t₂


--   -- -- Regular typing, with no subtyping
--   -- infix 1 _⊢_∈_

--   -- data _⊢_∈_ : Ctx n → Term□ n → Ty → Set₁ where
--   --   var : (i : Fin n) → Γ ⊢ var i ∈ (Γ ! i)
--   --   lam : {σ τ : Ty} {t : Term□ (suc n)} → Γ , σ ⊢ t ∈ τ → Γ ⊢ ƛ σ t ∈ σ ⇒ τ
--   --   app : {t₁ t₂ : Term□ n} {σ τ : Ty} → Γ ⊢ t₁ ∈ σ ⇒ τ → Γ ⊢ t₂ ∈ σ → Γ ⊢ (t₁ ∙ t₂) ∈ τ
--   --   pure : {τ : Ty} → Γ ⊢ pure ∈ τ ⇒ □ τ
--   --   ap : {σ τ : Ty} → Γ ⊢ ap ∈ □ (σ ⇒ τ) ⇒ (□ σ ⇒ □ τ)

--   -- weaken : {σ τ : Ty} {t : Term□ n} → Γ ⊢ t ∈ τ → Γ , σ ⊢ (weakenTerm t) ∈ τ
--   -- weaken (var i) = {!!}
--   -- weaken (lam pf) = {!!}
--   -- weaken (app pf pf₁) = {!!}
--   -- weaken pure = {!!}
--   -- weaken ap = {!!}

--   -- Term□′ : {n : ℕ} → Ctx n → Ty → Set₁
--   -- Term□′ {n} Γ τ = Σ[ t ∈ Term□ n ] (Γ ⊢ t ∈ τ)

--   -- ƛ′ : {σ τ : Ty} → Term□′ (Γ , σ) τ → Term□′ Γ (σ ⇒ τ)
--   -- ƛ′ {σ = σ} (t , p) = ƛ σ t , lam p

--   -- _∙′_ : {σ τ : Ty} → Term□′ Γ (σ ⇒ τ) → Term□′ Γ σ → Term□′ Γ τ
--   -- (t₁ , p₁) ∙′ (t₂ , p₂) = t₁ ∙ t₂ , app p₁ p₂

--   -- pure′ : {τ : Ty} → Term□′ Γ (τ ⇒ □ τ)
--   -- pure′ = pure , pure

--   -- ap′ : {σ τ : Ty} → Term□′ Γ (□ (σ ⇒ τ) ⇒ (□ σ ⇒ □ τ))
--   -- ap′ = ap , ap

--   -- weaken′ : {σ τ : Ty} → Term□′ Γ τ → Term□′ (Γ , σ) τ
--   -- weaken′ = {!!}
