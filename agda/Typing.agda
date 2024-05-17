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

  wkv : (x : Var Γ σ) → Var (Γ - x) τ → Var Γ τ
  wkv vz y = vs y
  wkv (vs x) vz = vz
  wkv (vs x) (vs y) = vs (wkv x y)

  wk : (x : Var Γ σ) → Term□ (Γ - x) τ → Term□ Γ τ
  wk x (var y) = var (wkv x y)
  wk x (ƛ t) = ƛ (wk (vs x) t)
  wk x (t₁ ∙ t₂) = wk x t₁ ∙ wk x t₂
  wk _ (con c) = con c
  wk _ pure = pure
  wk _ ap = ap

  -- Coercion insertion
  -- Should definitely present these rules in the paper!

  infixr 3 _≪_

  _≪_ : σ <: τ → Term□ Γ σ → Term□ Γ τ
  rfl ≪ t = t
  tr σ<:τ τ<:υ ≪ t = τ<:υ ≪ σ<:τ ≪ t
  -- η-expand at function types to apply the coercions --- could optimize this part
  -- of course, especially if t is syntactically a lambda already
  arr τ₁<:σ₁ σ₂<:τ₂ ≪ t = ƛ (σ₂<:τ₂ ≪ (wk vz t ∙ (τ₁<:σ₁ ≪ var vz)))
  -- -- essentially 'fmap coerce'
  box σ<:τ ≪ t = (ap ∙ (pure ∙ ƛ (σ<:τ ≪ var vz))) ∙ t
  pure ≪ t = pure ∙ t
  ap ≪ t = ap ∙ t

  elaborate : Term Γ τ → Term□ Γ τ
  elaborate (sub σ<:τ t) = σ<:τ ≪ elaborate t
  elaborate (var i) = var i
  elaborate (ƛ _ s) = ƛ (elaborate s)
  elaborate (t₁ ∙ t₂) = elaborate t₁ ∙ elaborate t₂
  elaborate (con c) = con c
