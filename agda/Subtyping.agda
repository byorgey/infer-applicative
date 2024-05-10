open import Function using (_∘_)
open import Data.Bool
open import Data.Nat
open import Data.Fin hiding (_≥_)
open import Data.Product using (Σ-syntax ; _,_)
open import Data.Sum
open import Data.Product
open import Relation.Nullary.Negation
open import Relation.Nullary.Decidable
open import Data.Empty
open import Relation.Binary using (Decidable ; DecidableEquality)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality using (_≅_ ; refl) renaming (cong₂ to ≅cong₂)

module Subtyping (B : Set) (DecB : DecidableEquality B) where

import Types
open module TypesB = Types B DecB

------------------------------------------------------------
-- Subtyping
------------------------------------------------------------

data _<:_ : Ty → Ty → Set where
  rfl : {τ : Ty} → τ <: τ
  tr : {σ τ υ : Ty} → σ <: τ → τ <: υ → σ <: υ
  arr : {τ₁ τ₂ σ₁ σ₂ : Ty} → (τ₁ <: σ₁) → (σ₂ <: τ₂) → (σ₁ ⇒ σ₂ <: τ₁ ⇒ τ₂)
  box : {σ τ : Ty} → (σ <: τ) → (□ σ <: □ τ)
  pure : {τ : Ty} → τ <: □ τ
  ap : {σ τ : Ty} → □ (σ ⇒ τ) <: □ σ ⇒ □ τ

infix 1 _<:_

-- Observation: given transitivity, we can split arr into two rules:
--   arrL : τ₁ <: σ₁ → (σ₁ ⇒ τ₂ <: τ₁ ⇒ τ₂)
--   arrR : σ₂ <: τ₂ → (τ₁ ⇒ σ₂ <: τ₁ ⇒ τ₂)
-- Not sure if this would be helpful or not.
--
-- If we do that, tr is the only rule which involves branching.  If
-- we tried to then eliminate tr, we would either need to
-- re-introduce some kind of branching constructor
-- (i.e. reconstitute arr), or else have only a linear chain of
-- combinators, which would necessarily need to operate implicitly
-- on some kind of stack or something.  I don't know if that's a
-- good idea.  Maybe this leads to something sequent-calculus-like?

-- First attempt at inversion lemma for subtyping, but as stated this is
-- not true, because of PURE!
{-
⇒<:⇒ : {σ τ υ : Ty} → σ ⇒ τ <: υ → Σ[ υ₁ ∈ Ty ] Σ[ υ₂ ∈ Ty ] (υ ≡ (υ₁ ⇒ υ₂))
⇒<:⇒ {σ = σ} {τ = τ} rfl = σ , τ , refl
⇒<:⇒ (tr σ⇒τ<:τ₁ τ₁<:υ) = {!!}
⇒<:⇒ (arr {τ₁ = τ₁} {τ₂ = τ₂} σ⇒τ<:υ σ⇒τ<:υ₁) = τ₁ , τ₂ , refl
⇒<:⇒ pure = {!!}
-}

-- Should work the other way around, though...

-- Argh, no, this is also false because of AP!
{-
⇒<:⇒ : {σ τ υ : Ty} → σ <: τ ⇒ υ → Σ[ σ₁ ∈ Ty ] Σ[ σ₂ ∈ Ty ] (σ ≡ (σ₁ ⇒ σ₂))
⇒<:⇒ {τ = τ} {υ = υ} rfl = τ , υ , refl
⇒<:⇒ (tr σ<:τ₁ τ₁<:τ⇒υ) with ⇒<:⇒ τ₁<:τ⇒υ
... | τ₁₁ , τ₁₂ , τ₁≡τ₁₁⇒τ₁₂ rewrite τ₁≡τ₁₁⇒τ₁₂ = ⇒<:⇒ σ<:τ₁
⇒<:⇒ (arr σ<:τ⇒υ σ<:τ⇒υ₁) = {!!}
⇒<:⇒ ap = {!!}
-}

--------------------------------------------------
-- Some inversion lemmas about subtyping

<:B-inv : {τ : Ty} {b : B} → (τ <: base b) → (τ ≡ base b)
<:B-inv rfl = refl
<:B-inv (tr τ<:τ₁ τ₁<:b) rewrite <:B-inv τ₁<:b = <:B-inv τ<:τ₁

¬□<:B : {τ : Ty} {b : B} → ¬ (□ τ <: base b)
¬□<:B □τ<:b with <:B-inv □τ<:b
... | ()

¬⇒<:B : {σ τ : Ty} {b : B} → ¬ (σ ⇒ τ <: base b)
¬⇒<:B σ⇒τ<:b with <:B-inv σ⇒τ<:b
... | ()

□^_∙_ : ℕ → Ty → Ty
□^ zero ∙ τ = τ
□^ suc n ∙ τ = □ (□^ n ∙ τ)

infix 5 □^_∙_

data LiftedBase (b : B) : Ty → Set where
  IsBase : LiftedBase b (base b)
  IsBox : {τ : Ty} → LiftedBase b τ → LiftedBase b (□ τ)

-- Can we get rid of LiftedBase --- is it just a special case of BaseTree etc.?

LB⇒□^ : {b : B} {τ : Ty} → LiftedBase b τ → Σ[ n ∈ ℕ ] τ ≡ □^ n ∙ base b
LB⇒□^ IsBase = zero , refl
LB⇒□^ (IsBox LB) with LB⇒□^ LB
... | k , τ≡□^kb = suc k , cong □_ τ≡□^kb

B<:LB : {b : B} {τ : Ty} → LiftedBase b τ → base b <: τ
B<:LB IsBase = rfl
B<:LB (IsBox lb) = tr (B<:LB lb) pure

B<:-inv : {b : B} {σ τ : Ty} → σ <: τ → LiftedBase b σ → LiftedBase b τ
B<:-inv rfl IsBase = IsBase
B<:-inv (tr b<:τ₁ τ₁<:τ) IsBase = B<:-inv τ₁<:τ (B<:-inv b<:τ₁ IsBase)
B<:-inv pure IsBase = IsBox IsBase
B<:-inv rfl (IsBox LBσ) = IsBox LBσ
B<:-inv (tr □τ₂<:τ₁ τ₁<:τ) (IsBox LBσ) = B<:-inv τ₁<:τ (B<:-inv □τ₂<:τ₁ (IsBox LBσ))
B<:-inv (box σ<:τ) (IsBox LBσ) = IsBox (B<:-inv σ<:τ LBσ)
B<:-inv pure (IsBox LBσ) = IsBox (IsBox LBσ)

B<:□-inv : {b : B} {τ : Ty} → base b <: □ τ → base b <: τ
B<:□-inv b<:□τ with B<:-inv b<:□τ IsBase
... | IsBox LBbτ = B<:LB LBbτ

¬LB<:⇒ : {b : B} {σ τ₁ τ₂ : Ty} → LiftedBase b σ → ¬ (σ <: τ₁ ⇒ τ₂)
¬LB<:⇒ LB σ<:τ₁⇒τ₂ with B<:-inv σ<:τ₁⇒τ₂ LB
... | ()

¬B<:⇒ : {b : B} {τ₁ τ₂ : Ty} → ¬ (base b <: τ₁ ⇒ τ₂)
¬B<:⇒ = ¬LB<:⇒ IsBase

data TyShape : Set where
  base : B → TyShape
  _⇒_ : TyShape → TyShape → TyShape

-- A ShapedTy is a type, but indexed by its shape.  Not sure whether we really need this.
data ShapedTy : TyShape → Set where
  base : (b : B) → ShapedTy (base b)
  _⇒_ : {l : TyShape} → ShapedTy l → {r : TyShape} → ShapedTy r → ShapedTy (l ⇒ r)
  □_ : {t : TyShape} → ShapedTy t → ShapedTy t

⟦_⟧ : {t : TyShape} → ShapedTy t → Ty
⟦ base b ⟧ = base b
⟦ l ⇒ r ⟧ = ⟦ l ⟧ ⇒ ⟦ r ⟧
⟦ □ t ⟧ = □ ⟦ t ⟧

⟨_⟩ : Ty → TyShape
⟨ base b ⟩ = base b
⟨ σ ⇒ τ ⟩ = ⟨ σ ⟩ ⇒ ⟨ τ ⟩
⟨ □ τ ⟩ = ⟨ τ ⟩

⟪_⟫ : (τ : Ty) → ShapedTy ⟨ τ ⟩
⟪ base b ⟫ = base b
⟪ σ ⇒ τ ⟫ = ⟪ σ ⟫ ⇒ ⟪ τ ⟫
⟪ □ τ ⟫ = □ ⟪ τ ⟫

_≡⟦⟪⟫⟧ : (τ : Ty) → τ ≡ ⟦ ⟪ τ ⟫ ⟧
base b ≡⟦⟪⟫⟧  = refl
(σ ⇒ τ) ≡⟦⟪⟫⟧  = cong₂ _⇒_ (σ ≡⟦⟪⟫⟧) (τ ≡⟦⟪⟫⟧)
(□ τ) ≡⟦⟪⟫⟧ = cong □_ (τ ≡⟦⟪⟫⟧)

_≡⟨⟦⟧⟩ : {s : TyShape} → (t : ShapedTy s) → s ≡ ⟨ ⟦ t ⟧ ⟩
base b ≡⟨⟦⟧⟩ = refl
(l ⇒ r) ≡⟨⟦⟧⟩ = cong₂ _⇒_ (l ≡⟨⟦⟧⟩) (r ≡⟨⟦⟧⟩)
□ t ≡⟨⟦⟧⟩ = t ≡⟨⟦⟧⟩

-- soundness?  Not sure how to express this so it typechecks.  Tried using heterogeneous equality
-- but not yet able to figure out how to make the node case go through.

-- _≅⟪⟦⟧⟫ : {s : TyShape} → (t : ShapedTy s) → t ≅ ⟪ ⟦ t ⟧ ⟫
-- base b ≅⟪⟦⟧⟫ = refl
-- _≅⟪⟦⟧⟫ {node lt rt} (node l r) with l ≡⟨⟦⟧⟩
-- ... | eq = {!!}
-- box t ≅⟪⟦⟧⟫ = {!!}

-- Theorem: if σ <: τ, then σ and τ have the same underlying TyShape.

<:→⟨⟩ : {σ τ : Ty} → σ <: τ → ⟨ σ ⟩ ≡ ⟨ τ ⟩
<:→⟨⟩ rfl = refl
<:→⟨⟩ (tr σ<:τ₁ τ₁<:τ) = trans (<:→⟨⟩ σ<:τ₁) (<:→⟨⟩ τ₁<:τ)
<:→⟨⟩ (arr τ₁<:σ₁ σ₂<:τ₂) = cong₂ _⇒_ (sym (<:→⟨⟩ τ₁<:σ₁)) (<:→⟨⟩ σ₂<:τ₂)
<:→⟨⟩ (box σ<:τ) = <:→⟨⟩ σ<:τ
<:→⟨⟩ pure = refl
<:→⟨⟩ ap = refl

------------------------------------------------------------
-- Transitivity-free subtyping
------------------------------------------------------------

-- Version of transitivity-free subtyping relation on normal types
-- rather than ShapedTys.  I had to work very, very hard to come up
-- with a definition that was correct and allows proving
-- transitivity admissible.
--
-- Building an actual proof looks like (1) first clearing away matching
-- or RHS boxes with box and pure, then (2) using ap to push existing
-- LHS boxes inwards, and/or using ap□ to create boxes and push them
-- inwards; and (3) using arr to recurse on the subtrees.

infix 1 _◃_

data _◃_ : Ty → Ty → Set where
  rfl : {τ : Ty} → τ ◃ τ
  box : {σ τ : Ty} → (σ ◃ τ) → □ σ ◃ □ τ
  arr : {σ₁ σ₂ τ₁ τ₂ : Ty} → (τ₁ ◃ σ₁) → (σ₂ ◃ τ₂) → (σ₁ ⇒ σ₂ ◃ τ₁ ⇒ τ₂)
  pure : {σ τ : Ty} → (σ ◃ τ) → σ ◃ □ τ
  ap : {σ σ₁ σ₂ τ : Ty} → (σ ◃ σ₁ ⇒ σ₂) → (□ σ₁ ⇒ □ σ₂ ◃ τ) → (□ σ ◃ τ)
  ap□ : {σ σ₁ σ₂ τ : Ty} → (σ ◃ σ₁ ⇒ σ₂) → (□ σ₁ ⇒ □ σ₂ ◃ τ) → (σ ◃ τ)

-- pureL was getting in the way, and in theory we never want to do
-- it unless we immediately do an ap right after.  So introduced
-- ap□ which corresponds to doing pureL then ap.  However, we
-- still need the original ap because we might want to prove a
-- relation which already has a □ on the LHS.

-- pureL : {σ τ : Ty} → (□ σ ◃ τ) → σ ◃ τ

-- Let's prove that ◃ actually completely characterizes (i.e. is
-- logically equivalent to) subtyping.

-- One direction (easy): if σ ◃ τ then σ <: τ.
◃→<: : {σ τ : Ty} → σ ◃ τ → σ <: τ
◃→<: rfl = rfl
◃→<: (box σ◃τ) = box (◃→<: σ◃τ)
◃→<: (pure σ◃τ) = tr (◃→<: σ◃τ) pure
◃→<: (ap σ◃σ₁⇒σ₂ □σ₁⇒□σ₂◃τ) = tr (box (◃→<: σ◃σ₁⇒σ₂)) (tr ap (◃→<: □σ₁⇒□σ₂◃τ))
◃→<: (ap□ σ◃σ₁⇒σ₂ □σ₁⇒□σ₂◃τ) = tr (◃→<: σ◃σ₁⇒σ₂) (tr pure (tr ap (◃→<: □σ₁⇒□σ₂◃τ)))
◃→<: (arr σ◃τ₁ τ₁◃τ) = arr (◃→<: σ◃τ₁) (◃→<: τ₁◃τ)

-- Harder direction: if σ <: τ then σ ◃ τ.  The key difficulty is to
-- show that transitivity is admissible, i.e. anything we could
-- prove with transitivity we can also prove without it.  We also
-- need a couple mutually inductive lemmas.
--
-- Blah blah cut elimination...

◃-trans : {σ τ υ : Ty} → σ ◃ τ → τ ◃ υ → σ ◃ υ
◃-trans-arr-ap□ : {τ₁ τ₂ σ₁ σ₂ υ₁ υ₂ υ : Ty} → τ₁ ◃ σ₁ → σ₂ ◃ τ₂ → (τ₁ ⇒ τ₂ ◃ υ₁ ⇒ υ₂) → (□ υ₁ ⇒ □ υ₂ ◃ υ) → σ₁ ⇒ σ₂ ◃ υ
◃-trans-pureL : {σ τ υ : Ty} → σ ◃ τ → □ τ ◃ υ → σ ◃ υ

◃-trans rfl τ◃υ = τ◃υ
◃-trans (box σ◃τ) rfl = box σ◃τ
◃-trans (box σ◃τ) (box τ◃υ) = box (◃-trans σ◃τ τ◃υ)
◃-trans (box σ◃τ) (pure □τ◃υ) = pure (◃-trans (box σ◃τ) □τ◃υ)
◃-trans (box σ◃τ) (ap □τ◃σ₁⇒σ₂ □σ₁⇒□σ₂◃υ) = ap (◃-trans σ◃τ □τ◃σ₁⇒σ₂) □σ₁⇒□σ₂◃υ
◃-trans (box σ◃τ) (ap□ □τ◃σ₁⇒σ₂ □σ₁⇒□σ₂◃υ) = ap (◃-trans (pure σ◃τ) □τ◃σ₁⇒σ₂) □σ₁⇒□σ₂◃υ
◃-trans (arr τ₁◃σ₁ σ₂◃τ₂) rfl = arr τ₁◃σ₁ σ₂◃τ₂
◃-trans (arr τ₁◃σ₁ σ₂◃τ₂) (arr τ₁◃υ₁ υ₂◃τ₂) = arr (◃-trans τ₁◃υ₁ τ₁◃σ₁) (◃-trans σ₂◃τ₂ υ₂◃τ₂)
◃-trans (arr τ₁◃σ₁ σ₂◃τ₂) (pure τ₁⇒τ₂◃τ) = pure (◃-trans (arr τ₁◃σ₁ σ₂◃τ₂) τ₁⇒τ₂◃τ)
◃-trans (arr τ₁◃σ₁ σ₂◃τ₂) (ap□ τ₁⇒τ₂◃υ₁⇒υ₂ □υ₁⇒□υ₂◃υ) = ◃-trans-arr-ap□ τ₁◃σ₁ σ₂◃τ₂ τ₁⇒τ₂◃υ₁⇒υ₂ □υ₁⇒□υ₂◃υ
◃-trans (pure σ◃τ) □τ◃υ = ◃-trans-pureL σ◃τ □τ◃υ
◃-trans (ap σ◃σ₁⇒σ₂ □σ₁⇒□σ₂◃τ) τ◃υ = ap σ◃σ₁⇒σ₂ (◃-trans □σ₁⇒□σ₂◃τ τ◃υ)
◃-trans (ap□ σ◃σ₁⇒σ₂ □σ₁⇒□σ₂◃τ) τ◃υ = ap□ σ◃σ₁⇒σ₂ (◃-trans □σ₁⇒□σ₂◃τ τ◃υ)

-- Need a helper lemma to potentially iterate ap□ in the RHS.  This makes sense since
-- we might need to apply pure;ap many times before getting an arrow type which we can then
-- combine with the arr on the LHS.
◃-trans-arr-ap□ τ₁◃σ₁ σ₂◃τ₂ rfl □υ₁⇒□υ₂◃υ = ap□ (arr τ₁◃σ₁ σ₂◃τ₂) □υ₁⇒□υ₂◃υ
◃-trans-arr-ap□ τ₁◃σ₁ σ₂◃τ₂ (arr υ₁◃τ₁ τ₂◃υ₂) □υ₁⇒□υ₂◃υ = ap□ (arr (◃-trans υ₁◃τ₁ τ₁◃σ₁) (◃-trans σ₂◃τ₂ τ₂◃υ₂)) □υ₁⇒□υ₂◃υ
◃-trans-arr-ap□ τ₁◃σ₁ σ₂◃τ₂ (ap□ τ₁⇒τ₂◃χ₁⇒χ₂ □χ₁⇒□χ₂◃υ₁⇒υ₂) □υ₁⇒□υ₂◃υ = ap□ (◃-trans-arr-ap□ τ₁◃σ₁ σ₂◃τ₂ τ₁⇒τ₂◃χ₁⇒χ₂ □χ₁⇒□χ₂◃υ₁⇒υ₂) □υ₁⇒□υ₂◃υ

-- applying an extra pure before doing something else...
◃-trans-pureL σ◃τ rfl = pure σ◃τ
◃-trans-pureL σ◃τ (box τ◃υ) = pure (◃-trans σ◃τ τ◃υ)
◃-trans-pureL σ◃τ (pure □τ◃υ) = pure (◃-trans-pureL σ◃τ □τ◃υ)
◃-trans-pureL σ◃τ (ap τ◃σ₁⇒σ₂ □σ₁⇒□σ₂◃υ) = ap□ (◃-trans σ◃τ τ◃σ₁⇒σ₂) □σ₁⇒□σ₂◃υ
◃-trans-pureL σ◃τ (ap□ τ◃σ₁⇒σ₂ □σ₁⇒□σ₂◃υ) = ap□ (◃-trans-pureL σ◃τ τ◃σ₁⇒σ₂) □σ₁⇒□σ₂◃υ

-- Now we can show that if σ <: τ then σ ◃ τ.  All the cases are
-- immediate except for transitivity, for which we use the previous
-- lemma.
<:→◃ : {σ τ : Ty} → σ <: τ → σ ◃ τ
<:→◃ rfl = rfl
<:→◃ (tr σ<:τ₁ τ₁<:τ) = ◃-trans (<:→◃ σ<:τ₁) (<:→◃ τ₁<:τ)
<:→◃ (arr τ₁<:σ₁ σ₂<:τ₂) = arr (<:→◃ τ₁<:σ₁) (<:→◃ σ₂<:τ₂)
<:→◃ (box σ<:τ) = box (<:→◃ σ<:τ)
<:→◃ pure = pure rfl
<:→◃ ap = ap rfl rfl

--------------------------------------------------
-- pureL is admissible
--------------------------------------------------

-- We went to a lot of trouble to get rid of pureL, but sometimes we
-- really want it!

pureL : {σ τ : Ty} → □ σ ◃ τ → σ ◃ τ
pureL rfl = pure rfl
pureL (box σ◃τ) = pure σ◃τ
pureL (pure □σ◃τ) = pure (pureL □σ◃τ)
pureL (ap f g) = ap□ f g
pureL (ap□ f g) = ap□ (pureL f) g

--------------------------------------------------
-- More lemmas about _◃_

◃→⟨⟩ : {σ τ : Ty} → σ ◃ τ → ⟨ σ ⟩ ≡ ⟨ τ ⟩
◃→⟨⟩ = <:→⟨⟩ ∘ ◃→<:

◃B-inv : {τ : Ty} {b : B} → τ ◃ base b → τ ≡ base b
◃B-inv = <:B-inv ∘ ◃→<:

B◃□-inv : {b : B} {τ : Ty} → base b ◃ □ τ → base b ◃ τ
B◃□-inv = <:→◃ ∘ B<:□-inv ∘ ◃→<:

¬B◃⇒ : {b : B} {τ₁ τ₂ : Ty} → ¬ (base b ◃ τ₁ ⇒ τ₂)
¬B◃⇒ = ¬B<:⇒ ∘ ◃→<:

¬⇒◃B : {b : B} {τ₁ τ₂ : Ty} → ¬ (τ₁ ⇒ τ₂ ◃ base b)
¬⇒◃B = ¬⇒<:B ∘ ◃→<:

¬□◃B : {τ : Ty} {b : B} → ¬ (□ τ ◃ base b)
¬□◃B = ¬□<:B ∘ ◃→<:

-- This inversion lemma is easy, because we don't have to worry
-- about transitivity! yippee!
⇒◃□-inv : {σ₁ σ₂ τ : Ty} → σ₁ ⇒ σ₂ ◃ □ τ → σ₁ ⇒ σ₂ ◃ τ
⇒◃□-inv (pure s) = s
⇒◃□-inv (ap□ f g) = ap□ f (⇒◃□-inv g)

-- This one is more difficult... but it would probably be super
-- impossible with transitivity in the mix.

-- This says when checking subtyping it is always OK to cancel boxes
-- from both sides.  Put another way, any proof of □ σ ◃ □ τ can be
-- rewritten to have 'box' as its outermost constructor. Put yet
-- another way, any term of type □ σ → □ τ can be rewritten to have
-- 'fmap' as its outermost function call.
□-inv : {σ τ : Ty} → □ σ ◃ □ τ → σ ◃ τ
□-inv rfl = rfl
□-inv (box p) = p
□-inv (pure p) = pureL p
□-inv (ap f g) = ◃-trans (ap□ f rfl) (⇒◃□-inv g)
□-inv (ap□ f g) = pureL (◃-trans (ap□ f rfl) (⇒◃□-inv g))

□◃⇒-inv : {σ τ₁ τ₂ : Ty} → □ σ ◃ τ₁ ⇒ τ₂ → Σ[ σ₁ ∈ Ty ] Σ[ σ₂ ∈ Ty ] (σ ◃ σ₁ ⇒ σ₂) × (□ σ₁ ⇒ □ σ₂ ◃ τ₁ ⇒ τ₂)
□◃⇒-inv (ap {σ₁ = σ₁} {σ₂ = σ₂} f g) = σ₁ , σ₂ , f , g
□◃⇒-inv (ap□ {σ₁ = σ₁} {σ₂ = σ₂} f g) = σ₁ , σ₂ , pureL f , g

--------------------------------------------------
-- BoxTrees

-- We can model types by binary trees with a natural number
-- (representing number of boxes) at each node, and base types at
-- leaves.

data BoxTreeNode : Set
data BoxTree : Set

data BoxTreeNode where
  base : B → BoxTreeNode
  _⇒_ : BoxTree → BoxTree → BoxTreeNode

data BoxTree where
  □⋆ : ℕ → BoxTreeNode → BoxTree

numBoxes : Ty → ℕ
numBoxes (base _) = 0
numBoxes (_ ⇒ _) = 0
numBoxes (□ τ) = suc (numBoxes τ)

Type→BoxTree : Ty → BoxTree
Type→BoxTreeNode : Ty → BoxTreeNode

Type→BoxTree τ = □⋆ (numBoxes τ) (Type→BoxTreeNode τ)

Type→BoxTreeNode (base b) = base b
Type→BoxTreeNode (σ ⇒ τ) = Type→BoxTree σ ⇒ Type→BoxTree τ
Type→BoxTreeNode (□ τ) = Type→BoxTreeNode τ

BoxTree→Type : BoxTree → Ty
BoxTreeNode→Type : BoxTreeNode → Ty

BoxTree→Type (□⋆ n t) = □^ n ∙ BoxTreeNode→Type t
BoxTreeNode→Type (base b) = base b
BoxTreeNode→Type (l ⇒ r) = BoxTree→Type l ⇒ BoxTree→Type r

Type→BoxTreeNode→Type : (τ : Ty) → □^ numBoxes τ ∙ BoxTreeNode→Type (Type→BoxTreeNode τ) ≡ τ
Type→BoxTree→Type : (τ : Ty) → BoxTree→Type (Type→BoxTree τ) ≡ τ

Type→BoxTreeNode→Type (base b) = refl
Type→BoxTreeNode→Type (σ ⇒ τ) = cong₂ _⇒_ (Type→BoxTree→Type σ) (Type→BoxTree→Type τ)
Type→BoxTreeNode→Type (□ τ) = cong □_ (Type→BoxTreeNode→Type τ)
Type→BoxTree→Type = Type→BoxTreeNode→Type

-- Individual subtyping transformations on BoxTrees

data _◂⁺_ : BoxTree → BoxTree → Set
data _◂⁻_ : BoxTree → BoxTree → Set

data _◂⁺_ where
  pure⁺ : {n : ℕ} {t : BoxTreeNode} → (□⋆ n t) ◂⁺ (□⋆ (suc n) t)
  ap⁺ : {n j k : ℕ} {l r : BoxTreeNode}
    → (□⋆ (suc n) (□⋆ j l ⇒ □⋆ k r)) ◂⁺ (□⋆ n (□⋆ (suc j) l ⇒ □⋆ (suc k) r))
  L⁺ : {n : ℕ} {l l′ r : BoxTree}
    → (l ◂⁻ l′) → (□⋆ n (l ⇒ r)) ◂⁺ (□⋆ n (l′ ⇒ r))
  R⁺ : {n : ℕ} {l r r′ : BoxTree}
    → (r ◂⁺ r′) → (□⋆ n (l ⇒ r)) ◂⁺ (□⋆ n (l ⇒ r′))

data _◂⁻_ where
  pure⁻ : {n : ℕ} {t : BoxTreeNode} → (□⋆ (suc n) t) ◂⁻ (□⋆ n t)
  ap⁻ : {n j k : ℕ} {l r : BoxTreeNode}
    → (□⋆ n (□⋆ (suc j) l ⇒ □⋆ (suc k) r)) ◂⁻ (□⋆ (suc n) (□⋆ j l ⇒ □⋆ k r))
  L⁻ : {n : ℕ} {l l′ r : BoxTree}
    → (l ◂⁺ l′) → (□⋆ n (l ⇒ r)) ◂⁻ (□⋆ n (l′ ⇒ r))
  R⁻ : {n : ℕ} {l r r′ : BoxTree}
    → (r ◂⁻ r′) → (□⋆ n (l ⇒ r)) ◂⁻ (□⋆ n (l ⇒ r′))

-- We actually need only a single _◂_ relation where we flip the
-- direction for negative positions.  The above version makes it
-- more clear that we can think in terms of just transforming one
-- tree, with the transformations allowed being opposite (adding vs
-- subtracting) at positive and negative nodes, but _◂_ is easier to
-- work with.

data _◂_ : BoxTree → BoxTree → Set where
  pure : {n : ℕ} {t : BoxTreeNode} → (□⋆ n t) ◂ (□⋆ (suc n) t)
  ap : {n j k : ℕ} {l r : BoxTreeNode}
    → (□⋆ (suc n) (□⋆ j l ⇒ □⋆ k r)) ◂ (□⋆ n (□⋆ (suc j) l ⇒ □⋆ (suc k) r))
  L : {n : ℕ} {l l′ r : BoxTree}
    → (l′ ◂ l) → (□⋆ n (l ⇒ r)) ◂ (□⋆ n (l′ ⇒ r))
  R : {n : ℕ} {l r r′ : BoxTree}
    → (r ◂ r′) → (□⋆ n (l ⇒ r)) ◂ (□⋆ n (l ⇒ r′))

◂→◂⁺ : {s t : BoxTree} → (s ◂ t) → (s ◂⁺ t)
◂→◂⁻ : {s t : BoxTree} → (s ◂ t) → (t ◂⁻ s)

◂→◂⁺ pure = pure⁺
◂→◂⁺ ap = ap⁺
◂→◂⁺ (L s◂t) = L⁺ (◂→◂⁻ s◂t)
◂→◂⁺ (R s◂t) = R⁺ (◂→◂⁺ s◂t)

◂→◂⁻ pure = pure⁻
◂→◂⁻ ap = ap⁻
◂→◂⁻ (L s◂t) = L⁻ (◂→◂⁺ s◂t)
◂→◂⁻ (R s◂t) = R⁻ (◂→◂⁻ s◂t)

◂⁺→◂ : {s t : BoxTree} → (s ◂⁺ t) → (s ◂ t)
◂⁻→◂ : {s t : BoxTree} → (s ◂⁻ t) → (t ◂ s)

◂⁺→◂ pure⁺ = pure
◂⁺→◂ ap⁺ = ap
◂⁺→◂ (L⁺ s◂⁻t) = L (◂⁻→◂ s◂⁻t)
◂⁺→◂ (R⁺ s◂⁺t) = R (◂⁺→◂ s◂⁺t)

◂⁻→◂ pure⁻ = pure
◂⁻→◂ ap⁻ = ap
◂⁻→◂ (L⁻ s◂⁺t) = L (◂⁺→◂ s◂⁺t)
◂⁻→◂ (R⁻ s◂⁻t) = R (◂⁻→◂ s◂⁻t)

-- Theorem: if the boxtrees for two types are related by ◂ , then
-- the first is a subtype of the second.

□^-<: : {n : ℕ} {σ τ : Ty} → σ <: τ → □^ n ∙ σ <: □^ n ∙ τ
□^-<: {zero} σ<:τ = σ<:τ
□^-<: {suc n} σ<:τ = box (□^-<: σ<:τ)

□□^n-assoc : (n : ℕ) (τ : Ty) → □ (□^ n ∙ τ) ≡ □^ n ∙ (□ τ)
□□^n-assoc zero _ = refl
□□^n-assoc (suc n) _ = cong □_ (□□^n-assoc n _)

◂→<: : {s t : BoxTree} → s ◂ t → BoxTree→Type s <: BoxTree→Type t

◂→<: pure = pure
◂→<: (ap {n} {j} {k} {l} {r})
  rewrite (□□^n-assoc n (□^ j ∙ BoxTreeNode→Type l ⇒ □^ k ∙ BoxTreeNode→Type r))
  = □^-<: ap
◂→<: (L l′◂l) = □^-<: (arr (◂→<: l′◂l) rfl)
◂→<: (R r◂r′) = □^-<: (arr rfl (◂→<: r◂r′))

-- Finally, we can chain together a bunch of transformations.

data _◂⋆_ : BoxTree → BoxTree → Set where
  rfl : {t : BoxTree} → t ◂⋆ t
  step : {s t u : BoxTree} → s ◂ t → t ◂⋆ u → s ◂⋆ u

_◂++_ : {s t u : BoxTree} → s ◂⋆ t → t ◂⋆ u → s ◂⋆ u
rfl ◂++ t◂u = t◂u
step stp s◂t ◂++ t◂u = step stp (s◂t ◂++ t◂u)

◂⋆→<: : {s t : BoxTree} → s ◂⋆ t → BoxTree→Type s <: BoxTree→Type t
◂⋆→<: rfl = rfl
◂⋆→<: (step s◂⁺t t◂⋆u) = tr (◂→<: s◂⁺t ) (◂⋆→<: t◂⋆u)

-- The other direction should be possible too (if σ <: τ then
-- Type→BoxTree σ ◂⋆ Type→BoxTree τ), but probably a lot more work
-- to prove. Is it worth it?  Would it help us come up with a
-- decision/inference algorithm?  Will need to think about it more.

-- Need to be able to distribute L⁺ / R⁺ etc. over an entire
-- ◂⋆-chain.  Maybe need to distinguish ◂⁺⋆ vs ◂⁻⋆ ?  Or maybe just
-- flip everything in the case of L⁺ ...

<:→◂⋆ : {σ τ : Ty} → σ <: τ → Type→BoxTree σ ◂⋆ Type→BoxTree τ
<:→◂⋆ rfl = rfl
<:→◂⋆ (tr σ<:τ τ<:υ) = (<:→◂⋆ σ<:τ) ◂++ (<:→◂⋆ τ<:υ)

-- Use ◂++ at the top level.  Distribute L⁺ / R⁺ over the IH
-- results.
<:→◂⋆ (arr τ₁<:σ₁ σ₂<:τ₂) = {!!}
<:→◂⋆ (box σ<:τ) = {!!}
<:→◂⋆ pure = step pure rfl
<:→◂⋆ ap = step ap rfl

--------------------------------------------------
-- Subtyping is decidable

◃-Dec : Decidable _◃_

-- First, some impossible cases.
◃-Dec (base _) (_ ⇒ _) = no ¬B◃⇒
◃-Dec (_ ⇒ _) (base _) = no ¬⇒◃B
◃-Dec (□ _) (base _) = no ¬□◃B

-- There's no subtyping among base types, so just check for equality.
◃-Dec (base b₁) (base b₂) with DecB b₁ b₂
... | no b₁≢b₂ = no (contraposition (base-inj ∘ ◃B-inv) b₁≢b₂)
... | yes b₁≡b₂ rewrite b₁≡b₂ = yes rfl

-- If there's a box on both sides, it's always OK to cancel them.
◃-Dec (□ σ) (□ τ) with ◃-Dec σ τ
... | no ¬σ◃τ = no (contraposition □-inv ¬σ◃τ)
... | yes σ◃τ = yes (box σ◃τ)

-- If there's a box only on the right, we can just use 'pure'.
◃-Dec (base b) (□ τ) with ◃-Dec (base b) τ
... | no ¬b◃τ = no (contraposition B◃□-inv ¬b◃τ)
... | yes b◃τ = yes (pure b◃τ)
◃-Dec (σ₁ ⇒ σ₂) (□ τ) with ◃-Dec (σ₁ ⇒ σ₂) τ  -- Just use pure for box on RHS
... | no ¬σ₁⇒σ₂◃τ = no (contraposition ⇒◃□-inv ¬σ₁⇒σ₂◃τ)
... | yes σ₁⇒σ₂◃τ = yes (pure σ₁⇒σ₂◃τ)

-- And now for the interesting cases, which of course involve
-- function types.

-- The only way to get this next case is to first push the box down,
-- i.e. the outermost constructor of any proof must be ap.  However,
-- we have to figure out σ₁ and σ₂.  They must be whatever is on the
-- LHS and RHS of σ (which must have a ⇒ shape), but with possibly
-- different numbers of □ ...
◃-Dec (□ σ) (τ₁ ⇒ τ₂) = {!!}

-- We might be tempted here to just check whether τ₁ ◃ σ₁ and σ₂ ◃
-- τ₂, and then use the 'arr' rule.  However, that would not be
-- correct; we might have to do some ap□ first (but we have to guess
-- how many...)  For example, (A → B) ◃ (□A → □B) (via pure + ap),
-- but □A ◃ A does not hold.
◃-Dec (σ₁ ⇒ σ₂) (τ₁ ⇒ τ₂) = {!!}

<:-Dec : Decidable _<:_
<:-Dec σ τ with ◃-Dec σ τ
... | no ¬σ◃τ = no λ σ<:τ → ¬σ◃τ (<:→◃ σ<:τ)
... | yes σ◃τ = yes (◃→<: σ◃τ)
