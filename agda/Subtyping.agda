open import Function using (_∘_)
open import Data.Bool hiding (_≤_)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product using (Σ-syntax ; _,_)
open import Data.Sum
open import Data.Product
open import Relation.Nullary.Negation
open import Relation.Nullary.Decidable using (yes ; no)
open import Data.Empty
open import Relation.Binary using (Decidable ; DecidableEquality)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality using (_≅_ ; refl) renaming (cong₂ to ≅cong₂)
open import Data.Maybe using (Maybe ; just ; nothing) renaming (map to mmap)

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

-- Subtypes have the same shape
<:→⌊⌋ : {σ τ : Ty} → σ <: τ → ⌊ σ ⌋ ≡ ⌊ τ ⌋
<:→⌊⌋ rfl = refl
<:→⌊⌋ (tr σ<:τ τ<:υ) = trans (<:→⌊⌋ σ<:τ) (<:→⌊⌋ τ<:υ)
<:→⌊⌋ (arr τ₁<:σ₁ σ₂<:τ₂) = cong₂ _⇒_ (sym (<:→⌊⌋ τ₁<:σ₁)) (<:→⌊⌋ σ₂<:τ₂)
<:→⌊⌋ (box σ<:τ) = <:→⌊⌋ σ<:τ
<:→⌊⌋ pure = refl
<:→⌊⌋ ap = refl

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

-- We can prove it the hard way:
-- pureL : {σ τ : Ty} → □ σ ◃ τ → σ ◃ τ
-- pureL rfl = pure rfl
-- pureL (box σ◃τ) = pure σ◃τ
-- pureL (pure □σ◃τ) = pure (pureL □σ◃τ)
-- pureL (ap f g) = ap□ f g
-- pureL (ap□ f g) = ap□ (pureL f) g

-- Or the easy way:
pureL : {σ τ : Ty} → □ σ ◃ τ → σ ◃ τ
pureL □σ◃τ = <:→◃ (tr pure (◃→<: □σ◃τ))

--------------------------------------------------
-- More lemmas about _◃_

◃→⟨⟩ : {σ τ : Ty} → σ ◃ τ → ⌊ σ ⌋ ≡ ⌊ τ ⌋
◃→⟨⟩ = <:→⌊⌋ ∘ ◃→<:

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

-- How about antisymmetry for subtyping?

-- ◃-antisym : σ ◃ τ → τ ◃ σ → σ ≡ τ
-- ◃-antisym rfl τ◃σ = refl
-- ◃-antisym (box σ◃τ) □τ◃□σ = cong □_ (◃-antisym σ◃τ (□-inv □τ◃□σ))
-- ◃-antisym (arr σ◃τ σ◃τ₁) rfl = refl
-- ◃-antisym (arr τ₁◃σ₁ σ₂◃τ₂) (arr σ₁◃τ₁ τ₂◃σ₂) = cong₂ _⇒_ (◃-antisym σ₁◃τ₁ τ₁◃σ₁) (◃-antisym σ₂◃τ₂ τ₂◃σ₂)
-- ◃-antisym (arr τ₁◃σ₁ σ₂◃τ₂) (ap□ τ₁⇒τ₂◃σ₃⇒σ₄ □σ₃⇒□σ₄◃σ₁⇒σ₂) = {!!}
-- ◃-antisym (pure σ◃τ) rfl = refl
-- ◃-antisym (pure σ◃τ) (box τ◃σ) = cong □_ {!!}
-- ◃-antisym (pure σ◃τ) (pure τ◃σ) = cong □_ {!!}
-- ◃-antisym (pure σ◃τ) (ap τ◃σ τ◃σ₁) = {!!}
-- ◃-antisym (pure σ◃τ) (ap□ τ◃σ τ◃σ₁) = {!!}
-- ◃-antisym (ap σ◃τ σ◃τ₁) rfl = refl
-- ◃-antisym (ap σ◃τ σ◃τ₁) (box τ◃σ) = cong □_ {!!}
-- ◃-antisym (ap σ◃τ σ◃τ₁) (pure τ◃σ) = {!!}
-- ◃-antisym (ap σ◃τ σ◃τ₁) (ap τ◃σ τ◃σ₁) = cong □_ {!!}
-- ◃-antisym (ap σ◃τ σ◃τ₁) (ap□ τ◃σ τ◃σ₁) = {!!}
-- ◃-antisym (ap□ σ◃τ σ◃τ₁) rfl = refl
-- ◃-antisym (ap□ σ◃τ σ◃τ₁) (box τ◃σ) = cong □_ {!!}
-- ◃-antisym (ap□ σ◃τ σ◃τ₁) (arr τ◃σ τ◃σ₁) = {!!}
-- ◃-antisym (ap□ σ◃τ σ◃τ₁) (pure τ◃σ) = {!!}
-- ◃-antisym (ap□ σ◃τ σ◃τ₁) (ap τ◃σ τ◃σ₁) = {!!}
-- ◃-antisym (ap□ σ◃τ σ◃τ₁) (ap□ τ◃σ τ◃σ₁) = {!!}

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
  _then_ : {s t u : BoxTree} → s ◂⋆ t → t ◂ u → s ◂⋆ u

cons : {s t u : BoxTree} → s ◂ t → t ◂⋆ u → s ◂⋆ u
cons s◂t rfl = rfl then s◂t
cons s◂t (t◂u then x) = cons s◂t t◂u then x

single : {s t : BoxTree} → s ◂ t → s ◂⋆ t
single s◂t = rfl then s◂t

-- Some helper/utility methods for dealing with ◂⋆ .

-- Append two transformation chains
_◂++_ : {s t u : BoxTree} → s ◂⋆ t → t ◂⋆ u → s ◂⋆ u
s ◂++ rfl = s
s ◂++ (t then x) = (s ◂++ t) then x

-- Lifting transformation chains to act on subtrees.

inc□ : {m n : ℕ} {s t : BoxTreeNode} → □⋆ m s ◂ □⋆ n t → □⋆ (suc m) s ◂ □⋆ (suc n) t
inc□ pure = pure
inc□ ap = ap
inc□ (L s◂t) = L s◂t
inc□ (R s◂t) = R s◂t

map□ : {m n : ℕ} {s t : BoxTreeNode} → □⋆ m s ◂⋆ □⋆ n t → □⋆ (suc m) s ◂⋆ □⋆ (suc n) t
map□ rfl = rfl
map□ (_then_ {t = □⋆ m t′} s◂t x) = map□ s◂t then inc□ x

mapR : {s t u : BoxTree} → s ◂⋆ t → □⋆ 0 (u ⇒ s) ◂⋆ □⋆ 0 (u ⇒ t)
mapR rfl = rfl
mapR (s◂t then x) = mapR s◂t then R x

mapL : {s t u : BoxTree} → s ◂⋆ t → □⋆ 0 (t ⇒ u) ◂⋆ □⋆ 0 (s ⇒ u)
mapL rfl = rfl
mapL (s◂t then x) = cons (L x) (mapL s◂t)

-- We can now prove that chained transformation ◂⋆ is equivalent to
-- subtyping.

-- First direction: if s ◂⋆t then their corresponding types are
-- subtypes.
◂⋆→<: : {s t : BoxTree} → s ◂⋆ t → BoxTree→Type s <: BoxTree→Type t
◂⋆→<: rfl = rfl
◂⋆→<: (s◂⋆t then t◂u) = tr (◂⋆→<: s◂⋆t ) (◂→<: t◂u)

-- And the other direction: if σ <: τ then Type→BoxTree σ ◂⋆
-- Type→BoxTree τ.
<:→◂⋆ : {σ τ : Ty} → σ <: τ → Type→BoxTree σ ◂⋆ Type→BoxTree τ
<:→◂⋆ rfl = rfl
<:→◂⋆ (tr σ<:τ τ<:υ) = (<:→◂⋆ σ<:τ) ◂++ (<:→◂⋆ τ<:υ)
<:→◂⋆ (arr τ₁<:σ₁ σ₂<:τ₂) = mapL (<:→◂⋆ τ₁<:σ₁) ◂++ mapR (<:→◂⋆ σ₂<:τ₂)
<:→◂⋆ (box σ<:τ) = map□ (<:→◂⋆ σ<:τ)
<:→◂⋆ pure = single pure
<:→◂⋆ ap = single ap

-- Not sure how/whether this helps us build a decision algorithm for
-- subtyping but at least it's good to know for certain that my
-- intuitive understanding of subtyping as tree transformations is
-- correct.

-- add□ : ℕ → BoxTree → BoxTree
-- add□ m (□⋆ n t) = □⋆ (m + n) t

-- pull□ : (m : ℕ) → (t : BoxTree) → Maybe (Σ[ t′ ∈ BoxTree ] (add□ m t′) ◂⋆ t)
-- pull□-BTN : (m : ℕ) → (t : BoxTreeNode) → Maybe (Σ[ t′ ∈ BoxTreeNode ] (□⋆ (suc m) t′ ◂⋆ □⋆ 0 t))

-- pull□ zero (□⋆ n t) = just (□⋆ n t , rfl)
-- pull□ (suc m) (□⋆ (suc n) t) with pull□ m (□⋆ n t)
-- ... | nothing = nothing
-- ... | just (□⋆ n′ t′ , prf) = just (□⋆ n′ t′ , map□ prf)
-- pull□ (suc m) (□⋆ zero t) with pull□-BTN m t
-- ... | nothing = nothing
-- ... | just (t′ , prf) = just (□⋆ 0 t′ , help m prf)
--   where
--     help : (m : ℕ) {t₁ t₂ : BoxTreeNode} → □⋆ (suc m) t₁ ◂⋆ □⋆ 0 t₂ → □⋆ (suc (m + 0)) t₁ ◂⋆ □⋆ 0 t₂
--     help m prf rewrite +-identityʳ m = prf

-- pull□-BTN _ (base _) = nothing
-- pull□-BTN m (s ⇒ t) with pull□ (suc m) t
-- ... | nothing = nothing
-- ... | just (□⋆ n t′ , prf) = just ((s ⇒ □⋆ n t′) , lemma m n prf)
--   where
--     lemma : (m n : ℕ) {s t : BoxTree} {t′ : BoxTreeNode} → □⋆ (suc (m + n)) t′ ◂⋆ t → □⋆ (suc m) (s ⇒ □⋆ n t′) ◂⋆ □⋆ 0 (s ⇒ t)
--     lemma zero n prf = {!!}
--     lemma (suc m) n prf = {!!}

-- ◂-SemiDec : (s t : BoxTree) → Maybe (s ◂⋆ t)
-- ◂-SemiDec-ℕ : (n : ℕ) → (s : BoxTreeNode) → (t : BoxTree) → Maybe (Σ[ r ∈ ℕ ] Σ[ k ∈ ℕ ] (r + k ≡ n) × (□⋆ k s ◂⋆ t))
-- ◂-SemiDec-BTN : (n : ℕ) → (s : BoxTreeNode) → (t : BoxTreeNode) → Maybe (Σ[ r ∈ ℕ ] Σ[ k ∈ ℕ ] (r + k ≡ n) × (□⋆ k s ◂⋆ □⋆ 0 t))
-- ◂-SemiDec-arr : (n : ℕ) → (s₁ s₂ t₁ t₂ : BoxTree) → Maybe (Σ[ r ∈ ℕ ] Σ[ k ∈ ℕ ] (r + k ≡ n) × (□⋆ k (s₁ ⇒ s₂) ◂⋆ □⋆ 0 (t₁ ⇒ t₂)))
-- ◂-SemiDec-arr-fixed : (n : ℕ) → (s₁ s₂ t₁ t₂ : BoxTree) → Maybe (□⋆ n (s₁ ⇒ s₂) ◂⋆ □⋆ 0 (t₁ ⇒ t₂))

-- ◂-SemiDec (□⋆ m s) t with ◂-SemiDec-ℕ m s t
-- ... | just (zero , _ , refl , □⋆ms◂⋆t) = just □⋆ms◂⋆t
-- ... | _ = nothing

-- ◂-SemiDec-ℕ (suc m) s (□⋆ (suc n) t) with ◂-SemiDec-ℕ m s (□⋆ n t)
-- ... | just (r , k , r+k≡m , □⋆ks◂⋆□⋆nt) = just (r , suc k , {!!} , (map□ □⋆ks◂⋆□⋆nt))
-- ... | nothing = nothing
-- ◂-SemiDec-ℕ zero s (□⋆ (suc n) t) with ◂-SemiDec-ℕ zero s (□⋆ n t)
-- ... | just (r , k , r+k≡m , □⋆ks◂⋆□⋆nt) = just (r , k , r+k≡m , (□⋆ks◂⋆□⋆nt then pure))
-- ... | nothing = nothing
-- ◂-SemiDec-ℕ m s (□⋆ 0 t) = ◂-SemiDec-BTN m s t

-- ◂-SemiDec-BTN n (base b₁) (base b₂) with DecB b₁ b₂
-- ... | no _ = nothing
-- ... | yes b₁≡b₂ rewrite b₁≡b₂ = just (n , 0 , {!!} , rfl)
-- ◂-SemiDec-BTN n (s₁ ⇒ s₂) (t₁ ⇒ t₂) = ◂-SemiDec-arr n s₁ s₂ t₁ t₂
-- ◂-SemiDec-BTN _ _ _ = nothing

-- ◂-SemiDec-arr zero s₁ s₂ t₁ t₂ with ◂-SemiDec-arr-fixed 0 s₁ s₂ t₁ t₂
-- ... | just prf = just (0 , 0 , refl , prf)
-- ... | nothing = nothing
-- ◂-SemiDec-arr (suc n) s₁ s₂ t₁ t₂ with ◂-SemiDec-arr-fixed (suc n) s₁ s₂ t₁ t₂ | ◂-SemiDec-arr n s₁ s₂ t₁ t₂
-- ... | just prf | _ = just (0 , suc n , refl , prf)
-- ... | nothing | just (r , k , r+k≡sn , prf) = just ( suc r , k , cong suc r+k≡sn , prf)
-- ... | nothing | nothing = nothing

-- ◂-SemiDec-arr-fixed n s₁ s₂ (□⋆ nt₁ t₁) t₂ with ◂-SemiDec-ℕ nt₁ t₁ (add□ n s₁)
-- ... | nothing = nothing
-- ... | just (_ , n₁ , eq , prf) with pull□ n₁ t₂
-- ...   | nothing = nothing
-- ...   | just (t₂′ , prf₂) = {!!}

--------------------------------------------------
-- Subtyping is decidable

-- ◃-Dec : Decidable _◃_

-- -- First, some impossible cases.
-- ◃-Dec (base _) (_ ⇒ _) = no ¬B◃⇒
-- ◃-Dec (_ ⇒ _) (base _) = no ¬⇒◃B
-- ◃-Dec (□ _) (base _) = no ¬□◃B

-- -- There's no subtyping among base types, so just check for equality.
-- ◃-Dec (base b₁) (base b₂) with DecB b₁ b₂
-- ... | no b₁≢b₂ = no (contraposition (base-inj ∘ ◃B-inv) b₁≢b₂)
-- ... | yes b₁≡b₂ rewrite b₁≡b₂ = yes rfl

-- -- If there's a box on both sides, it's always OK to cancel them.
-- ◃-Dec (□ σ) (□ τ) with ◃-Dec σ τ
-- ... | no ¬σ◃τ = no (contraposition □-inv ¬σ◃τ)
-- ... | yes σ◃τ = yes (box σ◃τ)

-- -- If there's a box only on the right, we can just use 'pure'.
-- ◃-Dec (base b) (□ τ) with ◃-Dec (base b) τ
-- ... | no ¬b◃τ = no (contraposition B◃□-inv ¬b◃τ)
-- ... | yes b◃τ = yes (pure b◃τ)
-- ◃-Dec (σ₁ ⇒ σ₂) (□ τ) with ◃-Dec (σ₁ ⇒ σ₂) τ  -- Just use pure for box on RHS
-- ... | no ¬σ₁⇒σ₂◃τ = no (contraposition ⇒◃□-inv ¬σ₁⇒σ₂◃τ)
-- ... | yes σ₁⇒σ₂◃τ = yes (pure σ₁⇒σ₂◃τ)

-- -- And now for the interesting cases, which of course involve
-- -- function types.

-- -- The only way to get this next case is to first push the box down,
-- -- i.e. the outermost constructor of any proof must be ap.  However,
-- -- we have to figure out σ₁ and σ₂.  They must be whatever is on the
-- -- LHS and RHS of σ (which must have a ⇒ shape), but with possibly
-- -- different numbers of □ ...
-- ◃-Dec (□ σ) (τ₁ ⇒ τ₂) = {!!}

-- -- We might be tempted here to just check whether τ₁ ◃ σ₁ and σ₂ ◃
-- -- τ₂, and then use the 'arr' rule.  However, that would not be
-- -- correct; we might have to do some ap□ first (but we have to guess
-- -- how many...)  For example, (A → B) ◃ (□A → □B) (via pure + ap),
-- -- but □A ◃ A does not hold.
-- ◃-Dec (σ₁ ⇒ σ₂) (τ₁ ⇒ τ₂) = {!!}

-- <:-Dec : Decidable _<:_
-- <:-Dec σ τ with ◃-Dec σ τ
-- ... | no ¬σ◃τ = no λ σ<:τ → ¬σ◃τ (<:→◃ σ<:τ)
-- ... | yes σ◃τ = yes (◃→<: σ◃τ)
