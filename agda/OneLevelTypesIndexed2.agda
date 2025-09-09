open import Data.Bool
open import Data.Empty
open import Data.Product using (Σ-syntax ; Σ ; _×_ ; _,_ ; -,_ ; proj₁ ; proj₂ )
open import Data.Product.Properties using (≡-dec)
open import Function using (_∘_)
open import Relation.Binary using (Decidable; DecidableEquality)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable using (yes; no; Dec)
open import Relation.Nullary.Negation.Core
open import Relation.Nullary.Negation

module OneLevelTypesIndexed2 (B : Set) (_≟B_ : DecidableEquality B) where

------------------------------------------------------------
-- Boxity
------------------------------------------------------------

data Boxity : Set where
  ₀ : Boxity
  ₁ : Boxity

variable b b₁ b₂ b₃ b₄ b₅ : Boxity

Boxity-≟ : DecidableEquality Boxity
Boxity-≟ ₀ ₀ = yes refl
Boxity-≟ ₀ ₁ = no λ ()
Boxity-≟ ₁ ₀ = no λ ()
Boxity-≟ ₁ ₁ = yes refl

------------------------------------------------------------
-- Path-dependent equality
------------------------------------------------------------

-- Based on https://martinescardo.github.io/dependent-equality-lecture/DependentEquality.html

_≡⟦_⟧_ : {A : Set} {B : A → Set} {a₀ a₁ : A}
       → B a₀ → a₀ ≡ a₁ → B a₁ → Set
b₀ ≡⟦ refl ⟧ b₁   =   b₀ ≡ b₁

undep : {A : Set} {B : A → Set} {a : A} {x y : B a} → _≡⟦_⟧_ {A} {B} x _ y → x ≡ y
undep p = p

------------------------------------------------------------
-- Types
------------------------------------------------------------

data Ty : Boxity → Set where
  □_ : Ty ₀ → Ty ₁
  base : B → Ty ₀
  _⇒_ : {b₁ b₂ : Boxity} → Ty b₁ → Ty b₂ → Ty ₀

infixr 2 _⇒_
infix 30 □_

□-inj : {τ₁ τ₂ : Ty ₀} → (□ τ₁ ≡ □ τ₂) → (τ₁ ≡ τ₂)
□-inj refl = refl

base-inj : {t₁ t₂ : B} → base t₁ ≡ base t₂ → t₁ ≡ t₂
base-inj refl = refl

⇒-inj : {σ₁ : Ty b₁} {σ₂ : Ty b₂} {τ₁ : Ty b₁} {τ₂ : Ty b₂} → (σ₁ ⇒ σ₂) ≡ (τ₁ ⇒ τ₂) → (σ₁ ≡ τ₁) × (σ₂ ≡ τ₂)
⇒-inj refl = refl , refl

------------------------------------------------------------
-- Type equality is decidable
------------------------------------------------------------

-- Boxity-heterogeneous decision principle, which decides equality of
-- boxities and types at the same time using a path-dependent equality
Ty-≟′ : (σ : Ty b₁) → (τ : Ty b₂) → Dec (Σ[ p ∈ b₁ ≡ b₂ ] _≡⟦_⟧_ {_} {Ty} σ p τ)
Ty-≟′ (□ σ) (□ τ) with Ty-≟′ σ τ
... | yes (refl , refl) = yes (refl , refl)
... | no σ≢τ = no λ { (refl , refl) → σ≢τ (refl , refl) }
Ty-≟′ (base S) (base T) with S ≟B T
... | yes refl = yes (refl , refl)
... | no S≢T = no λ { (refl , refl) → S≢T refl }
Ty-≟′ (_⇒_ {b₁} {b₂} σ₁ σ₂) (_⇒_ {b₃} {b₄} τ₁ τ₂) with Boxity-≟ b₁ b₃ | Boxity-≟ b₂ b₄ | Ty-≟′ σ₁ τ₁ | Ty-≟′ σ₂ τ₂
... | no b₁≢b₃ | _ | _ | _ = no λ { (refl , refl) → b₁≢b₃ refl }
... | yes _ | no b₂≢b₄ | _ | _ = no λ { (refl , refl) → b₂≢b₄ refl }
... | yes _ | yes _ | no σ₁≢τ₁ | _ = no λ { (refl , refl) → σ₁≢τ₁ (refl , refl) }
... | yes _ | yes _ | yes _ | no σ₂≢τ₂ = no λ { (refl , refl) → σ₂≢τ₂ (refl , refl) }
... | yes _ | yes _ | yes (refl , refl) | yes (refl , refl) = yes (refl , refl)
Ty-≟′ (□ _) (base _) = no λ ()
Ty-≟′ (□ _) (_ ⇒ _) = no λ ()
Ty-≟′ (base _) (□ _) = no λ ()
Ty-≟′ (base _) (_ ⇒ _) = no λ { (refl , ()) }
Ty-≟′ (_ ⇒ _) (□ _) = no λ ()
Ty-≟′ (_ ⇒ _) (base _) = no λ { (refl , ()) }

-- Boxity-homogeneous decision principle
Ty-≟ : DecidableEquality (Ty b)
Ty-≟ {b} σ τ with Ty-≟′ σ τ
... | no σ≢τ = no (λ σ≡τ → σ≢τ ( refl , σ≡τ))
... | yes (refl , σ≡τ) = yes σ≡τ

ΣTy-≟ : DecidableEquality (Σ Boxity Ty)
ΣTy-≟ (b₁ , σ) (b₂ , τ) with Ty-≟′ σ τ
... | no σ≢τ = no λ { refl → σ≢τ (refl , refl) }
... | yes (refl , refl) = yes refl

------------------------------------------------------------
-- Box erasure
------------------------------------------------------------

⌊_⌋ : Ty b → Ty ₀
⌊ □ τ ⌋ = ⌊ τ ⌋
⌊ base x ⌋ = base x
⌊ σ ⇒ τ ⌋ = ⌊ σ ⌋ ⇒ ⌊ τ ⌋

------------------------------------------------------------
-- Subtyping on one level indexed types
------------------------------------------------------------

data _<:_ : Ty b₁ → Ty b₂ → Set where
  rfl : ∀ {τ : Ty b} → τ <: τ
  tr : {σ : Ty b₁} {τ : Ty b₂} {υ : Ty b₃} → σ <: τ → τ <: υ → σ <: υ
  arr : {τ₁ : Ty b₁} {τ₂ : Ty b₂} {σ₁ : Ty b₃} {σ₂ : Ty b₄} → (τ₁ <: σ₁) → (σ₂ <: τ₂) → (σ₁ ⇒ σ₂) <: (τ₁ ⇒ τ₂)
  box : ∀ {σ τ} → (σ <: τ) → (□ σ <: □ τ)
  pure : ∀ {τ} → τ <: □ τ
  ap : ∀ {σ τ} → □ (σ ⇒ τ) <: (□ σ ⇒ □ τ)

infix 1 _<:_

--------------------------------------------------
-- Subtypes have the same shape

<:→⌊⌋ : {σ : Ty b₁} {τ : Ty b₂} → σ <: τ → ⌊ σ ⌋ ≡ ⌊ τ ⌋
<:→⌊⌋ rfl = refl
<:→⌊⌋ (tr σ<:τ τ<:υ) = trans (<:→⌊⌋ σ<:τ) (<:→⌊⌋ τ<:υ)
<:→⌊⌋ (arr τ₁<:σ₁ σ₂<:τ₂) = cong₂ _⇒_ (sym (<:→⌊⌋ τ₁<:σ₁)) (<:→⌊⌋ σ₂<:τ₂)
<:→⌊⌋ (box σ<:τ) = <:→⌊⌋ σ<:τ
<:→⌊⌋ pure = refl
<:→⌊⌋ ap = refl

------------------------------------------------------------
-- Transitivity-free subtyping
------------------------------------------------------------

infix 1 _◃_

data _◃_ : Ty b₁ → Ty b₂ → Set where
  rfl : {τ : Ty b} → τ ◃ τ
  box : {σ τ : Ty ₀} → (σ ◃ τ) → □ σ ◃ □ τ
  arr : {σ₁ : Ty b₁} {σ₂ : Ty b₂} {τ₁ : Ty b₃} {τ₂ : Ty b₄} → (τ₁ ◃ σ₁) → (σ₂ ◃ τ₂) → (σ₁ ⇒ σ₂ ◃ τ₁ ⇒ τ₂)
  pure : {σ : Ty b} {τ : Ty ₀} → (σ ◃ τ) → σ ◃ □ τ
  ap : {σ σ₁ σ₂ : Ty ₀} {τ : Ty b} → (σ ◃ σ₁ ⇒ σ₂) → (□ σ₁ ⇒ □ σ₂ ◃ τ) → (□ σ ◃ τ)
  ap□ : {σ : Ty b₁} {σ₁ σ₂ : Ty ₀} {τ : Ty b₂} → (σ ◃ σ₁ ⇒ σ₂) → (□ σ₁ ⇒ □ σ₂ ◃ τ) → (σ ◃ τ)

◃→<: : {σ : Ty b₁} {τ : Ty b₂} → σ ◃ τ → σ <: τ
◃→<: rfl = rfl
◃→<: (box σ◃τ) = box (◃→<: σ◃τ)
◃→<: (pure σ◃τ) = tr (◃→<: σ◃τ) pure
◃→<: (ap σ◃σ₁⇒σ₂ □σ₁⇒□σ₂◃τ) = tr (box (◃→<: σ◃σ₁⇒σ₂)) (tr ap (◃→<: □σ₁⇒□σ₂◃τ))
◃→<: (ap□ σ◃σ₁⇒σ₂ □σ₁⇒□σ₂◃τ) = tr (◃→<: σ◃σ₁⇒σ₂) (tr pure (tr ap (◃→<: □σ₁⇒□σ₂◃τ)))
◃→<: (arr σ◃τ₁ τ₁◃τ) = arr (◃→<: σ◃τ₁) (◃→<: τ₁◃τ)

◃-trans : {σ : Ty b₁} {τ : Ty b₂} {υ : Ty b₃} → σ ◃ τ → τ ◃ υ → σ ◃ υ
◃-trans-arr-ap□ : {τ₁ : Ty b₁} {τ₂ : Ty b₂} {σ₁ : Ty b₃} {σ₂ : Ty b₄} {υ₁ υ₂ : Ty ₀} {υ : Ty b₅} → τ₁ ◃ σ₁ → σ₂ ◃ τ₂ → (τ₁ ⇒ τ₂ ◃ υ₁ ⇒ υ₂) → (□ υ₁ ⇒ □ υ₂ ◃ υ) → σ₁ ⇒ σ₂ ◃ υ
◃-trans-pureL : {σ : Ty b₁} {τ : Ty ₀} {υ : Ty b₂} → σ ◃ τ → □ τ ◃ υ → σ ◃ υ

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
<:→◃ : {σ : Ty b₁} {τ : Ty b₂} → σ <: τ → σ ◃ τ
<:→◃ rfl = rfl
<:→◃ (tr σ<:τ₁ τ₁<:τ) = ◃-trans (<:→◃ σ<:τ₁) (<:→◃ τ₁<:τ)
<:→◃ (arr τ₁<:σ₁ σ₂<:τ₂) = arr (<:→◃ τ₁<:σ₁) (<:→◃ σ₂<:τ₂)
<:→◃ (box σ<:τ) = box (<:→◃ σ<:τ)
<:→◃ pure = pure rfl
<:→◃ ap = ap rfl rfl

-- pureL is admissible
pureL : {σ : Ty ₀} {τ : Ty b} → □ σ ◃ τ → σ ◃ τ
pureL □σ◃τ = <:→◃ (tr pure (◃→<: □σ◃τ))

------------------------------------------------------------
-- Inversion/impossibility lemmas
------------------------------------------------------------

¬B◃⇒ : {t : B} {τ₁ : Ty b₁} {τ₂ : Ty b₂} → ¬ (base t ◃ τ₁ ⇒ τ₂)
¬B◃⇒ (ap□ p _) = ¬B◃⇒ p

¬⇒◃B : {τ₁ : Ty b₁} {τ₂ : Ty b₂} {t : B} → ¬ (τ₁ ⇒ τ₂ ◃ base t)
¬⇒◃B (ap□ _ p) = ¬⇒◃B p

¬□◃B : {τ : Ty ₀} {t : B} → ¬ (□ τ ◃ base t)
¬□◃B (ap _ p) = ¬⇒◃B p
¬□◃B (ap□ _ p) = ¬⇒◃B p

-- If τ is a subtype of a base type, then in fact τ must be equal to
-- that base type (and its boxity must be 0).
◃B-inv : {τ : Ty b} {t : B} → τ ◃ base t → Σ[ p ∈ (b ≡ ₀) ] (_≡⟦_⟧_ {_} {Ty} τ p (base t))
◃B-inv rfl = refl , refl
◃B-inv (ap _ ⇒◃t) = ⊥-elim (¬⇒◃B ⇒◃t)
◃B-inv (ap□ _ ⇒◃t) = ⊥-elim (¬⇒◃B ⇒◃t)

-- Simpler version restricted to boxity-0 types
◃B-inv₀ : {τ : Ty ₀} {t : B} → τ ◃ base t → τ ≡ base t
◃B-inv₀ rfl = refl
◃B-inv₀ (ap□ _ ⇒◃t) = ⊥-elim (¬⇒◃B ⇒◃t)

B◃□-inv : {t : B} {τ : Ty ₀} → base t ◃ □ τ → base t ◃ τ
B◃□-inv (pure t◃□τ) = t◃□τ
B◃□-inv (ap□ t◃σ₁⇒σ₂ □σ₁⇒□σ₂◃□τ) = ⊥-elim (¬B◃⇒ t◃σ₁⇒σ₂)

-- This inversion lemma is easy, because we don't have to worry
-- about transitivity! yippee!
⇒◃□-inv : {σ₁ : Ty b₁} {σ₂ : Ty b₂} {τ : Ty ₀} → σ₁ ⇒ σ₂ ◃ □ τ → σ₁ ⇒ σ₂ ◃ τ
⇒◃□-inv (pure s) = s
⇒◃□-inv (ap□ f g) = ap□ f (⇒◃□-inv g)

-- This one is more difficult... but it would probably be super
-- impossible with transitivity in the mix.

-- This says when checking subtyping it is always OK to cancel boxes
-- from both sides.  Put another way, any proof of □ σ ◃ □ τ can be
-- rewritten to have 'box' as its outermost constructor. Put yet
-- another way, any term of type □ σ → □ τ can be rewritten to have
-- 'fmap' as its outermost function call.
□-inv : {σ τ : Ty ₀} → □ σ ◃ □ τ → σ ◃ τ
□-inv rfl = rfl
□-inv (box p) = p
□-inv (pure p) = pureL p
□-inv (ap f g) = ◃-trans (ap□ f rfl) (⇒◃□-inv g)
□-inv (ap□ f g) = pureL (◃-trans (ap□ f rfl) (⇒◃□-inv g))

------------------------------------------------------------
-- Subtyping is decidable
------------------------------------------------------------

◃-Dec : {b₁ b₂ : Boxity} → Decidable (_◃_ {b₁} {b₂})

-- First, some impossible cases.
◃-Dec (base _) (_ ⇒ _) = no ¬B◃⇒
◃-Dec (_ ⇒ _) (base _) = no ¬⇒◃B
◃-Dec (□ _) (base _) = no ¬□◃B

-- There's no subtyping among base types, so just check for equality.
◃-Dec (base t₁) (base t₂) with t₁ ≟B t₂
... | no t₁≢t₂ = no (contraposition (base-inj ∘ ◃B-inv₀) t₁≢t₂)
... | yes t₁≡t₂ rewrite t₁≡t₂ = yes rfl

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
