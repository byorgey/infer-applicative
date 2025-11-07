open import Data.Bool
open import Data.Empty
open import Data.Product using (Σ-syntax ; Σ ; _×_ ; _,_ ; -,_ ; proj₁ ; proj₂ )
open import Data.Product.Properties using (≡-dec)
open import Data.Sum using (_⊎_; inj₁; inj₂)
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

-- There are only two Boxities, so if it's not ₀, it must be ₁
¬₀→₁ : {b : Boxity} → b ≢ ₀ → b ≡ ₁
¬₀→₁ {₀} b≢₀ = ⊥-elim (b≢₀ refl)
¬₀→₁ {₁} b≢₀ = refl

------------------------------------------------------------
-- Path-dependent equality
------------------------------------------------------------

-- Based on https://martinescardo.github.io/dependent-equality-lecture/DependentEquality.html

_≡⟦_⟧_ : {A : Set} {B : A → Set} {a₀ a₁ : A}
       → B a₀ → a₀ ≡ a₁ → B a₁ → Set
b₀ ≡⟦ refl ⟧ b₁   =   b₀ ≡ b₁

------------------------------------------------------------
-- Types
------------------------------------------------------------

data Ty : Boxity → Set where
  □_ : Ty ₀ → Ty ₁
  base : B → Ty ₀
  _⇒_ : {b₁ b₂ : Boxity} → Ty b₁ → Ty b₂ → Ty ₀

infixr 25 _⇒_
infix 30 □_

□′ : (b ≡ ₀) → Ty b → Ty ₁
□′ refl σ = □ σ

□-inj : {τ₁ τ₂ : Ty ₀} → (□ τ₁ ≡ □ τ₂) → (τ₁ ≡ τ₂)
□-inj refl = refl

base-inj : {t₁ t₂ : B} → base t₁ ≡ base t₂ → t₁ ≡ t₂
base-inj refl = refl

⇒-inj : {σ₁ : Ty b₁} {σ₂ : Ty b₂} {τ₁ : Ty b₁} {τ₂ : Ty b₂} → (σ₁ ⇒ σ₂) ≡ (τ₁ ⇒ τ₂) → (σ₁ ≡ τ₁) × (σ₂ ≡ τ₂)
⇒-inj refl = refl , refl

decompose-□ : (σ : Ty ₁) → Σ[ σ′ ∈ Ty ₀ ] (σ ≡ □ σ′)
decompose-□ (□ σ) = σ , refl

case-□ : (σ : Ty b) → (b ≡ ₀) ⊎ (b ≡ ₁)
case-□ (□ _) = inj₂ refl
case-□ (base _) = inj₁ refl
case-□ (_ ⇒ _) = inj₁ refl

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

ΣTy : Set
ΣTy = Σ Boxity Ty

%_ : Ty b → ΣTy
% τ = _ , τ

ΣTy-≟ : DecidableEquality ΣTy
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

infix 20 _<:_

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

infix 20 _◃_

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

¬□B◃⇒ : {t : B} {τ₁ : Ty b₁} {τ₂ : Ty b₂} → ¬ (□ base t ◃ τ₁ ⇒ τ₂)
¬□B◃⇒ (ap p _) = ⊥-elim (¬B◃⇒ p)
¬□B◃⇒ (ap□ p _) = ¬□B◃⇒ p

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

-- If a type with no outermost box is a subtype of a type with an
-- outermost box, we can remove the box.
unbox : {σ τ : Ty ₀} → σ ◃ □ τ → σ ◃ τ
unbox (pure σ◃τ) = σ◃τ
unbox (ap□ σ◃σ₁⇒σ₂ □σ₁⇒□σ₂◃□τ) = ap□ σ◃σ₁⇒σ₂ (unbox □σ₁⇒□σ₂◃□τ)

------------------------------------------------------------
-- Inversion lemmas for arrow types
------------------------------------------------------------

-- If two arrow types are in the ◃ relation, then their right-hand
-- arguments are in the ◃ relation as well.
⇒-invʳ : {σ₁ : Ty b₁} {σ₂ : Ty b₂} {τ₁ : Ty b₃} {τ₂ : Ty b₄} → (σ₁ ⇒ σ₂) ◃ (τ₁ ⇒ τ₂) → σ₂ ◃ τ₂
⇒-invʳ rfl = rfl
⇒-invʳ (arr _ pf) = pf
⇒-invʳ {σ₂ = σ₂} (ap□ pf₁ pf₂) = ◃-trans (⇒-invʳ pf₁) (◃-trans (pure rfl) (⇒-invʳ pf₂))

-- The same is not true (neither co- nor contravariantly) for
-- the left-hand arguments.  For example, (A ⇒ A) ◃ (□A ⇒ □A) (via
-- pure + app), and also (□A ⇒ A) ◃ (A ⇒ □A) (via arr).
--
-- However, we can at least say that they are contravariantly related
-- with either zero or one boxes applied.
--
-- XXX CAN WE ADAPT THIS TO THE GENERAL CASE by proving a similar
-- lemma, but instead of a sum type we have something like ∃n. τ₁ ◃ □^n σ₁ ?
-- ⇒-invˡ : {σ₁ : Ty b₁} {σ₂ : Ty b₂} {τ₁ : Ty b₃} {τ₂ : Ty b₄} → (σ₁ ⇒ σ₂) ◃ (τ₁ ⇒ τ₂) → (τ₁ ◃ σ₁ ⊎ (Σ (b₁ ≡ ₀) (λ p → τ₁ ◃ □′ p σ₁)))
-- ⇒-invˡ rfl = inj₁ rfl
-- ⇒-invˡ (arr τ₁◃σ₁ _) = inj₁ τ₁◃σ₁
-- ⇒-invˡ {b₁ = ₁} {σ₁ = □ σ₁} (ap□ σ₁⇒σ₂◃σ₃⇒σ₄ □σ₃⇒□σ₄◃τ₁⇒τ₂) with ⇒-invˡ □σ₃⇒□σ₄◃τ₁⇒τ₂ | ⇒-invˡ σ₁⇒σ₂◃σ₃⇒σ₄
-- ... | inj₁ τ₁◃□σ₃ | inj₁ σ₃◃σ₁ = inj₁ (◃-trans τ₁◃□σ₃ (box (unbox σ₃◃σ₁)))
-- ⇒-invˡ {b₁ = ₀} (ap□ σ₁⇒σ₂◃σ₃⇒σ₄ □σ₃⇒□σ₄◃τ₁⇒τ₂) with ⇒-invˡ □σ₃⇒□σ₄◃τ₁⇒τ₂ | ⇒-invˡ σ₁⇒σ₂◃σ₃⇒σ₄
-- ... | inj₁ τ₁◃□σ₃ | inj₁ σ₃◃σ₁ = inj₂ (refl , ◃-trans τ₁◃□σ₃ (box σ₃◃σ₁))
-- ... | inj₁ τ₁◃□σ₃ | inj₂ (refl , σ₃◃□σ₁) = inj₂ (refl , ◃-trans τ₁◃□σ₃ (box (unbox σ₃◃□σ₁)))

⇒-invˡ : {σ₁ : Ty b₁} {σ₂ : Ty b₂} {τ₁ : Ty b₃} {τ₂ : Ty b₄} → (σ₁ ⇒ σ₂) ◃ (τ₁ ⇒ τ₂) → (τ₁ ◃ σ₁) ⊎ Σ[ p ∈ b₁ ≡ ₀ ] (τ₁ ◃ □′ p σ₁) × Σ[ q ∈ b₂ ≡ ₀ ] (□′ q σ₂ ◃ τ₂)
⇒-invˡ rfl = inj₁ rfl
⇒-invˡ (arr τ₁◃σ₁ _) = inj₁ τ₁◃σ₁
⇒-invˡ (ap□ σ₁⇒σ₂◃σ₃⇒σ₄ □σ₃⇒□σ₄◃τ₁⇒τ₂) = {!!}

-- ⇒-invˡ rfl = inj₁ rfl
-- ⇒-invˡ (arr τ₁◃σ₁ _) = inj₁ τ₁◃σ₁
-- ⇒-invˡ {b₁ = ₁} {σ₁ = □ σ₁} (ap□ σ₁⇒σ₂◃σ₃⇒σ₄ □σ₃⇒□σ₄◃τ₁⇒τ₂) with ⇒-invˡ □σ₃⇒□σ₄◃τ₁⇒τ₂ | ⇒-invˡ σ₁⇒σ₂◃σ₃⇒σ₄
-- ... | inj₁ τ₁◃□σ₃ | inj₁ σ₃◃σ₁ = inj₁ (◃-trans τ₁◃□σ₃ (box (unbox σ₃◃σ₁)))
-- ⇒-invˡ {b₁ = ₀} (ap□ σ₁⇒σ₂◃σ₃⇒σ₄ □σ₃⇒□σ₄◃τ₁⇒τ₂) with ⇒-invˡ □σ₃⇒□σ₄◃τ₁⇒τ₂ | ⇒-invˡ σ₁⇒σ₂◃σ₃⇒σ₄
-- ... | inj₁ τ₁◃□σ₃ | inj₁ σ₃◃σ₁ = inj₂ (refl , ◃-trans τ₁◃□σ₃ (box σ₃◃σ₁))
-- ... | inj₁ τ₁◃□σ₃ | inj₂ (refl , σ₃◃□σ₁) = inj₂ (refl , ◃-trans τ₁◃□σ₃ (box (unbox σ₃◃□σ₁)))

------------------------------------------------------------
-- Lemma: ¬A × ¬B → ¬ (A ⊎ B
------------------------------------------------------------

lem₁ : {P Q : Set} → (¬ P × ¬ Q) → ¬ (P ⊎ Q)
lem₁ (¬P , ¬Q) (inj₁ P) = ¬P P
lem₁ (¬P , ¬Q) (inj₂ Q) = ¬Q Q

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

-- If a box type is a subtype of a function type, the type inside the
-- box can't be a base type...
◃-Dec (□ base _) (_ ⇒ _) = no ¬□B◃⇒

-- ...in fact, it must be a function type itself.  The only way to get
-- this case is to first push the box down, i.e. the outermost
-- constructor of any proof must be ap or ap□.
--
-- However, we have to figure out σ₁ and σ₂.  They must be related to
-- whatever is on the LHS and RHS of σ (which must have a ⇒ shape),
-- but potentially with boxes pushed around.

-- Only rules we could possibly use here are ap or ap□.
--
--   To use ap, we must show
--     - (σ₁ ⇒ σ₂) ◃ x ⇒ y
--     - □ x ⇒ □ y ◃ τ₁ ⇒ τ₂
--   To use ap□, we must show
--     - □ (σ₁ ⇒ σ₂) ◃ x ⇒ y
--     - □ x ⇒ □ y ◃ τ₁ ⇒ τ₂
--
--   What can we say about the boxity of various things here?
--   I want to say σ₁ must have boxity 0...
--
--   Note we must have  □ σ₂ ◃ τ₂ ?
--
◃-Dec (□ (σ₁ ⇒ σ₂)) (τ₁ ⇒ τ₂) = {!!}

-- Finally, the case for two function types.  We might be tempted here
-- to just check whether τ₁ ◃ σ₁ and σ₂ ◃ τ₂, and then use the 'arr'
-- rule.  However, that would not be complete; we might have to do an
-- ap□ first.  For example, (A → B) ◃ (□A → □B) (via pure + ap), but
-- □A ◃ A does not hold.

-- ◃-Dec (σ₁ ⇒ σ₂) (τ₁ ⇒ τ₂) with case-□ σ₁
-- ◃-Dec (σ₁ ⇒ σ₂) (τ₁ ⇒ τ₂) | inj₁ refl with ◃-Dec σ₂ τ₂ | ◃-Dec τ₁ σ₁ | ◃-Dec τ₁ (□ σ₁)
-- ◃-Dec (σ₁ ⇒ σ₂) (τ₁ ⇒ τ₂) | inj₁ refl | no ¬σ₂◃τ₂ | _ | _ = no (contraposition ⇒-invʳ ¬σ₂◃τ₂)
-- ◃-Dec (σ₁ ⇒ σ₂) (τ₁ ⇒ τ₂) | inj₁ refl | yes σ₂◃τ₂ | yes τ₁◃σ₁ | _ = yes (arr τ₁◃σ₁ σ₂◃τ₂)
-- ◃-Dec (σ₁ ⇒ σ₂) (τ₁ ⇒ τ₂) | inj₁ refl | yes σ₂◃τ₂ | no ¬τ₁◃σ₁ | yes τ₁◃□σ₁ = yes {!!}
-- ◃-Dec (σ₁ ⇒ σ₂) (τ₁ ⇒ τ₂) | inj₁ refl | yes σ₂◃τ₂ | no ¬τ₁◃σ₁ | no ¬τ₁◃□σ₁ = no (contraposition ⇒-invˡ (lem₁ (¬τ₁◃σ₁ , (λ { (refl , τ₁◃□σ₁) → ¬τ₁◃□σ₁ τ₁◃□σ₁}))))
-- ◃-Dec (σ₁ ⇒ σ₂) (τ₁ ⇒ τ₂) | inj₂ refl with ◃-Dec σ₂ τ₂ | ◃-Dec τ₁ σ₁
-- ◃-Dec (σ₁ ⇒ σ₂) (τ₁ ⇒ τ₂) | inj₂ refl | no ¬σ₂◃τ₂ | _ = no (contraposition ⇒-invʳ ¬σ₂◃τ₂)
-- ◃-Dec (σ₁ ⇒ σ₂) (τ₁ ⇒ τ₂) | inj₂ refl | yes σ₂◃τ₂ | yes τ₁◃σ₁ = yes (arr τ₁◃σ₁ σ₂◃τ₂)
-- ◃-Dec (σ₁ ⇒ σ₂) (τ₁ ⇒ τ₂) | inj₂ refl | yes σ₂◃τ₂ | no ¬τ₁◃σ₁ = no (contraposition ⇒-invˡ (lem₁ (¬τ₁◃σ₁ , λ {()})))

------------------------------------------------------------
-- Typing + coercion elaboration
------------------------------------------------------------

data Ctx : Set where
  ∅ : Ctx
  _,_ : Ctx → ΣTy → Ctx

infixr 4 _,_

variable
  Γ : Ctx

-- Approach to variables + weakening taken from
-- Keller + Alternkirch, "Normalization by hereditary substitutions"
-- https://www.cs.nott.ac.uk/~psztxa/publ/msfp10.pdf
data Var : Ctx → ΣTy → Set₁ where
  vz : {τ : ΣTy} → Var (Γ , τ) τ
  vs : {σ τ : ΣTy} → Var Γ τ → Var (Γ , σ) τ

_-_ : {σ : ΣTy} → (Γ : Ctx) → Var Γ σ → Ctx
∅ - ()
(Γ , _) - vz = Γ
(Γ , x) - vs v = (Γ - v) , x

wkv : {σ τ : ΣTy}  → (x : Var Γ σ) → Var (Γ - x) τ → Var Γ τ
wkv vz y = vs y
wkv (vs x) vz = vz
wkv (vs x) (vs y) = vs (wkv x y)

module TypingJudgment where

  -- Type-indexed terms, with applicative subtyping
  data Term : Ctx → Ty b → Set₁ where
    sub : {σ : Ty b₁} {τ : Ty b₂} → σ <: τ → Term Γ σ → Term Γ τ
    var : {τ : Ty b} → Var Γ (% τ) → Term Γ τ
    ƛ : {σ : Ty b₁} {τ : Ty b₂} → Term (Γ , % σ) τ → Term Γ (σ ⇒ τ)
    _∙_ : {σ : Ty b₁} {τ : Ty b₂} → Term Γ (σ ⇒ τ) → Term Γ σ → Term Γ τ

  -- Type-indexed terms extended with extra `pure` and `ap` constants
  data Term□ : Ctx → Ty b → Set₁ where
    var : {τ : Ty b} → Var Γ (% τ) → Term□ Γ τ
--     ƛ : Term□ (Γ , σ) τ → Term□ Γ (σ ⇒ τ)
--     _∙_ : Term□ Γ (σ ⇒ τ) → Term□ Γ σ → Term□ Γ τ
--     con : (c : C) → Term□ Γ (Cty c)
--     pure : Term□ Γ (τ ⇒ □ τ)
--     ap : Term□ Γ (□ (σ ⇒ τ) ⇒ (□ σ ⇒ □ τ))

--   -- Weakening for terms.  Needed for arr case of coercion insertion.
--   wk : (x : Var Γ σ) → Term□ (Γ - x) τ → Term□ Γ τ
--   wk x (var y) = var (wkv x y)
--   wk x (ƛ t) = ƛ (wk (vs x) t)
--   wk x (t₁ ∙ t₂) = wk x t₁ ∙ wk x t₂
--   wk _ (con c) = con c
--   wk _ pure = pure
--   wk _ ap = ap

--   -- Coercion insertion
--   -- Should definitely present these rules in the paper!

--   infixr 5 _≪_

--   _≪_ : σ <: τ → Term□ Γ σ → Term□ Γ τ
--   rfl ≪ t = t
--   tr σ<:τ τ<:υ ≪ t = τ<:υ ≪ σ<:τ ≪ t
--   -- η-expand at function types to apply the coercions --- could optimize this part
--   -- of course, especially if t is syntactically a lambda already
--   arr τ₁<:σ₁ σ₂<:τ₂ ≪ t = ƛ (σ₂<:τ₂ ≪ (wk vz t ∙ (τ₁<:σ₁ ≪ var vz)))
--   -- -- essentially 'fmap coerce'
--   box σ<:τ ≪ t = (ap ∙ (pure ∙ ƛ (σ<:τ ≪ var vz))) ∙ t
--   pure ≪ t = pure ∙ t
--   ap ≪ t = ap ∙ t

--   elaborate : Term Γ τ → Term□ Γ τ
--   elaborate (sub σ<:τ t) = σ<:τ ≪ elaborate t
--   elaborate (var i) = var i
--   elaborate (ƛ _ s) = ƛ (elaborate s)
--   elaborate (t₁ ∙ t₂) = elaborate t₁ ∙ elaborate t₂
--   elaborate (con c) = con c
