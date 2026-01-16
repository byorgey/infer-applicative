open import Data.Bool
open import Data.Nat
open import Data.Fin using (Fin ; punchIn)
open import Data.Fin.Properties using (suc-injective)
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

module OneLevelTypesIndexed2 (Base : Set) (_≟B_ : DecidableEquality Base) where

variable n : ℕ
variable B B₁ B₂ : Base

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
  base : Base → Ty ₀
  _⇒_ : {b₁ b₂ : Boxity} → Ty b₁ → Ty b₂ → Ty ₀

variable
  σ τ υ σ₁ σ₂ τ₁ τ₂ υ₁ υ₂ : Ty b

infixr 25 _⇒_
infix 30 □_

□′ : (b ≡ ₀) → Ty b → Ty ₁
□′ refl σ = □ σ

□-inj : (□ τ₁ ≡ □ τ₂) → (τ₁ ≡ τ₂)
□-inj refl = refl

base-inj : base B₁ ≡ base B₂ → B₁ ≡ B₂
base-inj refl = refl

⇒-inj : (σ₁ ⇒ σ₂) ≡ (τ₁ ⇒ τ₂) → (σ₁ ≡ τ₁) × (σ₂ ≡ τ₂)
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

_Σ⇒_ : ΣTy → ΣTy → ΣTy
(_ , σ) Σ⇒ (_ , τ) = _ , (σ ⇒ τ)

ΣTy-≟ : DecidableEquality ΣTy
ΣTy-≟ (b₁ , σ) (b₂ , τ) with Ty-≟′ σ τ
... | no σ≢τ = no λ { refl → σ≢τ (refl , refl) }
... | yes (refl , refl) = yes refl

variable
  σ′ τ′ : ΣTy

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
  rfl : τ <: τ
  tr : σ <: τ → τ <: υ → σ <: υ
  arr : (τ₁ <: σ₁) → (σ₂ <: τ₂) → (σ₁ ⇒ σ₂) <: (τ₁ ⇒ τ₂)
  box : (σ <: τ) → (□ σ <: □ τ)
  pure : τ <: □ τ
  ap : □ (σ ⇒ τ) <: (□ σ ⇒ □ τ)

infix 20 _<:_

--------------------------------------------------
-- Subtypes have the same shape

<:→⌊⌋ : σ <: τ → ⌊ σ ⌋ ≡ ⌊ τ ⌋
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
  rfl : τ ◃ τ
  box : (σ ◃ τ) → □ σ ◃ □ τ
  arr : (τ₁ ◃ σ₁) → (σ₂ ◃ τ₂) → (σ₁ ⇒ σ₂ ◃ τ₁ ⇒ τ₂)
  pure : (σ ◃ τ) → σ ◃ □ τ
  ap : (σ ◃ σ₁ ⇒ σ₂) → (□ σ₁ ⇒ □ σ₂ ◃ τ) → (□ σ ◃ τ)
  ap□ : (σ ◃ σ₁ ⇒ σ₂) → (□ σ₁ ⇒ □ σ₂ ◃ τ) → (σ ◃ τ)

◃→<: : σ ◃ τ → σ <: τ
◃→<: rfl = rfl
◃→<: (box σ◃τ) = box (◃→<: σ◃τ)
◃→<: (pure σ◃τ) = tr (◃→<: σ◃τ) pure
◃→<: (ap σ◃σ₁⇒σ₂ □σ₁⇒□σ₂◃τ) = tr (box (◃→<: σ◃σ₁⇒σ₂)) (tr ap (◃→<: □σ₁⇒□σ₂◃τ))
◃→<: (ap□ σ◃σ₁⇒σ₂ □σ₁⇒□σ₂◃τ) = tr (◃→<: σ◃σ₁⇒σ₂) (tr pure (tr ap (◃→<: □σ₁⇒□σ₂◃τ)))
◃→<: (arr σ◃τ₁ τ₁◃τ) = arr (◃→<: σ◃τ₁) (◃→<: τ₁◃τ)

◃-trans : σ ◃ τ → τ ◃ υ → σ ◃ υ
◃-trans-arr-ap□ : τ₁ ◃ σ₁ → σ₂ ◃ τ₂ → (τ₁ ⇒ τ₂ ◃ υ₁ ⇒ υ₂) → (□ υ₁ ⇒ □ υ₂ ◃ υ) → σ₁ ⇒ σ₂ ◃ υ
◃-trans-pureL : σ ◃ τ → □ τ ◃ υ → σ ◃ υ

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
<:→◃ : σ <: τ → σ ◃ τ
<:→◃ rfl = rfl
<:→◃ (tr σ<:τ₁ τ₁<:τ) = ◃-trans (<:→◃ σ<:τ₁) (<:→◃ τ₁<:τ)
<:→◃ (arr τ₁<:σ₁ σ₂<:τ₂) = arr (<:→◃ τ₁<:σ₁) (<:→◃ σ₂<:τ₂)
<:→◃ (box σ<:τ) = box (<:→◃ σ<:τ)
<:→◃ pure = pure rfl
<:→◃ ap = ap rfl rfl

-- pureL is admissible
pureL : □ σ ◃ τ → σ ◃ τ
pureL □σ◃τ = <:→◃ (tr pure (◃→<: □σ◃τ))

-- Transitivity with an extra box when we know the result must have a box
◃-trans₁ : {υ : Ty ₁} → (σ ◃ □ τ) → (τ ◃ υ) → σ ◃ υ
◃-trans₁ σ◃□τ₁ (pure τ₁◃τ) = ◃-trans σ◃□τ₁ (box τ₁◃τ)
◃-trans₁ σ◃□τ (ap□ τ◃σ₁⇒σ₂ □σ₁⇒□σ₂◃υ) = ◃-trans σ◃□τ (ap τ◃σ₁⇒σ₂ □σ₁⇒□σ₂◃υ)

------------------------------------------------------------
-- Inversion/impossibility lemmas
------------------------------------------------------------

¬B◃⇒ : ¬ (base B ◃ τ₁ ⇒ τ₂)
¬B◃⇒ (ap□ p _) = ¬B◃⇒ p

¬□B◃⇒ : ¬ (□ base B ◃ τ₁ ⇒ τ₂)
¬□B◃⇒ (ap p _) = ⊥-elim (¬B◃⇒ p)
¬□B◃⇒ (ap□ p _) = ¬□B◃⇒ p

¬⇒◃B : ¬ (τ₁ ⇒ τ₂ ◃ base B)
¬⇒◃B (ap□ _ p) = ¬⇒◃B p

¬□◃B : ¬ (□ τ ◃ base B)
¬□◃B (ap _ p) = ¬⇒◃B p
¬□◃B (ap□ _ p) = ¬⇒◃B p

-- If τ is a subtype of a base type, then in fact τ must be equal to
-- that base type (and its boxity must be 0).
◃B-inv : τ ◃ base B → Σ[ p ∈ (b ≡ ₀) ] (_≡⟦_⟧_ {_} {Ty} τ p (base B))
◃B-inv rfl = refl , refl
◃B-inv (ap _ ⇒◃t) = ⊥-elim (¬⇒◃B ⇒◃t)
◃B-inv (ap□ _ ⇒◃t) = ⊥-elim (¬⇒◃B ⇒◃t)

-- Simpler version restricted to boxity-0 types
◃B-inv₀ : τ ◃ base B → τ ≡ base B
◃B-inv₀ rfl = refl
◃B-inv₀ (ap□ _ ⇒◃t) = ⊥-elim (¬⇒◃B ⇒◃t)

B◃□-inv : base B ◃ □ τ → base B ◃ τ
B◃□-inv (pure t◃□τ) = t◃□τ
B◃□-inv (ap□ t◃σ₁⇒σ₂ □σ₁⇒□σ₂◃□τ) = ⊥-elim (¬B◃⇒ t◃σ₁⇒σ₂)

-- This inversion lemma is easy, because we don't have to worry
-- about transitivity! yippee!
⇒◃□-inv : σ₁ ⇒ σ₂ ◃ □ τ → σ₁ ⇒ σ₂ ◃ τ
⇒◃□-inv (pure s) = s
⇒◃□-inv (ap□ f g) = ap□ f (⇒◃□-inv g)

-- If an arrow type is a subtype of a boxity-0 type, it must be an arrow type too.
⇒◃₀-inv : {τ : Ty ₀} → σ₁ ⇒ σ₂ ◃ τ → Σ[ τ₁ ∈ ΣTy ] Σ[ τ₂ ∈ ΣTy ] (τ ≡ proj₂ τ₁ ⇒ proj₂ τ₂)
⇒◃₀-inv rfl = (_ , _) , (_ , _) , refl
⇒◃₀-inv (arr _ _) = (_ , _) , (_ , _) , refl
⇒◃₀-inv (ap□ _ □σ₃⇒□σ₄◃τ) = ⇒◃₀-inv □σ₃⇒□σ₄◃τ

-- If an arrow type is a subtype of a boxity-1 type, it must be a box
-- applied to an arrow type.
⇒◃₁-inv : {τ : Ty ₁} → σ₁ ⇒ σ₂ ◃ τ → Σ[ τ₁ ∈ ΣTy ] Σ[ τ₂ ∈ ΣTy ] (τ ≡ □ (proj₂ τ₁ ⇒ proj₂ τ₂))
⇒◃₁-inv (pure σ₁⇒σ₂◃τ′) with ⇒◃₀-inv σ₁⇒σ₂◃τ′
... | τ₁ , τ₂ , τ′≡τ₁⇒τ₂ = τ₁ , τ₂ , cong □_ τ′≡τ₁⇒τ₂
⇒◃₁-inv (ap□ _ □σ₃⇒□σ₄◃τ) = ⇒◃₁-inv □σ₃⇒□σ₄◃τ

-- This one is more difficult... but it would probably be super
-- impossible with transitivity in the mix.

-- This says when checking subtyping it is always OK to cancel boxes
-- from both sides.  Put another way, any proof of □ σ ◃ □ τ can be
-- rewritten to have 'box' as its outermost constructor. Put yet
-- another way, any term of type □ σ → □ τ can be rewritten to have
-- 'fmap' as its outermost function call.
□-inv : □ σ ◃ □ τ → σ ◃ τ
□-inv rfl = rfl
□-inv (box p) = p
□-inv (pure p) = pureL p
□-inv (ap f g) = ◃-trans (ap□ f rfl) (⇒◃□-inv g)
□-inv (ap□ f g) = pureL (◃-trans (ap□ f rfl) (⇒◃□-inv g))

-- If a type with no outermost box is a subtype of a type with an
-- outermost box, we can remove the box.
--
-- Note we need {σ : Ty ₀} explicitly since this is not true without
-- the restriction on σ.
unbox : {σ : Ty ₀} → σ ◃ □ τ → σ ◃ τ
unbox (pure σ◃τ) = σ◃τ
unbox (ap□ σ◃σ₁⇒σ₂ □σ₁⇒□σ₂◃□τ) = ap□ σ◃σ₁⇒σ₂ (unbox □σ₁⇒□σ₂◃□τ)

------------------------------------------------------------
-- Inversion lemmas for arrow types
------------------------------------------------------------

-- If two arrow types are in the ◃ relation, then their right-hand
-- arguments are in the ◃ relation as well.
⇒-invʳ : (σ₁ ⇒ σ₂) ◃ (τ₁ ⇒ τ₂) → σ₂ ◃ τ₂
⇒-invʳ rfl = rfl
⇒-invʳ (arr _ pf) = pf
⇒-invʳ {σ₂ = σ₂} (ap□ pf₁ pf₂) = ◃-trans (⇒-invʳ pf₁) (◃-trans (pure rfl) (⇒-invʳ pf₂))

-- The same is not strictly true (neither co- nor contravariantly) for
-- the left-hand arguments.  For example, (A ⇒ A) ◃ (□A ⇒ □A) (via
-- pure + app), and also (□A ⇒ A) ◃ (A ⇒ □A) (via arr).  However, we
-- can say something based on whether σ₁ has a box or not.

-- When one arrow type is a subtype of another, and the domain of the
-- first arrow type has a box, subtyping holds contravariantly between
-- the domains.
⇒-invˡ₁ : {σ₁ : Ty ₁} → (σ₁ ⇒ σ₂) ◃ (τ₁ ⇒ τ₂) → (τ₁ ◃ σ₁)
⇒-invˡ₁ rfl = rfl
⇒-invˡ₁ (arr τ₁◃σ₁ _) = τ₁◃σ₁
⇒-invˡ₁ (ap□ σ₁⇒σ₂◃σ₃⇒σ₄ □σ₃⇒□σ₄◃τ₁⇒τ₂) with ⇒-invˡ₁ σ₁⇒σ₂◃σ₃⇒σ₄ | ⇒-invˡ₁ □σ₃⇒□σ₄◃τ₁⇒τ₂
... | σ₃◃σ₁ | τ₁◃□σ₃ = ◃-trans₁ τ₁◃□σ₃ σ₃◃σ₁

-- Same as ⇒-invˡ₁ , but with an extra box in the case that the first
-- domain has none.
⇒-invˡ₀ : {σ₁ : Ty ₀} → (σ₁ ⇒ σ₂) ◃ (τ₁ ⇒ τ₂) → (τ₁ ◃ □ σ₁)
⇒-invˡ₀ rfl = pure rfl
⇒-invˡ₀ (arr τ₁◃σ₁ _) = pure τ₁◃σ₁
⇒-invˡ₀ (ap□ σ₁⇒σ₂◃σ₃⇒σ₄ □σ₃⇒□σ₄◃τ₁⇒τ₂) with ⇒-invˡ₀ σ₁⇒σ₂◃σ₃⇒σ₄ | ⇒-invˡ₁ □σ₃⇒□σ₄◃τ₁⇒τ₂
... | σ₃◃□σ₁ | τ₁◃□σ₃ = ◃-trans₁ τ₁◃□σ₃ σ₃◃□σ₁

------------------------------------------------------------
-- Subtyping lattice
------------------------------------------------------------

₀◃₁ : {σ : Ty ₀} {τ : Ty ₁} → σ ◃ τ → □ σ ◃ τ
₀◃₁ (pure s) = box s
₀◃₁ (ap□ s₁ s₂) = ap s₁ s₂

lub : {υ : Ty b} → σ ◃ τ → σ ◃ υ → Σ[ φ ∈ ΣTy ] ((τ ◃ proj₂ φ) × (υ ◃ proj₂ φ))
glb : {υ : Ty b} → τ ◃ σ → υ ◃ σ → Σ[ φ ∈ ΣTy ] ((proj₂ φ ◃ τ) × (proj₂ φ ◃ υ))

lub rfl σ◃υ = (_ , _) , σ◃υ , rfl
lub (pure σ◃τ) σ◃υ with lub σ◃τ σ◃υ
... | (₀ , φ) , τ◃φ , υ◃φ = (₁ , □ φ) , box τ◃φ , pure υ◃φ
... | (₁ , φ) , τ◃φ , υ◃φ = (₁ , φ) , ₀◃₁ τ◃φ , υ◃φ
lub (box σ◃τ) σ◃υ with lub σ◃τ (pureL σ◃υ)
... | (₀ , φ) , τ◃φ , υ◃φ = (₁ , □ φ) , box τ◃φ , pure υ◃φ
... | (₁ , φ) , τ◃φ , υ◃φ = (₁ , φ) , ₀◃₁ τ◃φ , υ◃φ
lub {b} (arr τ₁◃σ₁ σ₂◃τ₂) σ₁⇒σ₂◃υ with b
lub {b} (arr τ₁◃σ₁ σ₂◃τ₂) σ₁⇒σ₂◃υ | ₀ with ⇒◃₀-inv σ₁⇒σ₂◃υ
lub {b} (arr {_} {_} {₀} {σ₁} τ₁◃σ₁ σ₂◃τ₂) σ₁⇒σ₂◃υ | ₀ | (_ , υ₁) , (_ , υ₂) , refl with ⇒-invˡ₀ σ₁⇒σ₂◃υ | ⇒-invʳ σ₁⇒σ₂◃υ
lub {b} (arr {_} {_} {₀} {σ₁} τ₁◃σ₁ σ₂◃τ₂) σ₁⇒σ₂◃υ | ₀ | (_ , υ₁) , (_ , υ₂) , refl | υ₁◃□σ₁ | σ₂◃υ₂ with lub σ₂◃τ₂ σ₂◃υ₂ | glb (pure τ₁◃σ₁) υ₁◃□σ₁
lub {b} (arr τ₁◃σ₁ σ₂◃τ₂) σ₁⇒σ₂◃υ | ₀ | (_ , υ₁) , (_ , υ₂) , refl | υ₁◃□σ₁ | σ₂◃υ₂ | φ₂ , τ₂◃φ₂ , υ₂◃φ₂ | φ₁ , φ₁◃τ₁ , φ₁◃υ₁ = (φ₁ Σ⇒ φ₂) , (arr φ₁◃τ₁ τ₂◃φ₂) , (arr φ₁◃υ₁ υ₂◃φ₂)
lub {b} (arr {_} {_} {₁} {σ₁} τ₁◃σ₁ σ₂◃τ₂) σ₁⇒σ₂◃υ | ₀ | (_ , υ₁) , (_ , υ₂) , refl = {!!}
lub {b} (arr τ₁◃σ₁ σ₂◃τ₂) σ₁⇒σ₂◃υ | ₁ = {!!}
  -- next step ^^^ : use ⇒◃₀-inv and ⇒◃₁-inv (move them above here)
  -- to decompose υ?
  -- Look also at new lemmas ⇒-invˡ₀, ⇒-invˡ₁.  Can we make use of those?
  -- Maybe we can compose those together into a more general/useful lemma?
lub (ap σ◃τ σ◃τ₁) σ◃υ = {!!}
lub (ap□ σ◃τ σ◃τ₁) σ◃υ = {!!}

glb τ◃σ υ◃σ = {!!}

------------------------------------------------------------
-- Lemma: ¬A × ¬B → ¬ (A ⊎ B
------------------------------------------------------------

lem₁ : {P Q : Set} → (¬ P × ¬ Q) → ¬ (P ⊎ Q)
lem₁ (¬P , ¬Q) (inj₁ P) = ¬P P
lem₁ (¬P , ¬Q) (inj₂ Q) = ¬Q Q

------------------------------------------------------------
-- Subtyping is decidable
------------------------------------------------------------

◃-Dec : Decidable (_◃_ {b₁} {b₂})

-- First, some impossible cases.
◃-Dec (base _) (_ ⇒ _) = no ¬B◃⇒
◃-Dec (_ ⇒ _) (base _) = no ¬⇒◃B
◃-Dec (□ _) (base _) = no ¬□◃B

-- There's no subtyping among base types, so just check for equality.
◃-Dec (base B₁) (base B₂) with B₁ ≟B B₂
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
-- Raw, untyped terms
------------------------------------------------------------

-- Raw, untyped terms.
data Raw (n : ℕ) : Set where
  var : Fin n → Raw n
  ƛ : Raw (suc n) → Raw n
  _∙_ : Raw n → Raw n → Raw n

-- Shift.
_↑_ : Fin (suc n) → Raw n → Raw (suc n)
i ↑ var x = var (punchIn i x)
i ↑ ƛ r = ƛ (Fin.suc i ↑ r)
i ↑ (r₁ ∙ r₂) = (i ↑ r₁) ∙ (i ↑ r₂)

variable
  r r₁ r₂ : Raw n

------------------------------------------------------------
-- Typing + coercion elaboration
------------------------------------------------------------

data Ctx : ℕ → Set where
  ∅ : Ctx 0
  _,_ : Ctx n → Ty b → Ctx (suc n)

infixr 4 _,_

variable
  Γ Γ₁ Γ₂ : Ctx n

-- Approach to variables + weakening adapted from
-- Keller + Alternkirch, "Normalization by hereditary substitutions"
-- https://www.cs.nott.ac.uk/~psztxa/publ/msfp10.pdf
data Var : Ctx n → Ty b → Set₁ where
  vz : Var (Γ , τ) τ
  vs : Var Γ τ → Var (Γ , σ) τ

_-_ : (Γ : Ctx (suc n)) → Var Γ σ → Ctx n
(Γ , _) - vz = Γ
_-_ {n = suc n} (Γ , x) (vs v) = Γ - v , x

wkv : (x : Var Γ σ) → Var (Γ - x) τ → Var Γ τ
wkv vz y = vs y
wkv (vs x) vz = vz
wkv (vs x) (vs y) = vs (wkv x y)

var2fin : {Γ : Ctx n} → Var Γ τ → Fin n
var2fin vz = Fin.zero
var2fin (vs x) = Fin.suc (var2fin x)

var2fin-wkv : (x : Var Γ σ) → (y : Var (Γ - x) τ) → var2fin (wkv x y) ≡ punchIn (var2fin x) (var2fin y)
var2fin-wkv vz y = refl
var2fin-wkv (vs x) vz = refl
var2fin-wkv (vs x) (vs y) = cong Fin.suc (var2fin-wkv x y)

var2fin-inj₁ : {σ₁ : Ty b₁} {σ₂ : Ty b₂} → (x : Var Γ σ₁) → (y : Var Γ σ₂) → (var2fin x ≡ var2fin y) → Σ[ p ∈ b₁ ≡ b₂ ] _≡⟦_⟧_ {_} {Ty} σ₁ p σ₂
var2fin-inj₁ vz vz _ = refl , refl
var2fin-inj₁ (vs x) (vs y) eq = var2fin-inj₁ x y (suc-injective eq)

var2fin-inj₂ : (x : Var Γ σ) → (y : Var Γ σ) → (var2fin x ≡ var2fin y) → (x ≡ y)
var2fin-inj₂ vz vz _ = refl
var2fin-inj₂ (vs x) (vs y) eq = cong vs (var2fin-inj₂ x y (suc-injective eq))

-- Set₁ != Set
-- var2fin-inj : (x : Var Γ σ₁) → (y : Var Γ σ₂) → (var2fin x ≡ var2fin y) → Σ[ p ∈ (σ₁ ≡ σ₂) ] (_≡⟦_⟧_ {_} {Var Γ} x p y)
-- var2fin-inj x y eq = ?


-- Typing judgments for raw terms in system with subtyping
data _⊢ₛ_∈_ : Ctx n → Raw n → Ty b → Set₁ where
  sub : σ <: τ → Γ ⊢ₛ r ∈ σ → Γ ⊢ₛ r ∈ τ
  var : ∀ {i} → (x : Var Γ τ) → (i ≡ var2fin x) → Γ ⊢ₛ var i ∈ τ
  ƛ : (Γ , σ) ⊢ₛ r ∈ τ → Γ ⊢ₛ ƛ r ∈ (σ ⇒ τ)
  _∙_ : Γ ⊢ₛ r₁ ∈ (σ ⇒ τ) → Γ ⊢ₛ r₂ ∈ σ → Γ ⊢ₛ r₁ ∙ r₂ ∈ τ

-- Can we use some kind of uniqueness lemma, that says two typing
-- derivations for the same raw term have to result in (similar) types?
--   - Surely doesn't have to be *the same* type due to subtyping
--   - But can we say that one type must be a subtype of the other?
--   - Maybe not; the same type can be subtype of two different types
--     which are not comparable to each other.
--   - But surely the types must have the same underlying shape.

unique : Γ ⊢ₛ r ∈ σ₁ → Γ ⊢ₛ r ∈ σ₂ → ⌊ σ₁ ⌋ ≡ ⌊ σ₂ ⌋
unique (sub σ<:σ₁ s) t = trans (sym (<:→⌊⌋ σ<:σ₁)) (unique s t)
unique s (sub σ<:σ₂ t) = trans (unique s t) (<:→⌊⌋ σ<:σ₂)
unique (var x i) (var y j) with (var2fin-inj₁ x y (trans (sym i) j))
... | refl , refl = refl
unique (ƛ s) (ƛ t) = {!!}
unique (s₁ ∙ s₂) (t₁ ∙ t₂) with unique s₂ t₂
... | ⌊σ⌋≡⌊σ₃⌋ = {!!}

-- XXX Perhaps make another version that only does subtyping in
-- certain specific spots e.g. at function applications + variable
-- lookups, and prove that it is equivalent?
--
-- Well, this version is NOT equivalent, because of e.g. being able to
-- apply subtyping to the output of a lambda.  Do we add subtyping to
-- the lambda rule as well?  Will I really need this?

data _⊢ₛ′_∈_ : Ctx n → Raw n → Ty b → Set₁ where
  var : (x : Var Γ σ) → (σ <: τ) → Γ ⊢ₛ′ var (var2fin x) ∈ τ
  ƛ : (Γ , σ) ⊢ₛ′ r ∈ τ → Γ ⊢ₛ′ ƛ r ∈ (σ ⇒ τ)
  app : Γ ⊢ₛ′ r₁ ∈ (σ₁ ⇒ τ) → Γ ⊢ₛ′ r₂ ∈ σ₂ → (σ₂ <: σ₁) → Γ ⊢ₛ′ r₁ ∙ r₂ ∈ τ

-- This direction is easy
s′→s : Γ ⊢ₛ′ r ∈ τ → Γ ⊢ₛ r ∈ τ
s′→s (var x σ<:τ) = sub σ<:τ (var {!!} {!!})
s′→s (ƛ d) = ƛ (s′→s d)
s′→s (app d₁ d₂ s) = s′→s d₁ ∙ sub s (s′→s d₂)

-- Other direction is tricky
help₃ : σ₂ ◃ σ₁ → (Γ , σ₁) ⊢ₛ′ r ∈ τ → (Γ , σ₂) ⊢ₛ′ r ∈ τ
◃-s′ : σ ◃ τ → Γ ⊢ₛ′ r ∈ σ → Γ ⊢ₛ′ r ∈ τ
<:-s′ : σ <: τ → Γ ⊢ₛ′ r ∈ σ → Γ ⊢ₛ′ r ∈ τ
s→s′ : Γ ⊢ₛ r ∈ τ → Γ ⊢ₛ′ r ∈ τ

help₃ σ₂◃σ₁ (var vz σ<:τ) = var vz (tr (◃→<: σ₂◃σ₁) σ<:τ)
help₃ σ₂◃σ₁ (var (vs x) σ<:τ) = var (vs x) σ<:τ
help₃ σ₂◃σ₁ (ƛ t) = ƛ {!!} -- stuck!
help₃ σ₂◃σ₁ (app t₁ t₂ σ₄<:σ₃) = app (help₃ σ₂◃σ₁ t₁) (help₃ σ₂◃σ₁ t₂) σ₄<:σ₃

◃-s′ σ◃τ (var x s) = var x (tr s (◃→<: σ◃τ))
◃-s′ rfl (ƛ t) = (ƛ t)
◃-s′ (arr τ₁◃σ₁ σ₂◃τ₂) (ƛ t) = ƛ (help₃ τ₁◃σ₁ (◃-s′ σ₂◃τ₂ t))
◃-s′ (pure σ⇒τ₁◃τ) (ƛ t) = {!!}
◃-s′ (ap□ σ◃τ σ◃τ₁) (ƛ t) = {!!}
◃-s′ σ◃τ (app t₁ t₂ s) = app (◃-s′ (arr rfl σ◃τ) t₁) t₂ s

<:-s′ σ<:τ = ◃-s′ (<:→◃ σ<:τ)

s→s′ (sub σ<:τ d) = <:-s′ σ<:τ (s→s′ d)
s→s′ (var x _) = {!!}
s→s′ (ƛ d) = ƛ (s→s′ d)
s→s′ (d₁ ∙ d₂) = app (s→s′ d₁) (s→s′ d₂) rfl

-- Typing judgments for raw terms in system without subtyping, but
-- with extra pure and ap rules
data _⊢_∈_ : Ctx n → Raw n → Ty b → Set₁ where
  var : (x : Var Γ τ) → Γ ⊢ var (var2fin x) ∈ τ
  ƛ : (Γ , σ) ⊢ r ∈ τ → Γ ⊢ ƛ r ∈ (σ ⇒ τ)
  _∙_ : Γ ⊢ r₁ ∈ (σ ⇒ τ) →  Γ ⊢ r₂ ∈ σ →  Γ ⊢ r₁ ∙ r₂ ∈ τ
  pure :  Γ ⊢ r ∈ τ → Γ ⊢ r ∈ □ τ
  ap :  Γ ⊢ r ∈ □ (σ ⇒ τ) → Γ ⊢ r ∈ □ σ ⇒ □ τ

-- Weakening for terms.  Needed for arr case of coercion insertion.
wk : {Γ : Ctx (suc n)} (x : Var Γ σ) → (Γ - x) ⊢ r ∈ τ → Γ ⊢ (var2fin x ↑ r) ∈ τ
wk x (var y) rewrite sym (var2fin-wkv x y) = var (wkv x y)
wk x (ƛ t) = ƛ (wk (vs x) t)
wk x (t₁ ∙ t₂) = wk x t₁ ∙ wk x t₂
wk x (pure t) = pure (wk x t)
wk x (ap t) = ap (wk x t)

------------------------------------------------------------
-- Terms
------------------------------------------------------------

-- We define typed terms, indexed by context and type, as
-- a dependent pair of a raw term and a typing derivation.

Term : Ctx n → Ty b → Set₁
Term {n = n} Γ τ = Σ[ r ∈ Raw n ] Γ ⊢ r ∈ τ

-- Smart constructors for Term

var′ : Var Γ σ → Term Γ σ
var′ x = (var (var2fin x) , var x)

ƛ′ : Term (Γ , σ) τ → Term Γ (σ ⇒ τ)
ƛ′ (r , t) = (ƛ r , ƛ t)

_∙′_ : Term Γ (σ ⇒ τ) → Term Γ σ → Term Γ τ
(r₁ , t₁) ∙′ (r₂ , t₂) = (r₁ ∙ r₂ , t₁ ∙ t₂)

pure′ : Term Γ σ → Term Γ (□ σ)
pure′ (r , t) = (r , pure t)

ap′ : Term Γ (□ (σ ⇒ τ)) → Term Γ (□ σ ⇒ □ τ)
ap′ (r , t) = (r , ap t)

wk′ : (x : Var Γ σ) → Term (Γ - x) τ → Term Γ τ
wk′ x (r , t) = (var2fin x ↑ r , wk x t)

-- Similar for terms with subtyping, except we don't need constructors

Term<: : Ctx n → Ty b → Set₁
Term<: {n = n} Γ τ = Σ[ r ∈ Raw n ] Γ ⊢ₛ r ∈ τ

------------------------------------------------------------
-- Coercion insertion + elaboration

infixr 5 _≪_

_≪_ : σ <: τ → Term Γ σ → Term Γ τ
rfl ≪ t = t
tr σ<:τ τ<:υ ≪ t = τ<:υ ≪ σ<:τ ≪ t
-- η-expand at function types to apply the coercions --- could optimize this part
-- of course, especially if t is syntactically a lambda already
arr τ₁<:σ₁ σ₂<:τ₂ ≪ t = ƛ′ (σ₂<:τ₂ ≪ (wk′ vz t ∙′ (τ₁<:σ₁ ≪ var′ vz)))
-- -- essentially 'fmap coerce'/
box σ<:τ ≪ t = (ap′ (pure′ (ƛ′ (σ<:τ ≪ var′ vz)))) ∙′ t
pure ≪ t = pure′ t
ap ≪ t = ap′ t

-- Elaborate derivations with subtyping into subtyping-free terms with pure + ap
elaborate : Γ ⊢ₛ r ∈ τ → Term Γ τ
elaborate (sub σ<:τ t) = σ<:τ ≪ elaborate t
elaborate (var x eq) = var′ x
elaborate (ƛ t) = ƛ′ (elaborate t)
elaborate (t₁ ∙ t₂) = elaborate t₁ ∙′ elaborate t₂

------------------------------------------------------------
-- Equivalence up to β, η, + Applicative laws

variable
  s t u : Term Γ τ

compose : Term Γ ((τ ⇒ υ) ⇒ (σ ⇒ τ) ⇒ σ ⇒ υ)
compose =  ƛ′ (ƛ′ (ƛ′ (var′ (vs (vs vz)) ∙′ (var′ (vs vz) ∙′ var′ vz))))

id : Term Γ (σ ⇒ σ)
id = ƛ′ (var′ vz)

infixl 5 _<*>_
_<*>_ : Term Γ (□ (σ ⇒ τ)) → Term Γ (□ σ) → Term Γ (□ τ)
f <*> x = ap′ f ∙′ x

-- Term equivalence up to Applicative laws.  Type heterogeneous??
infix 4 _≈_
data _≈_ : Term Γ τ → Term Γ τ → Set₁ where

  -- Equivalence and congruence laws
  ≈refl : s ≈ s
  ≈trans : s ≈ t → t ≈ u → s ≈ u
  ≈sym : s ≈ t → t ≈ s
  ≈cong : {s t : Term Γ₁ σ} → (f : Term Γ₁ σ → Term Γ₂ τ) → s ≈ t → f s ≈ f t
  ≈cong₂ : {s t : Term Γ₁ σ₁} {u v : Term Γ₂ σ₂} → (f : Term Γ₁ σ₁ → Term Γ₂ σ₂ → Term Γ τ) → s ≈ t → u ≈ v → f s u ≈ f t v

  -- η-equivalence
  η : t ≈ (ƛ′ (wk′ vz t ∙′ var′ vz))

  -- Applicative laws

  -- pure id <*> v = v                            -- Identity
  idt : (pure′ id) <*> s ≈ s

  -- pure f <*> pure x = pure (f x)               -- Homomorphism
  hom : (pure′ s) <*> (pure′ t) ≈ pure′ (s ∙′ t)

  -- u <*> pure y = pure ($ y) <*> u              -- Interchange
  int : s <*> pure′ t ≈ (pure′ (ƛ′ (var′ vz ∙′ wk′ vz t))) <*> s

  -- pure (.) <*> u <*> v <*> w = u <*> (v <*> w) -- Composition
  pur : pure′ compose <*> s <*> t <*> u ≈ s <*> (t <*> u)


------------------------------------------------------------
-- Coherence theorem

-- For any given raw term r, any two typing derivations for r with
-- subtyping will elaborate to equivalent terms.

coherence : (s t : Γ ⊢ₛ r ∈ τ) → elaborate s ≈ elaborate t
coherence {r = var x} (sub x₁ s) (sub x₂ t) = {!!}
coherence {r = var x} (sub σ<:τ s) (var x₂ eq) = {!σ<:τ!}
coherence {r = var x} (var x₁ eq) t = {!!}
coherence {r = ƛ r} (sub x s) t = {!!}
coherence {r = ƛ r} (ƛ s) (sub x t) = {!!}
coherence {r = ƛ r} (ƛ s) (ƛ t) = ≈cong ƛ′ (coherence s t)
coherence {r = r₁ ∙ r₂} (sub x s) t = {!!}
coherence {r = r₁ ∙ r₂} (s₁ ∙ s₂) (sub x t) = {!!}
coherence {r = r₁ ∙ r₂} (s₁ ∙ s₂) (t₁ ∙ t₂) = {!!}

-- coherence (sub σ<:τ s) t = {!!}
-- coherence (var x) t = {!!}
-- coherence (ƛ s) (sub x t) = {!!}
-- coherence (ƛ s) (ƛ t) = ≈cong ƛ′ (coherence s t)
-- coherence (s₁ ∙ s₂) (sub x t) = {!!}
-- -- Note, in this last case s₂ and t₂ might not be the same type!  So
-- -- the IH does not apply to them.  Can we generalize?
-- coherence (s₁ ∙ s₂) (t₁ ∙ t₂) = ≈cong₂ {!_∙′_!} {!!} {!!}
