open import Data.Bool
open import Data.Nat
open import Data.Fin hiding (_≥_)
open import Data.Product using (Σ-syntax ; _,_)
open import Data.Sum
open import Data.Product
open import Relation.Nullary.Negation
open import Relation.Nullary.Decidable
open import Data.Empty
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality

variable
  n : ℕ

------------------------------------------------------------
-- Types
------------------------------------------------------------

data Type (B : Set) : Set where
  base : B → Type B
  _⇒_ : Type B → Type B → Type B
  □_ : Type B → Type B

infix 2 _⇒_
infix 30 □_

base-inj : {B : Set} {b₁ b₂ : B} → base b₁ ≡ base b₂ → b₁ ≡ b₂
base-inj refl = refl

⇒-inj : {B : Set} {τ₁₁ τ₁₂ τ₂₁ τ₂₂ : Type B} → ((τ₁₁ ⇒ τ₁₂) ≡ (τ₂₁ ⇒ τ₂₂)) → (τ₁₁ ≡ τ₂₁) × (τ₁₂ ≡ τ₂₂)
⇒-inj refl = refl , refl

□-inj : {B : Set} {τ₁ τ₂ : Type B} → (□ τ₁ ≡ □ τ₂) → (τ₁ ≡ τ₂)
□-inj refl = refl

module Infer (B : Set) (DecB : Decidable {A = B} _≡_) (C : Set) (CTy : C → Type B) where

  ------------------------------------------------------------
  -- Type equality is decidable
  ------------------------------------------------------------

  ≡Ty-Dec : Decidable {A = Type B} _≡_
  ≡Ty-Dec (base b₁) (base b₂) with DecB b₁ b₂
  ... | no b₁≢b₂ = no λ eq → b₁≢b₂ (base-inj eq)
  ... | yes b₁≡b₂ = yes (cong base b₁≡b₂)
  ≡Ty-Dec (base _) (_ ⇒ _) = no (λ ())
  ≡Ty-Dec (base _) (□ _) = no (λ ())
  ≡Ty-Dec (_ ⇒ _) (base _) = no (λ ())
  ≡Ty-Dec (σ₁ ⇒ τ₁) (σ₂ ⇒ τ₂) with ≡Ty-Dec σ₁ σ₂ | ≡Ty-Dec τ₁ τ₂
  ... | no σ₁≢σ₂ | _ = no (λ eq → σ₁≢σ₂ (proj₁ (⇒-inj eq)))
  ... | yes _ | no τ₁≢τ₂ = no (λ eq → τ₁≢τ₂ (proj₂ (⇒-inj eq)))
  ... | yes σ₁≡σ₂ | yes τ₁≡τ₂ = yes (cong₂ _⇒_ σ₁≡σ₂ τ₁≡τ₂)
  ≡Ty-Dec (_ ⇒ _) (□ _) = no (λ ())
  ≡Ty-Dec (□ _) (base _) = no (λ ())
  ≡Ty-Dec (□ _) (_ ⇒ _) = no (λ ())
  ≡Ty-Dec (□ τ₁) (□ τ₂) with ≡Ty-Dec τ₁ τ₂
  ... | no τ₁≢τ₂ = no (λ eq → τ₁≢τ₂ (□-inj eq))
  ... | yes τ₁≡τ₂ = yes (cong □_ τ₁≡τ₂)

  ------------------------------------------------------------
  -- Subtyping
  ------------------------------------------------------------

  data _<:_ : Type B → Type B → Set where
    rfl : {τ : Type B} → τ <: τ
    tr : {σ τ υ : Type B} → σ <: τ → τ <: υ → σ <: υ
    arr : {τ₁ τ₂ σ₁ σ₂ : Type B} → (τ₁ <: σ₁) → (σ₂ <: τ₂) → (σ₁ ⇒ σ₂ <: τ₁ ⇒ τ₂)
    box : {σ τ : Type B} → (σ <: τ) → (□ σ <: □ τ)
    pure : {τ : Type B} → τ <: □ τ
    ap : {σ τ : Type B} → □ (σ ⇒ τ) <: □ σ ⇒ □ τ

  infix 1 _<:_

  -- Ill-fated attempt at not having to deal with transitivity.
  {-
  -- Version of subtyping with transitivity.
  data _<:′_ : Type B → Type B → Set where
    tr : {σ τ υ : Type B} → σ <:′ τ → τ <:′ υ → σ <:′ υ
    emb : {σ τ : Type B} → σ <: τ → σ <:′ τ

  -- Proof that transitivity is admissible, so we are OK to just use
  -- <: everywhere instead of <:′
  tr-admissible : {σ τ υ : Type B} → σ <: τ → τ <: υ → σ <: υ
  tr-admissible rfl τ<:υ = τ<:υ
  tr-admissible (arr τ₁<:σ₁ σ₂<:τ₂) τ₁⇒τ₂<:υ = {!!}
  tr-admissible (box σ<:τ) □τ<:υ = {!!}
  tr-admissible pure rfl = pure
  tr-admissible pure (box σ<:τ) = {!!}
  tr-admissible pure pure = {!!}
  tr-admissible pure ap = {!!}
  tr-admissible ap τ<:υ = {!!}

  <:′→<: : {σ τ : Type B} → σ <:′ τ → σ <: τ
  <:′→<: (tr σ<:′τ₁ τ₁<:′τ) = tr-admissible (<:′→<: σ<:′τ₁) (<:′→<: τ₁<:′τ)
  <:′→<: (emb σ:<τ) = σ:<τ
  -}

  -- First attempt at inversion lemma for subtyping, but as stated this is
  -- not true, because of PURE!
  {-
  ⇒<:⇒ : {σ τ υ : Type B} → σ ⇒ τ <: υ → Σ[ υ₁ ∈ Type B ] Σ[ υ₂ ∈ Type B ] (υ ≡ (υ₁ ⇒ υ₂))
  ⇒<:⇒ {σ = σ} {τ = τ} rfl = σ , τ , refl
  ⇒<:⇒ (tr σ⇒τ<:τ₁ τ₁<:υ) = {!!}
  ⇒<:⇒ (arr {τ₁ = τ₁} {τ₂ = τ₂} σ⇒τ<:υ σ⇒τ<:υ₁) = τ₁ , τ₂ , refl
  ⇒<:⇒ pure = {!!}
  -}

  -- Should work the other way around, though...
  -- Argh, no, this is also false because of AP!
  {-
  ⇒<:⇒ : {σ τ υ : Type B} → σ <: τ ⇒ υ → Σ[ σ₁ ∈ Type B ] Σ[ σ₂ ∈ Type B ] (σ ≡ (σ₁ ⇒ σ₂))
  ⇒<:⇒ {τ = τ} {υ = υ} rfl = τ , υ , refl
  ⇒<:⇒ (tr σ<:τ₁ τ₁<:τ⇒υ) with ⇒<:⇒ τ₁<:τ⇒υ
  ... | τ₁₁ , τ₁₂ , τ₁≡τ₁₁⇒τ₁₂ rewrite τ₁≡τ₁₁⇒τ₁₂ = ⇒<:⇒ σ<:τ₁
  ⇒<:⇒ (arr σ<:τ⇒υ σ<:τ⇒υ₁) = {!!}
  ⇒<:⇒ ap = {!!}
  -}

  --------------------------------------------------
  -- Some inversion lemmas about subtyping

  <:B-inv : {τ : Type B} {b : B} → (τ <: base b) → (τ ≡ base b)
  <:B-inv rfl = refl
  <:B-inv (tr τ<:τ₁ τ₁<:b) rewrite <:B-inv τ₁<:b = <:B-inv τ<:τ₁

  ¬□<:b : {τ : Type B} {b : B} → ¬ (□ τ <: base b)
  ¬□<:b □τ<:b with <:B-inv □τ<:b
  ... | ()

  □^_∙_ : ℕ → Type B → Type B
  □^ zero ∙ τ = τ
  □^ suc n ∙ τ = □ (□^ n ∙ τ)

  infix 5 □^_∙_

  data LiftedBase (b : B) : Type B → Set where
    IsBase : LiftedBase b (base b)
    IsBox : {τ : Type B} → LiftedBase b τ → LiftedBase b (□ τ)

  LB⇒□^ : {b : B} {τ : Type B} → LiftedBase b τ → Σ[ n ∈ ℕ ] τ ≡ □^ n ∙ base b
  LB⇒□^ IsBase = zero , refl
  LB⇒□^ (IsBox LB) with LB⇒□^ LB
  ... | k , τ≡□^kb = suc k , cong □_ τ≡□^kb

  B<:LB : {b : B} {τ : Type B} → LiftedBase b τ → base b <: τ
  B<:LB IsBase = rfl
  B<:LB (IsBox lb) = tr (B<:LB lb) pure

  B<:-inv : {b : B} {σ τ : Type B} → σ <: τ → LiftedBase b σ → LiftedBase b τ
  B<:-inv rfl IsBase = IsBase
  B<:-inv (tr b<:τ₁ τ₁<:τ) IsBase = B<:-inv τ₁<:τ (B<:-inv b<:τ₁ IsBase)
  B<:-inv pure IsBase = IsBox IsBase
  B<:-inv rfl (IsBox LBσ) = IsBox LBσ
  B<:-inv (tr □τ₂<:τ₁ τ₁<:τ) (IsBox LBσ) = B<:-inv τ₁<:τ (B<:-inv □τ₂<:τ₁ (IsBox LBσ))
  B<:-inv (box σ<:τ) (IsBox LBσ) = IsBox (B<:-inv σ<:τ LBσ)
  B<:-inv pure (IsBox LBσ) = IsBox (IsBox LBσ)

  B<:□-inv : {b : B} {τ : Type B} → base b <: □ τ → base b <: τ
  B<:□-inv b<:□τ with B<:-inv b<:□τ IsBase
  ... | IsBox LBbτ = B<:LB LBbτ

  ¬LB<:⇒ : {b : B} {σ τ₁ τ₂ : Type B} → LiftedBase b σ → ¬ (σ <: τ₁ ⇒ τ₂)
  ¬LB<:⇒ LB σ<:τ₁⇒τ₂ with B<:-inv σ<:τ₁⇒τ₂ LB
  ... | ()

  ¬B<:⇒ : {b : B} {τ₁ τ₂ : Type B} → ¬ (base b <: τ₁ ⇒ τ₂)
  ¬B<:⇒ = ¬LB<:⇒ IsBase

  -- Next order of business: characterize subtyping for functions just like
  --   I did for base types.  Come up with something like "LiftedFun"...

  -- data LiftedFun (σ τ : Type B) : Type B → Set where
  --   IsFun : LiftedFun σ τ (σ ⇒ τ)
  --   IsBoxR : LiftedFun LiftedFun σ τ (σ ⇒ □ τ)
  --   IsAp : LiftedFun σ τ (□ σ ⇒ □ τ)

  --  F<:LF : {σ τ υ : Type B} → LiftedFun σ τ υ → (σ ⇒ τ) <: υ

  -- ⇒<:□-inv : {τ₁ τ₂ τ : Type B} → (τ₁ ⇒ τ₂ <: □ τ) → (τ₁ ⇒ τ₂ <: τ)
  -- ⇒<:□-inv (tr τ₁⇒τ₂<:τ₃ τ₃<:□τ) = {!!}
  -- ⇒<:□-inv pure = rfl

  <:-□-inv : {σ τ : Type B} → ¬(Σ[ σ′ ∈ Type B ] σ ≡ □ σ′) → (σ <: □ τ) → (σ <: τ)
  □-<:-inv : {σ τ : Type B} → (□ σ <: □ τ) → (σ <: τ)

  <:-□-inv {τ = τ} notbox rfl = contradiction (τ , refl) notbox
  <:-□-inv notbox (tr {τ = base b} σ<:b b<:□τ) with <:B-inv σ<:b
  ... | refl = {!!}
  <:-□-inv notbox (tr {τ = τ₁ ⇒ τ₂} σ<:τ₁ τ₁<:□τ) = {!!}
  <:-□-inv notbox (tr {τ = □ τ₁} σ<:τ₁ τ₁<:□τ) = {!!}
  <:-□-inv notbox (box {σ = σ₁} σ<:τ) = contradiction (σ₁ , refl) notbox
  <:-□-inv notbox pure = rfl

  □-<:-inv rfl = rfl
  □-<:-inv (tr {τ = base b} □σ<:b b<:□τ) with <:B-inv □σ<:b
  ... | ()
  □-<:-inv (tr {τ = τ₁ ⇒ τ₂} □σ<:τ₁⇒τ₂ τ₁⇒τ₂<:□τ) = {!tr □σ<:τ₁⇒τ₂ (<:-□-inv _ τ₁⇒τ₂<:□τ)!}
  □-<:-inv (tr {τ = □ τ₁} □σ<:□τ₁ □τ₁<:□τ) = tr (□-<:-inv □σ<:□τ₁) (□-<:-inv □τ₁<:□τ)
  □-<:-inv (box prf) = prf
  □-<:-inv pure = pure

  ⇒-¬<:-B : {σ τ : Type B} {b : B} → ¬ (σ ⇒ τ <: base b)

  ⇒-¬<:-B (tr σ⇒τ<:b σ⇒τ<:b₁) = {!!}

  --------------------------------------------------
  -- Subtyping is decidable

  <:-Dec : Decidable _<:_
  <:-Dec (base b₁) (base b₂) with DecB b₁ b₂
  ... | no b₁≢b₂ = no (λ b₁<:b₂ → contradiction (base-inj (<:B-inv b₁<:b₂)) b₁≢b₂)
  ... | yes b₁≡b₂ rewrite b₁≡b₂ = yes rfl
  <:-Dec (base _) (_ ⇒ _) = no ¬B<:⇒
  <:-Dec (base b) (□ τ) with <:-Dec (base b) τ
  ... | no ¬b<:τ = no (λ b<:□τ → ¬b<:τ (B<:□-inv b<:□τ))
  ... | yes b<:τ = yes (tr b<:τ pure)
  <:-Dec (_ ⇒ _) (base _) = no ⇒-¬<:-B
  <:-Dec (σ₁ ⇒ σ₂) (τ₁ ⇒ τ₂) = {!!}
  <:-Dec (σ ⇒ σ₁) (□ τ) = {!!}
  <:-Dec (□ _) (base _) = no ¬□<:b
  <:-Dec (□ σ) (τ ⇒ τ₁) = {!!}
  <:-Dec (□ σ) (□ τ) with <:-Dec σ τ
  ... | no ¬σ<:τ = no (λ □σ<:□τ → ¬σ<:τ (□-<:-inv □σ<:□τ))
  ... | yes σ<:τ = yes (box σ<:τ)


  ------------------------------------------------------------
  -- Terms + contexts
  ------------------------------------------------------------

  data Term : ℕ → Set₁ where
    var : Fin n → Term n
    ƛ : Type B → Term (suc n) → Term n
    _∙_ : Term n → Term n → Term n
    con : C → Term n

  data Ctx : ℕ → Set₁ where
    ∅ : Ctx 0
    _,,_ : Ctx n → Type B → Ctx (suc n)

  variable
    Γ : Ctx n

  _!_ : Ctx n → Fin n → Type B
  (_ ,, x) ! zero = x
  (Γ ,, x) ! suc i = Γ ! i

  infix 1 _⊢_ː_
  infix 1 _⊬_
  infix 2 _,,_

  ------------------------------------------------------------
  -- Typing and untyping
  ------------------------------------------------------------

  data _⊢_ː_ : Ctx n → Term n → Type B → Set₁ where
    sub : {t : Term n} {σ τ : Type B} → (Γ ⊢ t ː σ) → (σ <: τ) → Γ ⊢ t ː τ
    var : (x : Fin n) → Γ ⊢ var x ː (Γ ! x)
    lam : {t : Term (suc n)} {τ₁ τ₂ : Type B} → (Γ ,, τ₁ ⊢ t ː τ₂) → (Γ ⊢ ƛ τ₁ t ː (τ₁ ⇒ τ₂))
    app : {σ τ : Type B} {t₁ t₂ : Term n} → (Γ ⊢ t₁ ː σ ⇒ τ) → (Γ ⊢ t₂ ː σ) → (Γ ⊢ t₁ ∙ t₂ ː τ)
    con : (c : C) → Γ ⊢ con c ː CTy c

  data _⊬_ : Ctx n → Term n → Set₁ where
    lam : {t : Term (suc n)} (σ : Type B) → (Γ ,, σ ⊬ t) → (Γ ⊬ ƛ σ t)

  ⊬⇒¬⊢ : {t : Term n} → (Γ ⊬ t) → ¬ (Σ[ τ ∈ Type B ] (Γ ⊢ t ː τ))
  ⊬⇒¬⊢ (lam σ pf) (τ , sub Γ⊢ƛσt:τ₁ τ₂<:τ) = ⊬⇒¬⊢ pf (σ , {!!})
  ⊬⇒¬⊢ (lam σ pf) ((.σ ⇒ τ) , lam Γ⊢ƛσt:τ) = ⊬⇒¬⊢ pf (τ , Γ⊢ƛσt:τ)

  ------------------------------------------------------------
  -- Inference algorithm
  ------------------------------------------------------------

  infer : (Γ : Ctx n) → (t : Term n) → (Σ[ τ ∈ Type B ] (Γ ⊢ t ː τ)) ⊎ (Γ ⊬ t)
  infer Γ (var x) = inj₁ (Γ ! x , var x)
  infer Γ (ƛ σ t) with infer (Γ ,, σ) t
  ... | inj₁ (τ , Γ,σ⊢t:τ ) = inj₁ ((σ ⇒ τ) , lam Γ,σ⊢t:τ)
  ... | inj₂ pf = inj₂ (lam _ pf)
  infer Γ (t₁ ∙ t₂) with infer Γ t₁ | infer Γ t₂
  ... | inj₁ ((σ ⇒ τ) , Γ⊢t₁:σ⇒τ) | inj₁ (τ₂ , Γ⊢t₂:τ₂) = {!!} -- with σ Ty≟ τ₂
  -- infer Γ (t₁ ∙ t₂) | inj₁ ((σ ⇒ τ) , Γ⊢t₁:σ⇒τ) | inj₁ (τ₂ , Γ⊢t₂:τ₂) | eq = ?
  -- infer Γ (t₁ ∙ t₂) | inj₁ (base x , Γ⊢t₁:τ₁) | inj₁ (τ₂ , Γ⊢t₂:τ₂) = {!!}
  ... | inj₁ (□ τ₁ , Γ⊢t₁:τ₁) | inj₁ (τ₂ , Γ⊢t₂:τ₂) = {!!}
  ... | inj₁ x | inj₂ y = {!!}
  ... | inj₂ y₁ | y = {!!}
  infer Γ (con x) = inj₁ (CTy x , con x)
