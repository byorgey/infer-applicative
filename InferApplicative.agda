open import Data.Bool
open import Data.Nat
open import Data.Fin
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

  infix 1 _<:_
  infix 1 _⊢_ː_
  infix 1 _⊬_
  infix 2 _,,_

  data _<:_ : Type B → Type B → Set where
    rfl : {τ : Type B} → τ <: τ
    tr : {σ τ υ : Type B} → σ <: τ → τ <: υ → σ <: υ
    arr : {τ₁ τ₂ σ₁ σ₂ : Type B} → (τ₁ <: σ₁) → (σ₂ <: τ₂) → (σ₁ ⇒ σ₂ <: τ₁ ⇒ τ₂)
    box : {σ τ : Type B} → (σ <: τ) → (□ σ <: □ τ)
    pure : {τ : Type B} → τ <: □ τ
    ap : {σ τ : Type B} → □ (σ ⇒ τ) <: □ σ ⇒ □ τ

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

  ⇒-¬<:-B : {σ τ : Type B} {b : B} → ¬ (σ ⇒ τ <: base b)
  no-base-subtype : {b₁ b₂ : B} → base b₁ <: base b₂ → b₁ ≡ b₂

  ⇒-¬<:-B (tr σ⇒τ<:b σ⇒τ<:b₁) = {!!}

  no-base-subtype rfl = refl
  no-base-subtype (tr {τ = base x} b₁<:b₂ b₂<:b₃) = trans (no-base-subtype b₁<:b₂) (no-base-subtype b₂<:b₃)
  no-base-subtype (tr {τ = τ ⇒ τ₁} b₁<:b₂ b₂<:b₃) = {!!}
  no-base-subtype (tr {τ = □ τ} b₁<:b₂ b₂<:b₃) = {!!}

  <:-Dec : Decidable _<:_
  <:-Dec (base b₁) (base b₂) with DecB b₁ b₂
  ... | no b₁≢b₂ = no (λ b₁<:b₂ → {!!})
  ... | true because proof₁ = {!!}
  <:-Dec (base x) (τ ⇒ τ₁) = {!!}
  <:-Dec (base x) (□ τ) = {!!}
  <:-Dec (σ ⇒ σ₁) (base x) = {!!}
  <:-Dec (σ ⇒ σ₁) (τ ⇒ τ₁) = {!!}
  <:-Dec (σ ⇒ σ₁) (□ τ) = {!!}
  <:-Dec (□ σ) (base x) = {!!}
  <:-Dec (□ σ) (τ ⇒ τ₁) = {!!}
  <:-Dec (□ σ) (□ τ) = {!!}

  data _⊢_ː_ : Ctx n → Term n → Type B → Set₁ where
    sub : {t : Term n} {σ τ : Type B} → (Γ ⊢ t ː σ) → (σ <: τ) → Γ ⊢ t ː τ
    var : (x : Fin n) → Γ ⊢ var x ː (Γ ! x)
    lam : {t : Term (suc n)} {τ₁ τ₂ : Type B} → (Γ ,, τ₁ ⊢ t ː τ₂) → (Γ ⊢ ƛ τ₁ t ː (τ₁ ⇒ τ₂))
    app : {σ τ : Type B} {t₁ t₂ : Term n} → (Γ ⊢ t₁ ː σ ⇒ τ) → (Γ ⊢ t₂ ː σ) → (Γ ⊢ t₁ ∙ t₂ ː τ)
    con : (c : C) → Γ ⊢ con c ː CTy c

  data _⊬_ : Ctx n → Term n → Set₁ where
    lam : {t : Term (suc n)} (σ : Type B) → (Γ ,, σ ⊬ t) → (Γ ⊬ ƛ σ t)

  ⊬⇒¬⊢ : {t : Term n} → (Γ ⊬ t) → ¬ (Σ[ τ ∈ Type B ] (Γ ⊢ t ː τ))
  ⊬⇒¬⊢ (lam σ pf) (τ , sub Γ⊢ƛσt:τ₁ τ₂<:τ) = ⊬⇒¬⊢ pf ({!!} , {!!})
  ⊬⇒¬⊢ (lam σ pf) ((.σ ⇒ τ) , lam Γ⊢ƛσt:τ) = ⊬⇒¬⊢ pf (τ , Γ⊢ƛσt:τ)

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
  infer Γ (con x) = {!!}
