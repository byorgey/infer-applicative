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

base-inj : {B : Set} {b₁ b₂ : B} → base b₁ ≡ base b₂ → b₁ ≡ b₂
base-inj refl = refl

⇒-inj : {B : Set} {τ₁₁ τ₁₂ τ₂₁ τ₂₂ : Type B} → ((τ₁₁ ⇒ τ₁₂) ≡ (τ₂₁ ⇒ τ₂₂)) → (τ₁₁ ≡ τ₂₁) × (τ₁₂ ≡ τ₂₂)
⇒-inj refl = refl , refl

□-inj : {B : Set} {τ₁ τ₂ : Type B} → (□ τ₁ ≡ □ τ₂) → (τ₁ ≡ τ₂)
□-inj refl = refl

infix 2 _⇒_
infix 30 □_

module Infer (B : Set) (DecB : Decidable {A = B} _≡_) (C : Set) (CTy : C → Type B) where

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
    arr : {τ₁ τ₂ σ₁ σ₂ : Type B} → (τ₁ <: σ₁) → (σ₂ <: τ₂) → (σ₁ ⇒ σ₂ <: τ₁ ⇒ τ₂)
    box : {σ τ : Type B} → (σ <: τ) → (□ σ <: □ τ)
    pure : {τ : Type B} → τ <: □ τ
    ap : {σ τ : Type B} → □ (σ ⇒ τ) <: □ σ ⇒ □ τ

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

  -- Ideally should prove   Decidable {A = Type B} _≡_  instead
  _Ty≟_ : (τ₁ τ₂ : Type B) → (τ₁ ≡ τ₂) ⊎ (τ₁ ≢ τ₂)
  base b₁ Ty≟ base b₂ with DecB b₁ b₂
  ... | no ¬a = inj₂ (λ eq → ¬a (base-inj eq))
  ... | yes eq = inj₁ (cong base eq)
  base _ Ty≟ (_ ⇒ _) = inj₂ (λ ())
  base _ Ty≟ (□ _) = inj₂ (λ ())
  (_ ⇒ _) Ty≟ base _ = inj₂ (λ ())
  (τ₁₁ ⇒ τ₁₂) Ty≟ (τ₂₁ ⇒ τ₂₂) with τ₁₁ Ty≟ τ₂₁ | τ₁₂ Ty≟ τ₂₂
  ... | inj₁ refl | inj₁ refl = inj₁ refl
  ... | inj₁ refl | inj₂ τ₁₂≢τ₂₂ = inj₂ (λ eq → τ₁₂≢τ₂₂ (proj₂ (⇒-inj eq)))
  ... | inj₂ τ₁₁≢τ₂₁ | pf2 = inj₂ (λ eq → τ₁₁≢τ₂₁ (proj₁ (⇒-inj eq)))
  (_ ⇒ _) Ty≟ (□ _) = inj₂ (λ ())
  (□ _) Ty≟ base _ = inj₂ (λ ())
  (□ _) Ty≟ (_ ⇒ _) = inj₂ (λ ())
  (□ τ₁) Ty≟ (□ τ₂) with τ₁ Ty≟ τ₂
  ... | inj₁ refl = inj₁ refl
  ... | inj₂ τ₁≢τ₂ = inj₂ (λ eq → τ₁≢τ₂ (□-inj eq))

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
