module InferApplicative (B : Set) (DecB : DecidableEquality B) (C : Set) where

variable
  n : ℕ

-- ------------------------------------------------------------
-- -- Terms + contexts
-- ------------------------------------------------------------

-- data Term : ℕ → Set₁ where
--   var : Fin n → Term n
--   ƛ : Ty → Term (suc n) → Term n
--   _∙_ : Term n → Term n → Term n
--   con : C → Term n

-- data Ctx : ℕ → Set₁ where
--   ∅ : Ctx 0
--   _,,_ : Ctx n → Ty → Ctx (suc n)

-- variable
--   Γ : Ctx n

-- _!_ : Ctx n → Fin n → Ty
-- (_ ,, x) ! zero = x
-- (Γ ,, x) ! suc i = Γ ! i

-- infix 1 _⊢_ː_
-- infix 1 _⊬_
-- infix 2 _,,_

-- ------------------------------------------------------------
-- -- Typing and untyping
-- ------------------------------------------------------------

-- data _⊢_ː_ : Ctx n → Term n → Ty → Set₁ where
--   sub : {t : Term n} {σ τ : Ty} → (Γ ⊢ t ː σ) → (σ <: τ) → Γ ⊢ t ː τ
--   var : (x : Fin n) → Γ ⊢ var x ː (Γ ! x)
--   lam : {t : Term (suc n)} {τ₁ τ₂ : Ty} → (Γ ,, τ₁ ⊢ t ː τ₂) → (Γ ⊢ ƛ τ₁ t ː (τ₁ ⇒ τ₂))
--   app : {σ τ : Ty} {t₁ t₂ : Term n} → (Γ ⊢ t₁ ː σ ⇒ τ) → (Γ ⊢ t₂ ː σ) → (Γ ⊢ t₁ ∙ t₂ ː τ)
--   con : (c : C) → Γ ⊢ con c ː CTy c

-- data _⊬_ : Ctx n → Term n → Set₁ where
--   lam : {t : Term (suc n)} (σ : Ty) → (Γ ,, σ ⊬ t) → (Γ ⊬ ƛ σ t)

-- -- ⊬⇒¬⊢ : {t : Term n} → (Γ ⊬ t) → ¬ (Σ[ τ ∈ Ty ] (Γ ⊢ t ː τ))
-- -- ⊬⇒¬⊢ (lam σ pf) (τ , sub Γ⊢ƛσt:τ₁ τ₂<:τ) = ⊬⇒¬⊢ pf (σ , {!!})
-- -- ⊬⇒¬⊢ (lam σ pf) ((.σ ⇒ τ) , lam Γ⊢ƛσt:τ) = ⊬⇒¬⊢ pf (τ , Γ⊢ƛσt:τ)

------------------------------------------------------------
-- Inference algorithm
------------------------------------------------------------

-- infer : (Γ : Ctx n) → (t : Term n) → (Σ[ τ ∈ Ty ] (Γ ⊢ t ː τ)) ⊎ (Γ ⊬ t)
-- infer Γ (var x) = inj₁ (Γ ! x , var x)
-- infer Γ (ƛ σ t) with infer (Γ ,, σ) t
-- ... | inj₁ (τ , Γ,σ⊢t:τ ) = inj₁ ((σ ⇒ τ) , lam Γ,σ⊢t:τ)
-- ... | inj₂ pf = inj₂ (lam _ pf)
-- infer Γ (t₁ ∙ t₂) with infer Γ t₁ | infer Γ t₂
-- ... | inj₁ ((σ ⇒ τ) , Γ⊢t₁:σ⇒τ) | inj₁ (τ₂ , Γ⊢t₂:τ₂) = {!!} -- with σ Ty≟ τ₂
-- -- infer Γ (t₁ ∙ t₂) | inj₁ ((σ ⇒ τ) , Γ⊢t₁:σ⇒τ) | inj₁ (τ₂ , Γ⊢t₂:τ₂) | eq = ?
-- -- infer Γ (t₁ ∙ t₂) | inj₁ (base x , Γ⊢t₁:τ₁) | inj₁ (τ₂ , Γ⊢t₂:τ₂) = {!!}
-- ... | inj₁ (□ τ₁ , Γ⊢t₁:τ₁) | inj₁ (τ₂ , Γ⊢t₂:τ₂) = {!!}
-- ... | inj₁ x | inj₂ y = {!!}
-- ... | inj₂ y₁ | y = {!!}
-- infer Γ (con x) = inj₁ (CTy x , con x)

-- Make versions of type system with and without subtyping.  Should
-- be able to use subtyping relation to elaborate terms to insert
-- appropriate constants (pure, ap).
