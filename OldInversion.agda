  -- ⇒<:□-inv : {τ₁ τ₂ τ : Type B} → (τ₁ ⇒ τ₂ <: □ τ) → (τ₁ ⇒ τ₂ <: τ)
  -- ⇒<:□-inv (tr τ₁⇒τ₂<:τ₃ τ₃<:□τ) = {!!}
  -- ⇒<:□-inv pure = rfl

  -- <:-□-inv : {σ τ : Type B} → ¬(Σ[ σ′ ∈ Type B ] σ ≡ □ σ′) → (σ <: □ τ) → (σ <: τ)
  -- <:-□-inv {τ = τ} notbox rfl = contradiction (τ , refl) notbox
  -- <:-□-inv notbox (tr {τ = base b} σ<:b b<:□τ) with <:B-inv σ<:b
  -- ... | refl = {!!}
  -- <:-□-inv notbox (tr {τ = τ₁ ⇒ τ₂} σ<:τ₁ τ₁<:□τ) = {!!}
  -- <:-□-inv notbox (tr {τ = □ τ₁} σ<:τ₁ τ₁<:□τ) = {!!}
  -- <:-□-inv notbox (box {σ = σ₁} σ<:τ) = contradiction (σ₁ , refl) notbox
  -- <:-□-inv notbox pure = rfl

  □-<:-inv : {σ τ : Type B} → (□ σ <: □ τ) → (σ <: τ)
  □-<:-inv rfl = rfl
  □-<:-inv (tr {τ = base b} □σ<:b b<:□τ) with <:B-inv □σ<:b
  ... | ()
  □-<:-inv (tr {τ = τ₁ ⇒ τ₂} □σ<:τ₁⇒τ₂ τ₁⇒τ₂<:□τ) = {!tr □σ<:τ₁⇒τ₂ (<:-□-inv _ τ₁⇒τ₂<:□τ)!}
  □-<:-inv (tr {τ = □ τ₁} □σ<:□τ₁ □τ₁<:□τ) = tr (□-<:-inv □σ<:□τ₁) (□-<:-inv □τ₁<:□τ)
  □-<:-inv (box prf) = prf
  □-<:-inv pure = pure
