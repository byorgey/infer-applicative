  infix 1 _◃_

  data _◃_ : Type B → Type B → Set where
    rfl : {τ : Type B} → τ ◃ τ
    box : {σ τ : Type B} → (σ ◃ τ) → □ σ ◃ □ τ
    arr : {σ₁ σ₂ τ₁ τ₂ : Type B} → (τ₁ ◃ σ₁) → (σ₂ ◃ τ₂) → (σ₁ ⇒ σ₂ ◃ τ₁ ⇒ τ₂)
    pureR : {σ τ : Type B} → (σ ◃ τ) → σ ◃ □ τ
    pureL : {σ τ : Type B} → (□ σ ◃ τ) → σ ◃ τ
    ap : {σ₁ σ₂ τ : Type B} → (□ σ₁ ⇒ □ σ₂ ◃ τ) → (□ (σ₁ ⇒ σ₂) ◃ τ)

  -- Oops, this version is actually incomplete!  Can't prove anything of the form
  -- □ □ σ ◃ τ₁ ⇒ τ₂ .
  wrong : { σ τ₁ τ₂ : Type B } → ¬ (□ □ σ ◃ τ₁ ⇒ τ₂)
  wrong (pureL prf) = wrong prf

  -- But in fact things of this form can be proved with <: .
  right : { σ₁ σ₂ : Type B } → □ □ (σ₁ ⇒ σ₂) <: □ □ σ₁ ⇒ □ □ σ₂
  right = tr (box ap) ap

  ◃-incomplete : ¬ ({σ τ : Type B} → σ <: τ → σ ◃ τ)
  ◃-incomplete all = wrong (all right)

  -- Adding apR would help with this example but it would only take us
  -- so far.

  -- My original version of the rules had the ap rule operate on □^n
  -- (σ₁ ⇒ σ₂) which would solve the problem, but I didn't like that.
  -- I thought adding ap would solve things but it actually gets stuck
  -- on multiple boxes.

  -- Broken attempts at admissibility of transitivity below.


  ◃-trans : {σ τ υ : Type B} → σ ◃ τ → τ ◃ υ → σ ◃ υ
  ◃-trans-□ : {σ τ υ : Type B} → σ ◃ τ → □ τ ◃ υ → □ σ ◃ υ

  ◃-trans-□ σ◃τ rfl = box σ◃τ
  ◃-trans-□ σ◃τ (box τ◃υ₁) = box (◃-trans σ◃τ τ◃υ₁ )
  ◃-trans-□ σ◃τ₁ (pureR □τ₁◃τ) = pureR (◃-trans-□ σ◃τ₁ □τ₁◃τ)
  ◃-trans-□ σ◃τ (pureL □□τ◃υ) = ◃-trans-□ (pureR σ◃τ) □□τ◃υ
  ◃-trans-□ σ◃σ₁⇒σ₂ (ap □σ₁⇒□σ₂◃υ) = {!!}
    -- ◃-trans (◃-trans (box σ◃σ₁⇒σ₂) (ap rfl)) □σ₁⇒□σ₂◃υ

    -- (box (arr rfl pureR)) ; (ap rfl)
    -- □ (σ ⇒ τ) ◃ □ (σ ⇒ □ τ)  ;  □ (σ ⇒ □ τ) ◃ □ σ ⇒ □ □ τ

    -- □ (σ ⇒ τ) ◃ □ σ ⇒ □ □ τ
    -- ap (arr  )

  ◃-trans rfl τ◃υ = τ◃υ
  ◃-trans (box σ◃τ) □τ◃υ = ◃-trans-□ σ◃τ □τ◃υ
  ◃-trans (arr τ₁◃σ₁ σ₂◃τ₂) τ₁⇒τ₂◃υ = {!!}
  ◃-trans (pureR σ◃τ) τ◃υ = ◃-trans σ◃τ (pureL τ◃υ)
  ◃-trans (pureL σ◃τ) τ◃υ = pureL (◃-trans σ◃τ τ◃υ)
  ◃-trans (ap σ◃τ) τ◃υ = ap (◃-trans σ◃τ τ◃υ)
