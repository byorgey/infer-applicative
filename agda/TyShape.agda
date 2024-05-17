-- Old code about TyShape.  Simpler to just define box erasure as Ty → Ty instead
-- of making up an entirely new type.

data TyShape : Set where
  base : B → TyShape
  _⇒_ : TyShape → TyShape → TyShape

-- A ShapedTy is a type, but indexed by its shape.  Not sure whether we really need this.
data ShapedTy : TyShape → Set where
  base : (b : B) → ShapedTy (base b)
  _⇒_ : {l : TyShape} → ShapedTy l → {r : TyShape} → ShapedTy r → ShapedTy (l ⇒ r)
  □_ : {t : TyShape} → ShapedTy t → ShapedTy t

⟦_⟧ : {t : TyShape} → ShapedTy t → Ty
⟦ base b ⟧ = base b
⟦ l ⇒ r ⟧ = ⟦ l ⟧ ⇒ ⟦ r ⟧
⟦ □ t ⟧ = □ ⟦ t ⟧

⟨_⟩ : Ty → TyShape
⟨ base b ⟩ = base b
⟨ σ ⇒ τ ⟩ = ⟨ σ ⟩ ⇒ ⟨ τ ⟩
⟨ □ τ ⟩ = ⟨ τ ⟩

⟪_⟫ : (τ : Ty) → ShapedTy ⟨ τ ⟩
⟪ base b ⟫ = base b
⟪ σ ⇒ τ ⟫ = ⟪ σ ⟫ ⇒ ⟪ τ ⟫
⟪ □ τ ⟫ = □ ⟪ τ ⟫

_≡⟦⟪⟫⟧ : (τ : Ty) → τ ≡ ⟦ ⟪ τ ⟫ ⟧
base b ≡⟦⟪⟫⟧  = refl
(σ ⇒ τ) ≡⟦⟪⟫⟧  = cong₂ _⇒_ (σ ≡⟦⟪⟫⟧) (τ ≡⟦⟪⟫⟧)
(□ τ) ≡⟦⟪⟫⟧ = cong □_ (τ ≡⟦⟪⟫⟧)

_≡⟨⟦⟧⟩ : {s : TyShape} → (t : ShapedTy s) → s ≡ ⟨ ⟦ t ⟧ ⟩
base b ≡⟨⟦⟧⟩ = refl
(l ⇒ r) ≡⟨⟦⟧⟩ = cong₂ _⇒_ (l ≡⟨⟦⟧⟩) (r ≡⟨⟦⟧⟩)
□ t ≡⟨⟦⟧⟩ = t ≡⟨⟦⟧⟩

-- soundness?  Not sure how to express this so it typechecks.  Tried using heterogeneous equality
-- but not yet able to figure out how to make the node case go through.

-- _≅⟪⟦⟧⟫ : {s : TyShape} → (t : ShapedTy s) → t ≅ ⟪ ⟦ t ⟧ ⟫
-- base b ≅⟪⟦⟧⟫ = refl
-- _≅⟪⟦⟧⟫ {node lt rt} (node l r) with l ≡⟨⟦⟧⟩
-- ... | eq = {!!}
-- box t ≅⟪⟦⟧⟫ = {!!}

-- Theorem: if σ <: τ, then σ and τ have the same underlying TyShape.

<:→⟨⟩ : {σ τ : Ty} → σ <: τ → ⟨ σ ⟩ ≡ ⟨ τ ⟩
<:→⟨⟩ rfl = refl
<:→⟨⟩ (tr σ<:τ₁ τ₁<:τ) = trans (<:→⟨⟩ σ<:τ₁) (<:→⟨⟩ τ₁<:τ)
<:→⟨⟩ (arr τ₁<:σ₁ σ₂<:τ₂) = cong₂ _⇒_ (sym (<:→⟨⟩ τ₁<:σ₁)) (<:→⟨⟩ σ₂<:τ₂)
<:→⟨⟩ (box σ<:τ) = <:→⟨⟩ σ<:τ
<:→⟨⟩ pure = refl
<:→⟨⟩ ap = refl
