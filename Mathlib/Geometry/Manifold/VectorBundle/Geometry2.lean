/-
Copyright (c) 2026 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Patrick Massot, Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-!
# Universal properties of the tangent spaces of vector bundle constructions

For example, direct sum of two vector bundles, pullback of a vector bundle, etc.
-/

open Bundle
open scoped ContDiff Manifold

variable {n : ℕ∞ω}

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] (IB : ModelWithCorners 𝕜 EB HB)
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB n B]

variable (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] {E₁ : B → Type*}
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, AddCommMonoid (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [∀ x : B, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁]
  -- [VectorBundle 𝕜 F₁ E₁]
  -- [ContMDiffVectorBundle n F₁ E₁ IB]

variable (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] {E₂ : B → Type*}
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, AddCommMonoid (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [∀ x : B, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂]
  -- [VectorBundle 𝕜 F₂ E₂]
  -- [ContMDiffVectorBundle n F₂ E₂ IB]

variable {V : Type*} [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V]

variable (x : B) (v₁ : E₁ x) (v₂ : E₂ x)
    (f₁ : V →L[𝕜] TangentSpace (IB.prod 𝓘(𝕜, F₁)) (M := TotalSpace F₁ E₁) ⟨x, v₁⟩)
    (f₂ : V →L[𝕜] TangentSpace (IB.prod 𝓘(𝕜, F₂)) (M := TotalSpace F₂ E₂) ⟨x, v₂⟩)
    (hf : mfderiv (IB.prod 𝓘(𝕜, F₁)) IB TotalSpace.proj ⟨x, v₁⟩ ∘L f₁
      = mfderiv (IB.prod 𝓘(𝕜, F₂)) IB TotalSpace.proj ⟨x, v₂⟩ ∘L f₂)

variable {IB F₁ F₂ x v₁ v₂}

public def glue : V →L[𝕜]
    TangentSpace (IB.prod 𝓘(𝕜, F₁ × F₂)) (M := TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂)) ⟨x, v₁, v₂⟩ :=
  have := hf
  (ContinuousLinearMap.fst _ _ _ ∘L f₁).prod <|
    (ContinuousLinearMap.snd _ _ _ ∘L f₁).prod (ContinuousLinearMap.snd _ _ _ ∘L f₂)

public theorem glue_left :
    mfderiv
      (IB.prod 𝓘(𝕜, F₁ × F₂)) (M := TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂))
      (IB.prod 𝓘(𝕜, F₁)) (M' := TotalSpace F₁ E₁)
      (fun v ↦ ⟨v.1, v.2.1⟩)
      ⟨x, v₁, v₂⟩
    ∘L glue f₁ f₂ hf = f₁ := by
  have H : MDifferentiableAt (IB.prod 𝓘(𝕜, F₁ × F₂)) (M := TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂))
      (IB.prod 𝓘(𝕜, F₁)) (M' := TotalSpace F₁ E₁) (fun v ↦ ⟨v.1, v.2.1⟩) ⟨x, v₁, v₂⟩ := sorry
  rw [H.mfderiv, writtenInExtChartAt]
  simp_rw [FiberBundle.extChartAt]
  simp only [extChartAt, OpenPartialHomeomorph.extend, PartialEquiv.coe_trans,
    PartialEquiv.prod_coe, ModelWithCorners.toPartialEquiv_coe, OpenPartialHomeomorph.toFun_eq_coe,
    Function.comp_apply, PartialEquiv.refl_coe, id_eq, Trivialization.coe_coe,
    FiberBundle.prod_trivializationAt', PartialEquiv.coe_trans_symm,
    OpenPartialHomeomorph.coe_coe_symm, PartialEquiv.prod_symm, PartialEquiv.refl_symm,
    ModelWithCorners.toPartialEquiv_coe_symm, modelWithCorners_prod_coe, modelWithCornersSelf_coe,
    Trivialization.prod_apply]
  set e := chartAt HB x
  set φ₁ := trivializationAt F₁ E₁ x
  set φ₂ := trivializationAt F₂ E₂ x
  let m : EB × (F₁ × F₂) →L[𝕜] EB × F₁ :=
    (ContinuousLinearMap.id 𝕜 EB).prodMap (ContinuousLinearMap.fst _ _ _)
  conv =>
    enter [1, 1, 2]
    equals m =>
    ext1 ⟨y, v₁, v₂⟩
    simp [m]
    rw [← ModelWithCorners.toPartialEquiv_coe]
    rw [← PartialEquiv.eq_symm_apply]
    rw [← OpenPartialHomeomorph.eq_symm_apply]
    dsimp
    set b := e.symm (IB.symm y)
    rw [← Prod.mk.injEq]
    conv_rhs => rw [← φ₁.apply_mk_symm sorry]
    -- set membership
    sorry
    sorry
    sorry
    sorry
  rw [ContinuousLinearMap.fderivWithin _ sorry]
  rfl

-- the statement of this lemma exploits the under-the-hood identification of the tangent space with
-- the model, so it should not be made public
theorem aux2 :
    mfderiv
      (IB.prod 𝓘(𝕜, F₁ × F₂)) (M := TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂))
      (IB.prod 𝓘(𝕜, F₂)) (M' := TotalSpace F₂ E₂)
      (fun v ↦ ⟨v.1, v.2.2⟩)
      ⟨x, v₁, v₂⟩
    = (ContinuousLinearMap.id 𝕜 EB).prodMap (ContinuousLinearMap.snd 𝕜 F₁ F₂) := by
  have H : MDifferentiableAt (IB.prod 𝓘(𝕜, F₁ × F₂)) (M := TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂))
      (IB.prod 𝓘(𝕜, F₂)) (M' := TotalSpace F₂ E₂) (fun v ↦ ⟨v.1, v.2.2⟩) ⟨x, v₁, v₂⟩ := by
    sorry
  rw [H.mfderiv]
  set m : EB × (F₁ × F₂) →L[𝕜] EB × F₂ :=
    (ContinuousLinearMap.id 𝕜 EB).prodMap (ContinuousLinearMap.snd _ _ _)
  rw [fderivWithin_congr' (f := m), m.fderivWithin]
  · sorry
  · rw [writtenInExtChartAt]
    simp_rw [FiberBundle.extChartAt, Set.eqOn_range]
    ext1 ⟨y, v₁, v₂⟩
    simp [m, -Prod.mk.injEq]
    set e := chartAt HB x
    set φ₁ := trivializationAt F₁ E₁ x
    set φ₂ := trivializationAt F₂ E₂ x
    rw [IB.left_inv]
    rw [φ₂.coe_coe_fst]
    rw [e.right_inv]
    rw [φ₂.apply_mk_symm]
    sorry
    sorry
    sorry
  -- set membership
  sorry

-- the statement of this lemma exploits the under-the-hood identification of the tangent space with
-- the model, so it should not be made public
theorem aux3 :
    mfderiv (IB.prod 𝓘(𝕜, F₁)) (M := TotalSpace F₁ E₁) IB TotalSpace.proj ⟨x, v₁⟩
    = ContinuousLinearMap.fst 𝕜 EB F₁ :=
  sorry

public theorem glue_right :
    mfderiv
      (IB.prod 𝓘(𝕜, F₁ × F₂)) (M := TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂))
      (IB.prod 𝓘(𝕜, F₂)) (M' := TotalSpace F₂ E₂)
      (fun v ↦ ⟨v.1, v.2.2⟩)
      ⟨x, v₁, v₂⟩
    ∘L glue f₁ f₂ hf = f₂ := by
  rw [aux2]
  ext v
  dsimp [glue]
  rw [← aux3 (IB := IB) (v₁ := v₁)]
  conv =>
    enter [1, 2, 1, 1]
    apply hf
  rw [aux3 (IB := IB) (v₁ := v₂)]
  rfl
