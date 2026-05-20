/-
Copyright (c) 2026 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Patrick Massot, Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.Notation

/-!
# The geometry of the total space of a vector bundle

-/

open Bundle Filter Module Topology Set
open scoped Bundle Manifold ContDiff

attribute [simp] Bundle.Trivialization.coe_linearMapAt_of_mem

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

@[expose] public section -- TODO: think if we want to expose all definitions!

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {x : M}

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  -- `F` model fiber
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x : M, TopologicalSpace (V x)] [FiberBundle F V]
  -- `V` vector bundle

-- move this
theorem TotalSpace.mdifferentiable_add :
    letI a (z : TotalSpace (F × F) (V ×ᵇ V)) : TotalSpace F V := ⟨z.1, z.2.1 + z.2.2⟩
    MDifferentiable (I.prod 𝓘(𝕜, F × F)) (I.prod 𝓘(𝕜, F)) a := by
  sorry

-- move this
theorem TotalSpace.mdifferentiable_neg :
    letI m (z : TotalSpace F V) : TotalSpace F V := ⟨z.1, - z.2⟩
    MDifferentiable (I.prod 𝓘(𝕜, F)) (I.prod 𝓘(𝕜, F)) m := by
  sorry

-- move this
theorem TotalSpace.mdifferentiable_smul (c : 𝕜) :
    letI m (z : TotalSpace F V) : TotalSpace F V := ⟨z.1, c • z.2⟩
    MDifferentiable (I.prod 𝓘(𝕜, F)) (I.prod 𝓘(𝕜, F)) m := by
  sorry

-- move this
theorem TotalSpace.mdifferentiable_incl :
    letI i (x : M) : TotalSpace F V := ⟨x, 0⟩
    MDifferentiable I (I.prod 𝓘(𝕜, F)) i :=
  sorry

-- move this
variable (F) in
noncomputable def VectorBundle.vert [VectorBundle 𝕜 F V] :
    ∀ (v : TotalSpace F V), V v.proj →L[𝕜] TangentSpace (I.prod 𝓘(𝕜, F)) v
  | ⟨x, v₀⟩ =>
    let a (w₀ : V x) : TotalSpace F V := ⟨x, w₀⟩
    -- morally we want the differential of `a` at `⟨x, v₀⟩`,
    -- which is a continuous linear map from `V x` (identified with `TangentSpace 𝓘(𝕜, F) v₀`)
    -- to `TangentSpace (I.prod 𝓘(𝕜, F)) ⟨x, v₀⟩`,
    -- but we haven't got the `𝓘(𝕜, F)`-manifold structure on `V x` in the library,
    -- nor the canonical identification of its tangent spaces with `V x`
    let ψ := (trivializationAt F V x).continuousLinearEquivAt 𝕜 x
      (FiberBundle.mem_baseSet_trivializationAt' x)
    let A : F → TotalSpace F V := a ∘ ψ.symm
    let b : F →L[𝕜] TangentSpace (I.prod 𝓘(𝕜, F)) _ :=
      mfderiv 𝓘(𝕜, F) (I.prod 𝓘(𝕜, F)) A (ψ v₀) ∘L
        (NormedSpace.fromTangentSpace (ψ v₀)).symm.toContinuousLinearMap
    b ∘L ψ

variable (F V) in
noncomputable def FiberBundle.horizZero (x : M) :
    TangentSpace I x →L[𝕜] TangentSpace (I.prod 𝓘(𝕜, F)) (⟨x, 0⟩ : TotalSpace F V) :=
  let i (y : M) : TotalSpace F V := ⟨y, 0⟩
  mfderiv% i x

variable (F V) in
noncomputable def VectorBundle.vertZero (x : M) :
    TangentSpace (I.prod 𝓘(𝕜, F)) (⟨x, 0⟩ : TotalSpace F V) →L[𝕜] V x :=
  sorry

theorem VectorBundle.mfderiv_proj_comp_vert [VectorBundle 𝕜 F V] :
    ∀ (v : TotalSpace F V),
    mfderiv (I.prod 𝓘(𝕜, F)) I Bundle.TotalSpace.proj v ∘L VectorBundle.vert F v = 0
  | ⟨x, v₀⟩ => by
    let a (w₀ : V x) : TotalSpace F V := ⟨x, w₀⟩
    let ψ := (trivializationAt F V x).continuousLinearEquivAt 𝕜 x
      (FiberBundle.mem_baseSet_trivializationAt' x)
    let A : F → TotalSpace F V := a ∘ ψ.symm
    letI b : F →L[𝕜] TangentSpace (I.prod 𝓘(𝕜, F)) _ :=
      mfderiv 𝓘(𝕜, F) (I.prod 𝓘(𝕜, F)) A (ψ v₀) ∘L
        (NormedSpace.fromTangentSpace (ψ v₀)).symm.toContinuousLinearMap
    change _ ∘L (b ∘L ψ.toContinuousLinearMap) = _
    rw [ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc]
    have h : A (ψ v₀) = ⟨x, v₀⟩ := by simp [A, a]
    let p : TotalSpace F V → M := Bundle.TotalSpace.proj
    conv =>
      enter [1, 1, 1]
      change mfderiv (I.prod 𝓘(𝕜, F)) I p _
      equals mfderiv (I.prod 𝓘(𝕜, F)) I p (A (ψ v₀)) => rw [h]
    conv =>
      enter [1, 1]
      equals mfderiv 𝓘(𝕜, F) I (p ∘ A) (ψ v₀) =>
        refine (mfderiv_comp (g := p) (f := A) (x := ψ v₀) ?_ ?_).symm
        · exact mdifferentiableAt_proj V
        unfold A a
        sorry -- differentiability
    conv =>
      enter [1, 1]
      change mfderiv 𝓘(𝕜, F) I (fun _ ↦ x) (ψ v₀)
    rw [mfderiv_const]
    simp


theorem FiberBundle.mfderiv_proj_comp_horizZero (x : M) :
    mfderiv (I.prod 𝓘(𝕜, F)) I Bundle.TotalSpace.proj ⟨x, 0⟩ ∘L FiberBundle.horizZero F V x
    = ContinuousLinearMap.id 𝕜 (TangentSpace I x) := by
  unfold FiberBundle.horizZero
  letI p : TotalSpace F V → M := Bundle.TotalSpace.proj
  let i (y : M) : TotalSpace F V := ⟨y, 0⟩
  have hi : MDiffAt i x := TotalSpace.mdifferentiable_incl ..
  rw [← mfderiv_comp _ (mdifferentiableAt_proj V) hi]
  apply mfderiv_id

variable (I F V) in
noncomputable def tangentBundleSplittingEquiv
    [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)] [VectorBundle 𝕜 F V]
    (x : M) (v₀ : V x) :
    let f := VectorBundle.vert (I := I) F ⟨x, v₀⟩
    let g := mfderiv (I.prod 𝓘(𝕜, F)) I (Bundle.TotalSpace.proj (F := F) (E := V)) ⟨x, v₀⟩
    { l // l ∘ₗ f.toLinearMap = LinearMap.id }
    ≃ { l // g.toLinearMap ∘ₗ l = LinearMap.id } :=
  let f := VectorBundle.vert (I := I) F ⟨x, v₀⟩
  let g := mfderiv (I.prod 𝓘(𝕜, F)) I Bundle.TotalSpace.proj ⟨x, v₀⟩
  have hf : Function.Injective f := sorry
  have hg : Function.Surjective (g) := sorry
  have h : Function.Exact f (g) := sorry
  let e := h.splitInjectiveEquiv hg
  let e' := h.splitSurjectiveEquiv hf
  e.trans e'.symm


variable (F) in
noncomputable def differentialAtZero {x : M} (σ : Π x, V x) (hσx : σ x = 0) :
    TangentSpace I x →L[𝕜] V x :=
  VectorBundle.vertZero (F := F) (V := V) x ∘L (hσx ▸ mfderiv% (T% σ) x)

theorem differentialAtZero_smul [∀ x, ContinuousSMul 𝕜 (V x)]
    {x : M} (σ : Π x, V x) (f : M → 𝕜) (hfx : f x = 0) :
    differentialAtZero F (x := x) (f • σ) (hfx ▸ zero_smul 𝕜 (σ x):)
    = (d% f x).smulRight (σ x) := by
  sorry
