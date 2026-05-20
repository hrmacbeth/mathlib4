/-
Copyright (c) 2026 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Patrick Massot, Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.OneJetBundle

/-!
# Operation on one-jets defined by a covariant derivative

-/
open Bundle NormedSpace
open scoped Manifold ContDiff Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

@[expose] public noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
  [FiberBundle F V]

-- descends from value of `cov` on sections,
-- uniquely determined in order to make `CovariantDerivative.der_section` true
def CovariantDerivative.der (cov : CovariantDerivative I F V) (x : M) :
    oneJetSpace I F V x →ₗ[𝕜] TangentSpace I x →L[𝕜] V x where
  toFun := sorry
  map_add' := sorry
  map_smul' := sorry

variable (cov : CovariantDerivative I F V)

theorem CovariantDerivative.der_inclAtZero [VectorBundle 𝕜 F V] (x : M) :
    cov.der x ∘ₗ inclAtZero I F V x = LinearMap.id :=
  sorry

theorem CovariantDerivative.der_inclAtZero_apply [VectorBundle 𝕜 F V] (x : M)
    (j : TangentSpace I x →L[𝕜] V x) :
    cov.der x (inclAtZero I F V x j) = j :=
  sorry

theorem CovariantDerivative.der_section (σ : Π x, V x) {x : M}
    (hσx : MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (T% σ) x) :
    cov.der x (oneJet σ hσx) = cov σ x := by
  sorry

def CovariantDerivative.secₗ [VectorBundle 𝕜 F V] (cov : CovariantDerivative I F V) (x : M) :
    V x →ₗ[𝕜] oneJetSpace I F V x :=
  (oneJetSplittingEquiv I F V x ⟨cov.der x, cov.der_inclAtZero x⟩).1

theorem CovariantDerivative.zerothPart_secₗ [VectorBundle 𝕜 F V] (cov : CovariantDerivative I F V)
    (x : M) :
    zerothPart I F V x ∘ₗ cov.secₗ x = LinearMap.id :=
  (oneJetSplittingEquiv I F V x ⟨cov.der x, cov.der_inclAtZero x⟩).2

theorem CovariantDerivative.zerothPart_secₗ_apply [VectorBundle 𝕜 F V]
    (cov : CovariantDerivative I F V) (x : M) (v₀ : V x) :
    zerothPart I F V x (cov.secₗ x v₀) = v₀ :=
  congr($(cov.zerothPart_secₗ x) v₀)

theorem CovariantDerivative.der_secₗ [VectorBundle 𝕜 F V] (cov : CovariantDerivative I F V)
    (x : M) :
    cov.der x ∘ₗ cov.secₗ x = 0 :=
  sorry

theorem CovariantDerivative.der_secₗ_apply [VectorBundle 𝕜 F V] (cov : CovariantDerivative I F V)
    (x : M) (v₀ : V x) :
    cov.der x (cov.secₗ x v₀) = 0 :=
  congr($(cov.der_secₗ x) v₀)

/-- Given `v₀` in the fibre over `x` of `V`, the (unique) 1-jet extension of `v₀` which is constant
with respect to the covariant derivative `cov`. -/
def CovariantDerivative.sec [VectorBundle 𝕜 F V] (cov : CovariantDerivative I F V)
    (x : M) (v₀ : V x) :
    oneJetOver I F V v₀ :=
  have H : (cov.secₗ x v₀).1 = v₀ := cov.zerothPart_secₗ_apply x v₀
  H ▸ (cov.secₗ x v₀).2

theorem CovariantDerivative.der_sec_apply [VectorBundle 𝕜 F V] (cov : CovariantDerivative I F V)
    (x : M) (v₀ : V x) :
    cov.der x ⟨v₀, cov.sec x v₀⟩ = 0 := by
  convert cov.der_secₗ_apply x v₀
  have H : (cov.secₗ x v₀).1 = v₀ := cov.zerothPart_secₗ_apply x v₀
  change (⟨v₀, H ▸ (cov.secₗ x v₀).2⟩ : oneJetSpace I F V x) = _
  apply Sigma.ext H.symm
  simp
