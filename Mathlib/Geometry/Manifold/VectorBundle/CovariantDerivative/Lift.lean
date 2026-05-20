/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Patrick Massot, Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Ehresmann

/-!
# Lifting vectors using covariant derivatives

TODO: add a more complete doc-string

-/

@[expose] public section

open Bundle Filter Module Topology Set

open scoped Bundle Manifold ContDiff

section
variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [FiniteDimensional 𝕜 F] [IsManifold I 1 M]
  -- {cov : (M → F) → (Π x : M, TangentSpace I x →L[𝕜] F)}
  {s : Set M} --(hcov : IsCovariantDerivativeOn F cov s)



end

section
variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [(x : M) → AddCommGroup (V x)] [(x : M) → Module 𝕜 (V x)]
  [(x : M) → TopologicalSpace (V x)] [FiberBundle F V]
  [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ (x : M), ContinuousSMul 𝕜 (V x)]
  [FiniteDimensional 𝕜 F]
  [IsManifold I 1 M] [VectorBundle 𝕜 F V] {cov : CovariantDerivative I F V}
  [ContMDiffVectorBundle 1 F V I]


@[simp]
lemma CovariantDerivative.lift_vec_mem_horiz {v : TotalSpace F V} (u : TangentSpace I v.proj) :
    cov.lift_vec v u ∈ cov.horiz v := by
  unfold horiz
  simp
  sorry

@[simp]
lemma CovariantDerivative.proj_lift_vec {v : TotalSpace F V} (u : TangentSpace I v.proj) :
    cov.proj v (cov.lift_vec v u) = 0 := by
  rw [← cov.mem_horiz_iff_proj]
  exact lift_vec_mem_horiz u

omit [CompleteSpace 𝕜]
  [FiniteDimensional 𝕜 F]
  [IsManifold I 1 M]
  [ContMDiffVectorBundle 1 F V I] in
@[simp]
lemma CovariantDerivative.mfderiv_proj_lift_vec {v : TotalSpace F V} (u : TangentSpace I v.proj) :
    mfderiv (I.prod 𝓘(𝕜, F)) I TotalSpace.proj v (cov.lift_vec v u) = u :=
  sorry

lemma CovariantDerivative.lift_vec_eq_iff {v : TotalSpace F V} (u : TangentSpace I v.proj)
    (w : TangentSpace (I.prod 𝓘(𝕜, F)) v) :
    cov.lift_vec v u = w  ↔
      cov.proj v w = 0 ∧
      mfderiv (I.prod 𝓘(𝕜, F)) I (TotalSpace.proj : TotalSpace F V → M) v w = u := by
  constructor
  · rintro rfl
    simp
  · sorry

lemma CovariantDerivative.lift_vec_eq_iff' {v : TotalSpace F V} (u : TangentSpace I v.proj)
    (w : TangentSpace (I.prod 𝓘(𝕜, F)) v) :
    cov.lift_vec v u = w  ↔
      w ∈ cov.horiz v ∧
      mfderiv (I.prod 𝓘(𝕜, F)) I (TotalSpace.proj : TotalSpace F V → M) v w = u := by
  simp [CovariantDerivative.lift_vec_eq_iff, horiz]

end
