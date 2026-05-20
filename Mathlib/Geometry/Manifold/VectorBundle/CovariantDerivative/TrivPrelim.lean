/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
public import Mathlib.Geometry.Manifold.Notation

/-!
# Supporting lemmas for CovariantDerivative.Basic trivialization stuff

TODO: PR all this to appropriate places.

-/

@[expose] public section

open Bundle Filter Module Topology Set

open scoped Bundle Manifold ContDiff



variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  -- `F` model fiber
  (n : WithTop ℕ∞)
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [FiberBundle F V]

@[simp]
lemma _root_.mdifferentiableAt_total_trivial_iff {s : M → F} {x : M} :
    MDiffAt (T% s) x ↔ MDiffAt s x := by
  rw [mdifferentiableAt_section I]
  simp

@[simp]
lemma _root_.mdifferentiableAt_section_trivial_iff {σ : (x : M) → Trivial M F x} {x : M} :
    MDiffAt (T% σ) x ↔ MDifferentiableAt I 𝓘(𝕜, F) σ x := by
  rw [mdifferentiableAt_section I]
  simp

noncomputable def _root_.Bundle.vert (v : TotalSpace F V) :
    Submodule 𝕜 (TangentSpace (I.prod 𝓘(𝕜, F)) v) :=
  (mfderiv (I.prod 𝓘(𝕜, F)) I Bundle.TotalSpace.proj v).ker
