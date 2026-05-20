/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.OneJet
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.TrivPrelim

/-!
# Covariant derivatives

TODO: add a more complete doc-string

-/

open Bundle Filter Module Topology Set
open scoped Bundle Manifold ContDiff

attribute [simp] Bundle.Trivialization.coe_linearMapAt_of_mem

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

@[expose] public section -- TODO: think if we want to expose all definitions!

variable {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {x : M}

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  -- `F` model fiber
  (n : WithTop ℕ∞)
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x : M, TopologicalSpace (V x)] [FiberBundle F V]
  -- `V` vector bundle

section horiz
namespace CovariantDerivative

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
    [IsManifold I 1 M]
    [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
    [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]

local notation "TM" => TangentSpace I


/-- Horizontal lift of a vector tangent to the base at a point in the corresponding fiber. -/
noncomputable def lift_vec [VectorBundle 𝕜 F V] (cov : CovariantDerivative I F V)
    (v : TotalSpace F V) :
    TangentSpace I v.proj →L[𝕜] TangentSpace (I.prod 𝓘(𝕜, F)) v :=
  (cov.sec v.proj v.2).1

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] [IsManifold I 1 M] [VectorBundle 𝕜 F V]
  [ContMDiffVectorBundle 1 F V I] in
theorem lift_vec_prop [VectorBundle 𝕜 F V] (cov : CovariantDerivative I F V)
    (v : TotalSpace F V) :
    mfderiv (I.prod 𝓘(𝕜, F)) I TotalSpace.proj v ∘L cov.lift_vec v
    = ContinuousLinearMap.id 𝕜 (TangentSpace I x) := by
  have : cov.lift_vec v ∈ _ := (cov.sec v.proj v.2).2
  rwa [mem_oneJetOver_iff] at this

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] [IsManifold I 1 M] [VectorBundle 𝕜 F V]
  [ContMDiffVectorBundle 1 F V I] in
theorem lift_vec_prop_apply [VectorBundle 𝕜 F V] (cov : CovariantDerivative I F V)
    (v : TotalSpace F V) (u : TangentSpace I v.proj) :
    mfderiv (I.prod 𝓘(𝕜, F)) I TotalSpace.proj v (cov.lift_vec v u)
    = u :=
  congr($(cov.lift_vec_prop v) u)


theorem der_lift_vec_apply [VectorBundle 𝕜 F V] (cov : CovariantDerivative I F V)
    (x : M) (v₀ : V x) :
    cov.der x ⟨v₀, ⟨cov.lift_vec ⟨x, v₀⟩, sorry⟩⟩ = 0 :=
  cov.der_sec_apply x v₀

noncomputable
def proj (cov : CovariantDerivative I F V) (v : TotalSpace F V) :
    TangentSpace (I.prod 𝓘(𝕜, F)) v →L[𝕜] V v.proj :=
  have H : (mfderiv (I.prod 𝓘(𝕜, F)) I TotalSpace.proj v).toLinearMap ∘ₗ cov.lift_vec v
    = LinearMap.id := congr(ContinuousLinearMap.toLinearMap $(cov.lift_vec_prop v))
  let a := (tangentBundleSplittingEquiv I F V v.1 v.2).symm ⟨cov.lift_vec v, H⟩
  have : T2Space (TangentSpace (I.prod 𝓘(𝕜, F)) v) := sorry
  have : FiniteDimensional 𝕜 (TangentSpace (I.prod 𝓘(𝕜, F)) v) := sorry
  a.1.toContinuousLinearMap

def proj_prop (cov : CovariantDerivative I F V) (v : TotalSpace F V) :
    cov.proj v ∘ₗ (VectorBundle.vert (I := I) F v).toLinearMap = LinearMap.id :=
  have H : (mfderiv (I.prod 𝓘(𝕜, F)) I TotalSpace.proj v).toLinearMap ∘ₗ cov.lift_vec v
    = LinearMap.id := congr(ContinuousLinearMap.toLinearMap $(cov.lift_vec_prop v))
  let a := (tangentBundleSplittingEquiv I F V v.1 v.2).symm ⟨cov.lift_vec v, H⟩
  a.2

omit [FiniteDimensional 𝕜 F]
  [IsManifold I 1 M]
  [ContMDiffVectorBundle 1 F V I] in
theorem proj_prop' (cov : CovariantDerivative I F V) (v : TotalSpace F V) :
    cov.proj v ∘L VectorBundle.vert (I := I) F v = ContinuousLinearMap.id 𝕜 _ :=
  ContinuousLinearMap.coe_injective <| cov.proj_prop v

theorem projsdjkl (cov : CovariantDerivative I F V) {x : M} (v₀ : V x)
    (φ : TangentSpace I x →L[𝕜] TangentSpace (I.prod 𝓘(𝕜, F)) (⟨x, v₀⟩ : TotalSpace F V))
    (hφ : φ ∈ oneJetOver I F V ⟨x, v₀⟩) :
    (cov.der x) ⟨v₀, ⟨φ, hφ⟩⟩ = cov.proj ⟨x, v₀⟩ ∘SL φ := by
  rw [mem_oneJetOver_iff] at hφ
  sorry

noncomputable def horiz (cov : CovariantDerivative I F V) (v : TotalSpace F V) :
    Submodule 𝕜 (TangentSpace (I.prod 𝓘(𝕜, F)) v) :=
  (cov.proj v).ker

omit [FiniteDimensional 𝕜 F] [IsManifold I 1 M] [ContMDiffVectorBundle 1 F V I] in
lemma mem_horiz_iff_proj {cov : CovariantDerivative I F V} {v : TotalSpace F V}
    (u : TangentSpace (I.prod 𝓘(𝕜, F)) v) :
    u ∈ cov.horiz v ↔ cov.proj v u = 0 := by
  simp [horiz]

omit [ContMDiffVectorBundle 1 F V I] in
lemma horiz_vert_direct_sum [ContMDiffVectorBundle 1 F V I]
    (cov : CovariantDerivative I F V) (v : TotalSpace F V) :
    IsCompl (cov.horiz v) (vert v) := by
  sorry

variable (cov : CovariantDerivative I F V)

theorem projsdjkl' {x : M} (v₀ : V x)
    (j : oneJetOver I F V ⟨x, v₀⟩) :
    (cov.der x) ⟨v₀, j⟩ = cov.proj ⟨x, v₀⟩ ∘SL j.1 :=
  cov.projsdjkl v₀ j.1 j.2

theorem projsdjkl'' {x : M} (j : oneJetSpace I F V x) :
    (cov.der x) j = cov.proj ⟨x, j.1⟩ ∘SL j.2.1 :=
  cov.projsdjkl' j.1 j.2

variable {cov}

lemma proj_mderiv {σ : Π x : M, V x} (x : M)
    (hσ : MDiffAt (T% σ) x) :
    cov σ x = cov.proj (σ x) ∘L (mfderiv I (I.prod 𝓘(𝕜, F)) (T% σ) x) := by
  rw [← CovariantDerivative.der_section _ _ hσ, projsdjkl'']
  rfl

lemma mem_horiz_iff_exists [FiniteDimensional 𝕜 E]
    {cov : CovariantDerivative I F V} {v : TotalSpace F V}
    (w : TangentSpace (I.prod 𝓘(𝕜, F)) v) :
    letI u := mfderiv (I.prod 𝓘(𝕜, F)) I TotalSpace.proj v w
    w ∈ cov.horiz v ↔ ∃ σ : Π x, V x,
                        MDiffAt (T% σ) v.proj ∧
                        σ v.proj = v ∧
                        mfderiv% (T% σ) v.proj u = w ∧
                        cov σ v.proj u = 0
    := by
  sorry

end CovariantDerivative
end horiz


end
