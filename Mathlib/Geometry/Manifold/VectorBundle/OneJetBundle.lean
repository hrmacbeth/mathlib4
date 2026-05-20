/-
Copyright (c) 2026 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Patrick Massot, Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Geometry.Manifold.VectorBundle.Geometry1
public import Mathlib.Geometry.Manifold.VectorBundle.Geometry2

/-!
# The one-jet bundle of a vector bundle

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


/-! ## The one-jet bundle -/


variable (I F V) in
noncomputable def oneJetOver (v : TotalSpace F V) :
    AffineSubspace 𝕜 (TangentSpace I v.proj →L[𝕜] TangentSpace (I.prod 𝓘(𝕜, F)) v) :=
  let p : TotalSpace F V → M := Bundle.TotalSpace.proj
  let P : TangentSpace (I.prod 𝓘(𝕜, F)) v →ₗ[𝕜] TangentSpace I v.proj :=
    (mfderiv (I.prod 𝓘(𝕜, F)) I p v)
  let i : AffineSubspace 𝕜 (TangentSpace I v.proj →ₗ[𝕜] TangentSpace I v.proj) :=
    affineSpan 𝕜 {LinearMap.id}
  let z := LinearMap.llcomp 𝕜 (TangentSpace I v.proj) _ _ (σ₁₂ := RingHom.id 𝕜) P
  let z' := z ∘ₗ ContinuousLinearMap.coeLM 𝕜
  i.comap z'.toAffineMap

variable (I F V) in
def oneJetSpace (x : M) := Σ v₀ : V x, oneJetOver I F V ⟨x, v₀⟩

omit [(x : M) → AddCommGroup (V x)] [(x : M) → Module 𝕜 (V x)] in
theorem mem_oneJetOver_iff (x : M) (v₀ : V x)
    (φ : TangentSpace I x →L[𝕜] TangentSpace (I.prod 𝓘(𝕜, F)) ⟨x, v₀⟩) :
    φ ∈ oneJetOver I F V ⟨x, v₀⟩ ↔
      mfderiv (I.prod 𝓘(𝕜, F)) I TotalSpace.proj ⟨x, v₀⟩ ∘L φ
      = ContinuousLinearMap.id 𝕜 (TangentSpace I x) := by
  rw [← ContinuousLinearMap.coe_injective.eq_iff]
  change _ ∈ affineSpan 𝕜 {LinearMap.id} ↔ _
  simp [LinearMap.llcomp_apply']

variable (I F V) in
def foo (x : M) (v : oneJetSpace I F V x) :
    Σ v₀ : V x, TangentSpace I x →L[𝕜] TangentSpace (I.prod 𝓘(𝕜, F)) (⟨x, v₀⟩ : TotalSpace F V) :=
  ⟨v.1, v.2⟩

omit [(x : M) → AddCommGroup (V x)] in
theorem injective_foo (x : M) : Function.Injective (foo I F V x) := by
  rintro ⟨v₀, ⟨φ, hφ⟩⟩ ⟨v₀', ⟨φ', hφ'⟩⟩ H
  obtain rfl : v₀ = v₀' := congr($H.1)
  simp [foo] at H
  simp [H]

noncomputable def oneJetOver.add (x : M) :
    oneJetSpace I F V x → oneJetSpace I F V x → oneJetSpace I F V x
  | ⟨v₀, φ, hφ⟩, ⟨v₀', φ', hφ'⟩ =>
    letI T (w₀ : V x) := TangentSpace (I.prod 𝓘(𝕜, F)) (⟨x, w₀⟩ : TotalSpace F V)
    let a (z : TotalSpace (F × F) (V ×ᵇ V)) : TotalSpace F V := ⟨z.1, z.2.1 + z.2.2⟩
    let A : TangentSpace (I.prod 𝓘(𝕜, F × F)) (⟨x, (v₀, v₀')⟩ : TotalSpace (F × F) (V ×ᵇ V))
        →L[𝕜] T (v₀ + v₀'):=
      mfderiv (I.prod 𝓘(𝕜, F × F)) (I.prod 𝓘(𝕜, F)) a ⟨x, v₀, v₀'⟩
    have H : mfderiv (I.prod 𝓘(𝕜, F)) _ TotalSpace.proj ⟨x, v₀⟩ ∘SL φ
        = mfderiv (I.prod 𝓘(𝕜, F)) _ TotalSpace.proj ⟨x, v₀'⟩ ∘SL φ' := by
      rw [mem_oneJetOver_iff] at hφ hφ'
      exact hφ.trans hφ'.symm
    ⟨v₀ + v₀', ⟨A ∘L glue φ φ' H, by
      rw [mem_oneJetOver_iff] at hφ ⊢
      rw [← ContinuousLinearMap.comp_assoc]
      rw [← mfderiv_comp ⟨x, v₀, v₀'⟩ (mdifferentiableAt_proj V) (TotalSpace.mdifferentiable_add _)]
      let p : TangentSpace (I.prod 𝓘(𝕜, F)) (M := TotalSpace F V) ⟨x, v₀⟩ →L[𝕜] _ :=
        mfderiv (I.prod 𝓘(𝕜, F)) I TotalSpace.proj ⟨x, v₀⟩
      refine Eq.trans ?_ <| congr(p ∘L $(glue_left φ φ' H)).trans hφ
      rw [← ContinuousLinearMap.comp_assoc]
      let p₁ (v : TotalSpace (F × F) (V ×ᵇ V)) : TotalSpace F V := ⟨v.1, v.2.1⟩
      rw [← mfderiv_comp ⟨x, v₀, v₀'⟩ (mdifferentiableAt_proj V) (f := p₁)]
      · rfl
      -- exact mdifferentiableAt_proj V

      sorry⟩⟩

noncomputable instance (x : M) : Add (oneJetSpace I F V x) where
  add := oneJetOver.add x

@[simp] theorem foo_add (x : M) (v₀ v₀' : V x)
    (φ : TangentSpace I x →L[𝕜] TangentSpace (I.prod 𝓘(𝕜, F)) (⟨x, v₀⟩ : TotalSpace F V))
    {hφ : φ ∈ oneJetOver I F V ⟨x, v₀⟩}
    (φ' : TangentSpace I x →L[𝕜] TangentSpace (I.prod 𝓘(𝕜, F)) (⟨x, v₀'⟩ : TotalSpace F V))
    {hφ' : φ' ∈ oneJetOver I F V ⟨x, v₀'⟩} :
    letI j : oneJetSpace I F V x := ⟨v₀, ⟨φ, hφ⟩⟩
    letI j' : oneJetSpace I F V x := ⟨v₀', ⟨φ', hφ'⟩⟩
    letI T (w₀ : V x) := TangentSpace (I.prod 𝓘(𝕜, F)) (⟨x, w₀⟩ : TotalSpace F V)
    letI a (z : TotalSpace (F × F) (V ×ᵇ V)) : TotalSpace F V := ⟨z.1, z.2.1 + z.2.2⟩
    letI A : TangentSpace (I.prod 𝓘(𝕜, F × F)) (⟨x, (v₀, v₀')⟩ : TotalSpace (F × F) (V ×ᵇ V))
        →L[𝕜] T (v₀ + v₀'):=
      mfderiv (I.prod 𝓘(𝕜, F × F)) (I.prod 𝓘(𝕜, F)) a ⟨x, v₀, v₀'⟩
    have H : mfderiv (I.prod 𝓘(𝕜, F)) _ TotalSpace.proj ⟨x, v₀⟩ ∘SL φ
        = mfderiv (I.prod 𝓘(𝕜, F)) _ TotalSpace.proj ⟨x, v₀'⟩ ∘SL φ' := by
      rw [mem_oneJetOver_iff] at hφ hφ'
      exact hφ.trans hφ'.symm
    foo I F V x (j + j') = ⟨v₀ + v₀', A ∘L glue φ φ' H⟩ :=
  rfl

-- @[simp] theorem foo_add (x : M) --(v₀ v₀' : V x)
--     -- (φ : TangentSpace I x →L[𝕜] TangentSpace (I.prod 𝓘(𝕜, F)) (⟨x, v₀⟩ : TotalSpace F V))
--     -- {hφ : φ ∈ oneJetOver I F V ⟨x, v₀⟩}
--     -- (φ' : TangentSpace I x →L[𝕜] TangentSpace (I.prod 𝓘(𝕜, F)) (⟨x, v₀'⟩ : TotalSpace F V))
--     -- {hφ' : φ' ∈ oneJetOver I F V ⟨x, v₀'⟩} :
--     (j j' : oneJetSpace I F V x) : -- := ⟨v₀, ⟨φ, hφ⟩⟩
--     -- letI j' : oneJetSpace I F V x := ⟨v₀', ⟨φ', hφ'⟩⟩
--     letI T (w₀ : V x) := TangentSpace (I.prod 𝓘(𝕜, F)) (⟨x, w₀⟩ : TotalSpace F V)
--     letI a (z : TotalSpace (F × F) (V ×ᵇ V)) : TotalSpace F V := ⟨z.1, z.2.1 + z.2.2⟩
--     letI A : TangentSpace (I.prod 𝓘(𝕜, F × F)) (⟨x, (j.1, j'.1)⟩ : TotalSpace (F × F) (V ×ᵇ V))
--         →L[𝕜] T (j.1 + j'.1):=
--       mfderiv (I.prod 𝓘(𝕜, F × F)) (I.prod 𝓘(𝕜, F)) a ⟨x, j.1, j'.1⟩
--     have H : mfderiv (I.prod 𝓘(𝕜, F)) _ TotalSpace.proj ⟨x, j.1⟩ ∘SL j.2.1
--         = mfderiv (I.prod 𝓘(𝕜, F)) _ TotalSpace.proj ⟨x, j'.1⟩ ∘SL j'.2.1 := by
--       sorry
--       -- rw [mem_oneJetOver_iff] at hφ hφ'
--       -- exact hφ.trans hφ'.symm
--     foo I F V x (j + j') = ⟨j.1 + j'.1, A ∘L glue x j.1 j'.1 j.2.1 j'.2.1 H⟩ :=
--   rfl

noncomputable instance (x : M) : Zero (oneJetSpace I F V x) where
  zero := ⟨0, ⟨FiberBundle.horizZero F V x, by
    rw [mem_oneJetOver_iff]
    simp [FiberBundle.mfderiv_proj_comp_horizZero ..]⟩⟩

@[simp] theorem foo_zero (x : M) : foo I F V x 0 = ⟨0, FiberBundle.horizZero F V x⟩ := rfl

theorem zero_def (x : M) :
    (0 : oneJetSpace I F V x) = ⟨0, FiberBundle.horizZero F V x, by
    rw [mem_oneJetOver_iff]
    simp [FiberBundle.mfderiv_proj_comp_horizZero ..]⟩ :=
  rfl

noncomputable def oneJetOver.neg (x : M) : oneJetSpace I F V x → oneJetSpace I F V x
  | ⟨v₀, φ, hφ⟩ =>
    let m (z : TotalSpace F V) : TotalSpace F V := ⟨z.1, - z.2⟩
    ⟨- v₀, mfderiv _ _ m ⟨x, v₀⟩ ∘L φ, by
      rw [mem_oneJetOver_iff] at hφ ⊢
      rw [← hφ, ← ContinuousLinearMap.comp_assoc]
      rw [← mfderiv_comp (f := m) (x := ⟨x, v₀⟩) (mdifferentiableAt_proj V)]
      · rfl
      exact TotalSpace.mdifferentiable_neg ..⟩

noncomputable instance (x : M) : Neg (oneJetSpace I F V x) where
  neg := oneJetOver.neg x

noncomputable instance (x : M) : AddCommGroup (oneJetSpace I F V x) where
  zero_add j := by
    obtain ⟨v₀, ⟨φ, hφ⟩⟩ := j
    dsimp at φ
    rw [mem_oneJetOver_iff] at hφ
    apply injective_foo
    rw [zero_def, foo_add]
    dsimp
    change _ = Sigma.mk _ _
    ext
    · simp
    simp only
    congr
    convert glue_right (FiberBundle.horizZero F V x) φ sorry using 2 -- ought to infer this sorry
    sorry
  add_zero := sorry
  add_assoc := sorry
  add_comm := sorry
  neg_add_cancel := sorry
  nsmul := nsmulRec
  zsmul := zsmulRec

noncomputable def oneJetOver.smul (x : M) (c : 𝕜) : oneJetSpace I F V x → oneJetSpace I F V x
  | ⟨v₀, φ, hφ⟩ =>
    let m (z : TotalSpace F V) : TotalSpace F V := ⟨z.1, c • z.2⟩
    ⟨c • v₀, mfderiv _ _ m ⟨x, v₀⟩ ∘L φ, by
      rw [mem_oneJetOver_iff] at hφ ⊢
      rw [← hφ, ← ContinuousLinearMap.comp_assoc]
      rw [← mfderiv_comp (f := m) (x := ⟨x, v₀⟩) (mdifferentiableAt_proj V)]
      · rfl
      exact TotalSpace.mdifferentiable_smul ..⟩

noncomputable instance (x : M) : SMul 𝕜 (oneJetSpace I F V x) where
  smul := oneJetOver.smul x

@[simp] theorem foo_smul (x : M) (c : 𝕜) (v₀ : V x)
    (φ : TangentSpace I x →L[𝕜] TangentSpace (I.prod 𝓘(𝕜, F)) (⟨x, v₀⟩ : TotalSpace F V))
    {hφ : φ ∈ oneJetOver I F V ⟨x, v₀⟩} :
    letI m (z : TotalSpace F V) : TotalSpace F V := ⟨z.1, c • z.2⟩
    foo I F V x (c • ⟨v₀, ⟨φ, hφ⟩⟩) = ⟨c • v₀, mfderiv _ _ m ⟨x, v₀⟩ ∘L φ⟩ :=
  rfl

noncomputable instance (x : M) : Module 𝕜 (oneJetSpace I F V x) where
  one_smul j := by
    obtain ⟨v₀, ⟨φ, hφ⟩⟩ := j
    apply injective_foo
    dsimp at φ
    rw [foo_smul]
    change _ = Sigma.mk _ _
    dsimp
    ext
    · simp
    congr!
    · simp
    trans ContinuousLinearMap.id 𝕜 _ ∘L φ
    · congr! 1
      apply Eq.trans (b := mfderiv (I.prod 𝓘(𝕜, F)) (I.prod 𝓘(𝕜, F)) (@id (TotalSpace F V)) ⟨x, v₀⟩)
      · congr
        ext <;> simp
      apply mfderiv_id
    simp
  zero_smul j := by
    obtain ⟨v₀, ⟨φ, hφ⟩⟩ := j
    apply injective_foo
    dsimp at φ
    rw [foo_smul, foo_zero]
    rw [mem_oneJetOver_iff] at hφ
    have := congr(FiberBundle.horizZero F V x ∘L $hφ)
    simp only [ContinuousLinearMap.comp_id] at this
    rw [← ContinuousLinearMap.comp_assoc] at this
    rw [← this]
    ext
    · simp
    congr!
    · simp
    unfold FiberBundle.horizZero
    dsimp
    symm
    letI p (x : TotalSpace F V) : M := TotalSpace.proj x
    rw [← mfderiv_comp (f := p) (x := ⟨x, v₀⟩)]
    · apply congr_fun
      apply congr_arg
      ext1 ⟨x, v⟩
      simp [p]
    · exact TotalSpace.mdifferentiable_incl ..
    · exact mdifferentiableAt_proj V
  smul_zero c := by
    apply injective_foo
    conv =>
      enter [1, 5, 2]
      change ⟨0, ⟨FiberBundle.horizZero F V x, _⟩⟩
    rw [foo_smul, foo_zero]
    unfold FiberBundle.horizZero
    dsimp
    let m (z : TotalSpace F V) : TotalSpace F V := ⟨z.1, c • z.2⟩
    let i (y : M) : TotalSpace F V := ⟨y, 0⟩
    conv =>
      enter [1, 2, 1]
      change mfderiv _ _ m ⟨x, 0⟩
    conv =>
      enter [1, 2, 2]
      change mfderiv _ _ i x
    conv =>
      enter [1, 2]
      equals mfderiv% (m ∘ i) x =>
        symm
        apply mfderiv_comp
        · exact TotalSpace.mdifferentiable_smul ..
        · exact TotalSpace.mdifferentiable_incl ..
    conv =>
      enter [1, 2]
      change mfderiv _ _ (fun y : M ↦ (⟨y, c • 0⟩ : TotalSpace F V)) x
    ext
    · simp
    congr!
    · simp
    simp
  mul_smul c c' j := by
    sorry
  smul_add c v v' := sorry
  add_smul c c' v := sorry

variable (I F V) in
def zerothPart (x : M) : oneJetSpace I F V x →ₗ[𝕜] V x where
  toFun := Sigma.fst
  map_add' := sorry
  map_smul' := sorry

variable [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)] in
variable (I F V) in
noncomputable def inclAtZero [VectorBundle 𝕜 F V] (x : M) :
    (TangentSpace I x →L[𝕜] V x) →ₗ[𝕜] oneJetSpace I F V x where
  toFun φ :=
    ⟨0, ⟨FiberBundle.horizZero F V x + VectorBundle.vert (I := I) F ⟨x, 0⟩ ∘L φ, by
      rw [mem_oneJetOver_iff]
      let p : TotalSpace F V → M := Bundle.TotalSpace.proj
      have i : ContinuousAdd (TangentSpace I (⟨x, 0⟩ : TotalSpace F V).proj) := inferInstance
      convert ContinuousLinearMap.comp_add _ _ _ using 1
      · symm
        rw [← ContinuousLinearMap.comp_assoc]
        rw [VectorBundle.mfderiv_proj_comp_vert]
        simp only [ContinuousLinearMap.zero_comp, add_zero]
        rw [FiberBundle.mfderiv_proj_comp_horizZero]
      infer_instance⟩⟩
  map_add' := sorry
  map_smul' c φ := by
    let m (z : TotalSpace F V) : TotalSpace F V := ⟨z.1, c • z.2⟩
    apply injective_foo
    rw [foo_smul]
    change Sigma.mk (0 : V x) _ = _
    -- (mfderiv _ _ m ⟨x, 0⟩ ∘L _)
    dsimp
    conv =>
      enter [2, 2]
      change mfderiv _ _ m ⟨x, 0⟩ ∘L _
    simp only [ContinuousLinearMap.comp_smulₛₗ, RingHom.id_apply, ContinuousLinearMap.comp_add]

    sorry


/-! ### One-jets of sections -/


noncomputable def oneJet (σ : Π x, V x) {x : M}
    (hσx : MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (T% σ) x) : oneJetSpace I F V x :=
  ⟨σ x, ⟨mfderiv% (T% σ) x, by
    rw [mem_oneJetOver_iff]
    set p : TotalSpace F V → M := Bundle.TotalSpace.proj
    rw [← mfderiv_comp x (mdifferentiableAt_proj V) hσx]
    exact mfderiv_id⟩⟩

omit [(x : M) → AddCommGroup (V x)] in
@[simp] theorem foo_oneJet (σ : Π x, V x) {x : M}
    (hσx : MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (T% σ) x) :
    foo I F V x (oneJet σ hσx) = ⟨σ x, mfderiv% (T% σ) x⟩ :=
  rfl

theorem zerothPart_oneJet (σ : Π x, V x) {x : M}
    (hσx : MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (T% σ) x) :
    zerothPart I F V x (oneJet σ hσx) = σ x :=
  rfl

variable [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)] in
theorem oneJet_inclAtZero [VectorBundle 𝕜 F V] (σ : Π x, V x) {x : M}
    (hσx : MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (T% σ) x)
    (hσx₀ : σ x = 0) :
    inclAtZero I F V x (differentialAtZero F σ hσx₀) = oneJet σ hσx := by
  apply injective_foo
  dsimp [inclAtZero, differentialAtZero]
  sorry

theorem oneJet_add [VectorBundle 𝕜 F V] (σ τ : Π x, V x) {x : M}
    (hσx : MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (T% σ) x)
    (hτx : MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (T% τ) x) :
    oneJet (σ + τ) (mdifferentiableAt_add_section hσx hτx)
    = oneJet σ hσx + oneJet τ hτx := by
  sorry

theorem oneJet_smul_const [VectorBundle 𝕜 F V] (σ : Π x, V x) {x : M} (c : 𝕜)
    (hσx : MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (T% σ) x) :
    oneJet (c • σ) (hσx.smul_const_section) = c • oneJet σ hσx := by
  sorry

theorem oneJet_smul [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
    [VectorBundle 𝕜 F V] (f : M → 𝕜) (σ : Π x, V x) {x : M}
    (hfx : MDifferentiableAt I 𝓘(𝕜) f x)
    (hσx : MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (T% σ) x) :
    oneJet (f • σ) (hfx.smul_section hσx)
    = f x • oneJet σ hσx + inclAtZero I F V x ((d% f x).smulRight (σ x)) := by
  sorry

variable (I F V) in
noncomputable def oneJetSplittingEquiv
    [∀ (x : M), IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)] [VectorBundle 𝕜 F V]
    (x : M) :
    { l // l ∘ₗ (inclAtZero I F V x) = LinearMap.id }
    ≃ { l // zerothPart I F V x ∘ₗ l = LinearMap.id } :=
  have hf : Function.Injective (inclAtZero I F V x) := sorry
  have hg : Function.Surjective (zerothPart I F V x) := sorry
  have h : Function.Exact (inclAtZero I F V x) (zerothPart I F V x) := sorry
  let e := h.splitInjectiveEquiv hg
  let e' := h.splitSurjectiveEquiv hf
  e.trans e'.symm
