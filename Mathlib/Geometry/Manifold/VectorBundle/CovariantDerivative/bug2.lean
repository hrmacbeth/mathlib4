module
public section

universe u v v1 v2 v3 w w'

instance {ι : Type u} {α : ι → Type v} {β : ι → Type w} [∀ i, SMul (α i) (β i)] :
  SMul (∀ i, α i) (∀ i, β i) where smul s x i := s i • x i

instance {ι : Type u} {M : ι → Type v} [(i : ι) → Zero (M i)] : Zero ((i : ι) → M i) := sorry

-- mocked up from `Inner`, specialised to real spaces
class Inner' (R : Type u) (E : Type w) where
  /-- The inner product function. -/
  inner : E → E → R
export Inner' (inner)

variable {R : Type u} [Mul R] [Zero R] {M : Type v} {V : M → Type w}
    [∀ x, Inner' R (V x)] [∀ x, SMul R (V x)]

variable (R) in
noncomputable abbrev product1 (σ τ : ∀ x : M, V x) : M → R :=
  fun x ↦ inner (σ x) (τ x)

variable (R) in
noncomputable def product2 (σ τ : ∀ x : M, V x) : M → R :=
  fun x ↦ inner (σ x) (τ x)

theorem product1_smul_left {σ τ : ∀ x : M, V x} (f : M → R) :
    product1 R (f • σ) τ = f • product1 R σ τ := by
  sorry -- omitted

theorem product2_smul_left {σ τ : ∀ x : M, V x} (f : M → R) :
    product2 R (f • σ) τ = f • product2 R σ τ := by
  sorry -- omitted

variable {f : M → R} {σ τ : (x : M) → V x} {x : M}

theorem fails_with_abbrev : (product1 R (f • σ) τ) x = 0 := by
  fail_if_success simp -beta [product1_smul_left]
  fail_if_success simp [product1_smul_left]
  rw [product1_smul_left]
  sorry

theorem works_with_def : (product2 R (f • σ) τ) x = 0 := by
  --simp -beta [product2_smul_left]
  simp [product2_smul_left]
  --rw [product2_smul_left]
  sorry

theorem works_regardless : product1 R (f • σ) τ = 0 := by
  simp [product1_smul_left]
  sorry

theorem works_regardless' : product2 R (f • σ) τ = 0 := by
  simp [product2_smul_left]
  sorry
