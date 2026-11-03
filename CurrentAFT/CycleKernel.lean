import CurrentAFT.PathLikelihood

/-!
# Finite Cauchy--Schwarz for the complete cycle partition function

The cyclic tensor contraction is a trace of a product of actual finite
matrices. At least two factors suffice for the Frobenius product bound;
there is no dimension factor and an unconstrained rank-one factor has
energy one. The expansion below keeps the closing edge explicitly.
-/

namespace CurrentAFT.CycleKernel

open AFT
open scoped BigOperators Classical

noncomputable section

variable {Scalar : Type*} [Fintype Scalar]

def energy (matrix : Matrix Scalar Scalar ℝ) : ℝ :=
  ∑ first, ∑ second, matrix first second ^ 2

theorem energy_nonneg (matrix : Matrix Scalar Scalar ℝ) : 0 ≤ energy matrix :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem energy_mul_le (first second : Matrix Scalar Scalar ℝ) :
    energy (first * second) ≤ energy first * energy second := by
  unfold energy
  simp only [Matrix.mul_apply]
  calc
    _ ≤ ∑ start, ∑ ending, (∑ middle, first start middle ^ 2) *
        ∑ middle, second middle ending ^ 2 := by
      apply Finset.sum_le_sum
      intro start _
      apply Finset.sum_le_sum
      intro ending _
      exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
    _ = (∑ start, ∑ middle, first start middle ^ 2) *
        ∑ ending, ∑ middle, second middle ending ^ 2 := by
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]
    _ = _ := by rw [Finset.sum_comm (f := fun ending middle => second middle ending ^ 2)]

/-- Product of a nonempty finite matrix sequence, avoiding any norm of the
identity matrix. -/
def chainProduct : (length : ℕ) → (Fin (length + 1) → Matrix Scalar Scalar ℝ) → Matrix Scalar Scalar ℝ
  | 0, matrices => matrices 0
  | length + 1, matrices => matrices 0 * chainProduct length (fun index => matrices index.succ)

theorem energy_chainProduct_le (length : ℕ) (matrices : Fin (length + 1) → Matrix Scalar Scalar ℝ) :
    energy (chainProduct length matrices) ≤ ∏ index, energy (matrices index) := by
  induction length with
  | zero => simp [chainProduct]
  | succ length ih =>
    apply (energy_mul_le (matrices 0) (chainProduct length (fun index => matrices index.succ))).trans
    rw [Fin.prod_univ_succ]
    exact mul_le_mul_of_nonneg_left (ih _) (energy_nonneg _)

/-- A trace pairs two matrices in their Frobenius inner product. -/
theorem trace_mul_sq_le (first second : Matrix Scalar Scalar ℝ) :
    Matrix.trace (first * second) ^ 2 ≤ energy first * energy second := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Scalar × Scalar))
    (fun pair => first pair.1 pair.2) (fun pair => second pair.2 pair.1)
  simp only [Fintype.sum_prod_type] at hcs
  have htrace : Matrix.trace (first * second) = ∑ start, ∑ ending, first start ending * second ending start := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  rw [htrace]
  unfold energy
  rw [Finset.sum_comm (f := fun start ending => second ending start ^ 2)] at hcs
  exact hcs

/-- The complete cyclic product always contains at least two factors. -/
def cycleValue (length : ℕ) (matrices : Fin (length + 2) → Matrix Scalar Scalar ℝ) : ℝ :=
  Matrix.trace (matrices 0 * chainProduct length (fun index => matrices index.succ))

/-- Complete squared cyclic contraction bound, without a palette-size loss. -/
theorem cycleValue_sq_le (length : ℕ) (matrices : Fin (length + 2) → Matrix Scalar Scalar ℝ) :
    cycleValue length matrices ^ 2 ≤ ∏ index, energy (matrices index) := by
  apply (trace_mul_sq_le (matrices 0) (chainProduct length (fun index => matrices index.succ))).trans
  rw [Fin.prod_univ_succ]
  exact mul_le_mul_of_nonneg_left (energy_chainProduct_le length _) (energy_nonneg _)

/-- Exact open-chain expansion with every intermediate latent value summed. -/
theorem chainProduct_expansion (length : ℕ) (matrices : Fin (length + 1) → Matrix Scalar Scalar ℝ)
    (first last : Scalar) :
    chainProduct length matrices first last =
      ∑ middle : Fin length → Scalar,
        ∏ index : Fin (length + 1),
          matrices index ((Fin.cons first middle : Fin (length + 1) → Scalar) index) ((Fin.snoc middle last : Fin (length + 1) → Scalar) index) := by
  induction length generalizing first last with
  | zero => simp [chainProduct, Fin.snoc_zero]
  | succ length ih =>
    rw [chainProduct, Matrix.mul_apply]
    simp_rw [ih]
    conv_rhs =>
      rw [← (PathLikelihood.latentConsEquiv length).sum_comp, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro next _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro middle _
    simp only [PathLikelihood.latentConsEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ,
      ← Fin.cons_snoc_eq_snoc_cons, Fin.cons_zero, Fin.cons_succ]

/-- The matrix trace is exactly the complete independent-latent cycle sum,
including the last-to-first closing edge. -/
theorem cycleValue_expansion (length : ℕ) (matrices : Fin (length + 2) → Matrix Scalar Scalar ℝ) :
    cycleValue length matrices =
      ∑ latent : Fin (length + 2) → Scalar,
        ∏ index : Fin (length + 2), matrices index (latent index) (latent (finRotate (length + 2) index)) := by
  unfold cycleValue Matrix.trace
  simp only [Matrix.diag_apply, Matrix.mul_apply]
  simp_rw [chainProduct_expansion]
  simp only [Finset.mul_sum]
  conv_rhs =>
    rw [← (PathLikelihood.latentConsEquiv (length + 1)).sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro first _
  conv_rhs =>
    rw [← (PathLikelihood.latentConsEquiv length).sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro next _
  apply Finset.sum_congr rfl
  intro middle _
  have hrotate (index : Fin (length + 2)) :
      (Fin.cons first (Fin.cons next middle) : Fin (length + 2) → Scalar) (finRotate (length + 2) index) =
        (Fin.snoc (Fin.cons next middle) first : Fin (length + 2) → Scalar) index :=
    congrFun (Fin.snoc_eq_cons_rotate (Fin.cons next middle) first).symm index
  simp only [PathLikelihood.latentConsEquiv, Equiv.coe_fn_mk]
  simp_rw [hrotate]
  simp only [Fin.prod_univ_succ, ← Fin.cons_snoc_eq_snoc_cons, Fin.cons_zero, Fin.cons_succ]

/-- Finner's degree-two cycle inequality in its explicit finite sum form. -/
theorem cycle_partition_sq_le (length : ℕ) (matrices : Fin (length + 2) → Matrix Scalar Scalar ℝ) :
    (∑ latent : Fin (length + 2) → Scalar,
      ∏ index : Fin (length + 2), matrices index (latent index)
        (latent (finRotate (length + 2) index))) ^ 2 ≤
      ∏ index, energy (matrices index) := by
  rw [← cycleValue_expansion]
  exact cycleValue_sq_le length matrices

end

end CurrentAFT.CycleKernel
