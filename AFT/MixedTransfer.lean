import AFT.MixedKernel

/-! # Mixed-fiber Hilbert transfers for canonical moment collision graphs -/

namespace AFT.CanonicalMoments

open scoped BigOperators Classical

variable {Ending New Fixed Keep : Type*}
variable [Fintype Ending] [Fintype New] [Fintype Fixed] [Fintype Keep]

omit [Fintype New] [Fintype Fixed] [Fintype Keep] in
/-- Weighted Cauchy--Schwarz in an actual finite probability space. -/
theorem expectation_mul_sq_le (law : FiniteDist Ending) (first second : Ending → ℝ) :
    law.expectation (fun value => first value * second value) ^ 2 ≤ law.l2Sq first * law.l2Sq second := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
  · intro value _
    exact mul_nonneg (law.nonneg value) (sq_nonneg _)
  · intro value _
    exact mul_nonneg (law.nonneg value) (sq_nonneg _)
  · intro value _
    ring

/-- One exact contraction step: ending sample labels are integrated, new
labels remain, while the fixed and untouched labels pass through unchanged. -/
noncomputable def fiberTransfer (ending : FiniteDist Ending)
    (kernel : Ending → New → Fixed → ℝ) (input : Ending → Fixed → Keep → ℝ)
    (newValue : New) (fixedValue : Fixed) (keepValue : Keep) : ℝ :=
  ending.expectation fun endingValue => kernel endingValue newValue fixedValue * input endingValue fixedValue keepValue

/-- The genuine mixed-fiber transfer inequality. The supremum fixes only
middle labels; every first/last occurrence retains its L2 contribution.
Untouched active labels introduce no dimension or cardinality factor. -/
theorem fiberTransfer_energy_le (ending : FiniteDist Ending) (fresh : FiniteDist New)
    (fixed : FiniteDist Fixed) (keep : FiniteDist Keep)
    (kernel : Ending → New → Fixed → ℝ) (input : Ending → Fixed → Keep → ℝ)
    (bound : ℝ)
    (hfiber : ∀ fixedValue, (fresh.expectation fun newValue =>
      ending.l2Sq (fun endingValue => kernel endingValue newValue fixedValue)) ≤ bound) :
    (fixed.expectation fun fixedValue => keep.expectation fun keepValue =>
      fresh.l2Sq (fun newValue => fiberTransfer ending kernel input newValue fixedValue keepValue)) ≤
      bound * (fixed.expectation fun fixedValue => keep.expectation fun keepValue =>
        ending.l2Sq (fun endingValue => input endingValue fixedValue keepValue)) := by
  have hpoint (fixedValue : Fixed) (keepValue : Keep) :
      fresh.l2Sq (fun newValue => fiberTransfer ending kernel input newValue fixedValue keepValue) ≤
      bound * ending.l2Sq (fun endingValue => input endingValue fixedValue keepValue) := by
    have hcs (newValue : New) := expectation_mul_sq_le ending
      (fun endingValue => kernel endingValue newValue fixedValue)
      (fun endingValue => input endingValue fixedValue keepValue)
    have hh := Finset.sum_le_sum (fun newValue (_ : newValue ∈ Finset.univ) =>
      mul_le_mul_of_nonneg_left (hcs newValue) (fresh.nonneg newValue))
    have heq : (∑ newValue, fresh.weight newValue *
        (ending.l2Sq (fun endingValue => kernel endingValue newValue fixedValue) *
          ending.l2Sq (fun endingValue => input endingValue fixedValue keepValue))) =
      (fresh.expectation fun newValue => ending.l2Sq (fun endingValue => kernel endingValue newValue fixedValue)) *
        ending.l2Sq (fun endingValue => input endingValue fixedValue keepValue) := by
      unfold FiniteDist.expectation
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro newValue _
      ring
    exact (hh.trans_eq heq).trans
      (mul_le_mul_of_nonneg_right (hfiber fixedValue) (FiniteDist.l2Sq_nonneg _ _))
  unfold FiniteDist.expectation
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro fixedValue _
  have hh := Finset.sum_le_sum (fun keepValue (_ : keepValue ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hpoint fixedValue keepValue) (keep.nonneg keepValue))
  have hm := mul_le_mul_of_nonneg_left hh (fixed.nonneg fixedValue)
  convert hm using 1
  · simp only [Finset.mul_sum]
  · simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro keepValue _
    ring

/-- The actual mixed Hilbert fiber of a transfer kernel. -/
noncomputable def transferFiberNorm (ending : FiniteDist Ending) (fresh : FiniteDist New)
    (kernel : Ending → New → Fixed → ℝ) : ℝ :=
  ‖fun fixedValue => Real.sqrt (fresh.expectation fun newValue =>
    ending.l2Sq (fun endingValue => kernel endingValue newValue fixedValue))‖

/-- The transfer bound with its actual mixed-fiber norm, with no operator
estimate supplied as a premise. -/
theorem fiberTransfer_actual_energy_le (ending : FiniteDist Ending) (fresh : FiniteDist New)
    (fixed : FiniteDist Fixed) (keep : FiniteDist Keep)
    (kernel : Ending → New → Fixed → ℝ) (input : Ending → Fixed → Keep → ℝ) :
    (fixed.expectation fun fixedValue => keep.expectation fun keepValue =>
      fresh.l2Sq (fun newValue => fiberTransfer ending kernel input newValue fixedValue keepValue)) ≤
      transferFiberNorm ending fresh kernel ^ 2 *
        (fixed.expectation fun fixedValue => keep.expectation fun keepValue =>
          ending.l2Sq (fun endingValue => input endingValue fixedValue keepValue)) := by
  apply fiberTransfer_energy_le
  intro fixedValue
  have hnonneg : 0 ≤ fresh.expectation (fun newValue =>
      ending.l2Sq (fun endingValue => kernel endingValue newValue fixedValue)) :=
    Finset.sum_nonneg fun newValue _ => mul_nonneg (fresh.nonneg _) (FiniteDist.l2Sq_nonneg _ _)
  have h := norm_le_pi_norm (fun fixedValue => Real.sqrt (fresh.expectation fun newValue =>
    ending.l2Sq (fun endingValue => kernel endingValue newValue fixedValue))) fixedValue
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] at h
  have hh := (sq_le_sq₀ (Real.sqrt_nonneg _) (norm_nonneg _)).mpr h
  rwa [Real.sq_sqrt hnonneg] at hh

end AFT.CanonicalMoments
