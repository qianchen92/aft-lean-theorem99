import AFT.ActualPairedChannel
import AFT.PublicChartKernel
import AFT.SignedChannelEnergy

/-! # The actual positive four-output kernel underlying the paired score -/

namespace AFT.V7Calibration

open GaussianSource BoundaryCalibration PhysicalBlockTensors
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance fixedPairedKernelFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
attribute [local instance] actualModulusNeZero

/-- The real positive fixed-root output kernel, before inserting a paired
score. The attachment retains the same Gaussian source as the endpoints. -/
def fixedPairedKernel (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark)
    (attachedRoot compensatorRoot queue : ℤ)
    (input : Fin (Parameters.modulus parameter) × Fin (Parameters.modulus parameter))
    (word : Fin 4 → Fin (Parameters.modulus parameter)) : ℝ :=
  publicChartRaw cutoffScale parameter input.1 (charts input.1)
    (fun source => (actualShiftedBodyLaw cutoffScale parameter beta
      (attachedRoot + source + queue)).weight (word 2)) (word 0) (word 1) *
    (if ((word 3).val : ℤ) = (input.2.val : ℤ) + compensatorRoot then 1 else 0)

theorem fixedPairedKernel_nonneg (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark)
    (attachedRoot compensatorRoot queue : ℤ) (input word) :
    0 ≤ fixedPairedKernel cutoffScale parameter beta charts attachedRoot compensatorRoot queue input word := by
  apply mul_nonneg
  · exact publicChartRaw_nonneg _ _ _ _ _ (fun source => (actualShiftedBodyLaw _ _ _ _).nonneg _) _ _
  · split_ifs <;> norm_num

theorem publicChartRaw_triple_mass (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (mark : Fin (Parameters.modulus parameter)) (charts : PublicChartFamily cutoffScale parameter mark)
    (attachedRoot queue : ℤ) :
    (∑ first, ∑ second, ∑ attached : Fin (Parameters.modulus parameter),
      publicChartRaw cutoffScale parameter mark charts
        (fun source => (actualShiftedBodyLaw cutoffScale parameter beta (attachedRoot + source + queue)).weight attached) first second) = 1 := by
  have hh := sum_pair_mixture (fun _ : Fin (Parameters.modulus parameter) => (1 : ℝ))
    (fun attached first second => publicChartRaw cutoffScale parameter mark charts
      (fun source => (actualShiftedBodyLaw cutoffScale parameter beta (attachedRoot + source + queue)).weight attached) first second)
  simp only [one_mul] at hh
  rw [hh]
  simp only [publicChartRaw_total]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, FiniteDist.sum_one, mul_one]

/-- Even for impossible centers the integer translation has mass at most
one, so the literal physical kernel is substochastic on its entire domain. -/
theorem fixedPairedKernel_mass_le (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark)
    (attachedRoot compensatorRoot queue : ℤ) (input) :
    (∑ word, fixedPairedKernel cutoffScale parameter beta charts attachedRoot compensatorRoot queue input word) ≤ 1 := by
  have hdelta : (∑ output : Fin (Parameters.modulus parameter),
      if (output.val : ℤ) = (input.2.val : ℤ) + compensatorRoot then (1 : ℝ) else 0) ≤ 1 := by
    by_cases h : ∃ output : Fin (Parameters.modulus parameter), (output.val : ℤ) = (input.2.val : ℤ) + compensatorRoot
    · obtain ⟨output, hout⟩ := h
      have heq (other : Fin (Parameters.modulus parameter)) :
          ((other.val : ℤ) = (input.2.val : ℤ) + compensatorRoot) ↔ other = output := by
        constructor
        · intro hh; apply Fin.ext; omega
        · rintro rfl; exact hout
      simp only [heq, Finset.sum_ite_eq', Finset.mem_univ, if_true, le_refl]
    · push_neg at h
      simp only [if_neg (h _), Finset.sum_const_zero]
      norm_num
  rw [← quadrupleEquiv.symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  change (∑ first : Fin (Parameters.modulus parameter), ∑ second : Fin (Parameters.modulus parameter),
    ∑ attached : Fin (Parameters.modulus parameter), ∑ output : Fin (Parameters.modulus parameter),
    publicChartRaw cutoffScale parameter input.1 (charts input.1)
      (fun source => (actualShiftedBodyLaw cutoffScale parameter beta (attachedRoot + source + queue)).weight attached) first second *
      (if (output.val : ℤ) = (input.2.val : ℤ) + compensatorRoot then 1 else 0)) ≤ 1
  simp only [← Finset.mul_sum]
  have hm := publicChartRaw_triple_mass cutoffScale parameter beta input.1 (charts input.1) attachedRoot queue
  calc
    _ ≤ ∑ first, ∑ second, ∑ attached : Fin (Parameters.modulus parameter),
      publicChartRaw cutoffScale parameter input.1 (charts input.1)
        (fun source => (actualShiftedBodyLaw cutoffScale parameter beta (attachedRoot + source + queue)).weight attached) first second := by
      apply Finset.sum_le_sum
      intro first _
      apply Finset.sum_le_sum
      intro second _
      apply Finset.sum_le_sum
      intro attached _
      exact (mul_le_mul_of_nonneg_left hdelta
        (publicChartRaw_nonneg _ _ _ _ _ (fun source => (actualShiftedBodyLaw _ _ _ _).nonneg _) _ _)).trans_eq (mul_one _)
    _ = 1 := hm

/-- The profile channel is exactly a signed expectation through the positive
kernel, on the original independent primary and compensating-center law. -/
theorem fixedPairedChartRaw_expectation (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark)
    (attachedRoot compensatorRoot queue : ℤ) (profile : Fin (Parameters.modulus parameter) → ℝ) (word) :
    fixedPairedChartRaw cutoffScale parameter beta charts attachedRoot compensatorRoot queue profile word =
      ∑ input, ((actualPrimaryLaw cutoffScale parameter beta).prod (actualBodyLaw cutoffScale parameter beta)).weight input *
        pairedLift (actualPrimaryLaw cutoffScale parameter beta).weight (actualBodyLaw cutoffScale parameter beta).weight
          (fun color position => publicAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color position.val)
          (v7Activation cutoffScale parameter) profile input.1 input.2 *
        fixedPairedKernel cutoffScale parameter beta charts attachedRoot compensatorRoot queue input word := by
  simp only [fixedPairedChartRaw, fixedPairedKernel, Fintype.sum_prod_type, FiniteDist.prod_weight]
  apply Finset.sum_congr rfl
  intro mark _
  apply Finset.sum_congr rfl
  intro center _
  ring

end
end AFT.V7Calibration
