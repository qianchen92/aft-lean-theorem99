import AFT.PublicChartMass
import AFT.ActualPairEnergy

/-! # Positivity and sharp point ceilings of the original conditional chart -/

namespace AFT.V7Calibration

open GaussianSource BoundaryCalibration Filter TrimmedSlice
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance chartKernelFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
attribute [local instance] actualModulusNeZero

theorem publicChartRaw_nonneg (cutoffScale : ℝ) (parameter : ℕ)
    (mark : Fin (Parameters.modulus parameter)) (charts : PublicChartFamily cutoffScale parameter mark)
    (attached : Window (legCutoff cutoffScale parameter - 1) → ℝ) (ha : ∀ source, 0 ≤ attached source)
    (first second : Fin (Parameters.modulus parameter)) :
    0 ≤ publicChartRaw cutoffScale parameter mark charts attached first second := by
  apply Finset.sum_nonneg
  intro sample _
  apply mul_nonneg (FiniteDist.nonneg _ _)
  apply Finset.sum_nonneg
  intro offset _
  apply mul_nonneg (FiniteDist.nonneg _ _)
  apply Finset.sum_nonneg
  intro input _
  exact mul_nonneg (mul_nonneg (FiniteDist.nonneg _ _) (FiniteDist.nonneg _ _)) (ha input.2)

/-- A bound on the actual attached body's probability can be taken outside
the full chart average, without decoupling its shared source. -/
theorem publicChartRaw_attached_le (cutoffScale : ℝ) (parameter : ℕ)
    (mark : Fin (Parameters.modulus parameter)) (charts : PublicChartFamily cutoffScale parameter mark)
    (attached : Window (legCutoff cutoffScale parameter - 1) → ℝ) (upper : ℝ)
    (ha : ∀ source, attached source ≤ upper) (first second : Fin (Parameters.modulus parameter)) :
    publicChartRaw cutoffScale parameter mark charts attached first second ≤
      upper * publicChartRaw cutoffScale parameter mark charts (fun _ => 1) first second := by
  unfold publicChartRaw
  simp only [Finset.mul_sum, mul_one]
  apply Finset.sum_le_sum
  intro sample _
  apply Finset.sum_le_sum
  intro offset _
  apply Finset.sum_le_sum
  intro input _
  have hn : 0 ≤ (errorLaw (bodyBlur cutoffScale parameter)).weight sample *
      (publicOffsetLaw cutoffScale parameter mark sample).weight offset *
      (protectedGaussianLaw cutoffScale parameter).weight input *
      (chartPairOutput cutoffScale parameter offset (charts sample offset) input).weight (first,second) := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (FiniteDist.nonneg _ _)
      (FiniteDist.nonneg _ _)) (FiniteDist.nonneg _ _)) (FiniteDist.nonneg _ _)
  convert mul_le_mul_of_nonneg_left (ha input.2) hn using 1 <;> ring

/-- Any primary-dependent sign branch has at most twice the fair diffuse
mass. This pointwise inequality retains the exact integer-window law. -/
theorem conditionalPairAtSource_le_twice (cutoffScale : ℝ) (parameter : ℕ)
    (mark : Fin (Parameters.modulus parameter)) (source : ℤ)
    (first second : Fin (Parameters.modulus parameter)) :
    conditionalPairAtSource cutoffScale parameter mark source first second ≤
      2 * inactivePairAtSource cutoffScale parameter source first second := by
  have hp := mixedPair_nonneg (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter)
    (fun sample => (Parameters.anchorWidth parameter : ℤ) + bodyShift cutoffScale parameter sample)
    (fun _ => source) (bodyBlur cutoffScale parameter).weight (Parameters.anchorWidth parameter)
    (bodyBlur cutoffScale parameter).nonneg first second
  have hm := mixedPair_nonneg (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter)
    (fun sample => -(2 * (Parameters.anchorWidth parameter : ℤ)) + 1 + bodyShift cutoffScale parameter sample)
    (fun _ => source) (bodyBlur cutoffScale parameter).weight (Parameters.anchorWidth parameter)
    (bodyBlur cutoffScale parameter).nonneg first second
  rw [conditionalPairAtSource_formula]
  have hnorm : |signedPairAtSource cutoffScale parameter source first second| ≤
      inactivePairAtSource cutoffScale parameter source first second := by
    unfold signedPairAtSource inactivePairAtSource
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hprod := mul_le_mul_of_nonneg_right (paletteSign_abs_le (Parameters.modulus parameter) mark)
    (abs_nonneg (signedPairAtSource cutoffScale parameter source first second))
  rw [← abs_mul, one_mul] at hprod
  linarith [le_abs_self (paletteSign (Parameters.modulus parameter) mark *
    signedPairAtSource cutoffScale parameter source first second)]

/-- Averaging an actual primary law gives the sharp pair height needed for
the full positive four-output density ceiling. -/
theorem publicChartRaw_primary_height (cutoffScale : ℝ) (parameter : ℕ)
    (primary : FiniteDist (Fin (Parameters.modulus parameter)))
    (charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark)
    (hcharts : ∀ mark first second,
      publicChartRaw cutoffScale parameter mark (charts mark) (fun _ => 1) first second =
        conditionalJointOutput cutoffScale parameter mark (fun _ => 1) first second)
    (hinactive : ∀ source : Window (legCutoff cutoffScale parameter - 1), ∀ first second,
      inactivePairAtSource cutoffScale parameter source first second ≤
        2 / ((Parameters.anchorWidth parameter : ℝ) * Parameters.modulus parameter))
    (first second : Fin (Parameters.modulus parameter)) :
    (∑ mark, primary.weight mark * publicChartRaw cutoffScale parameter mark (charts mark) (fun _ => 1) first second) ≤
      4 / ((Parameters.modulus parameter : ℝ) * Parameters.anchorWidth parameter) +
        v7Activation cutoffScale parameter * primary.weight first / Parameters.anchorWidth parameter := by
  have ha0 : 0 ≤ v7Activation cutoffScale parameter := by
    unfold v7Activation GaussianSource.activation
    exact mul_nonneg (by positivity) (FiniteDist.nonneg _ _)
  have ha1 : v7Activation cutoffScale parameter ≤ 1 := activation_le_one _ _ _ _
  have hdiff (mark : Fin (Parameters.modulus parameter)) :
      (1 - v7Activation cutoffScale parameter) *
          (∑ source, (inactiveLegSource cutoffScale parameter).weight source *
            conditionalPairAtSource cutoffScale parameter mark source first second) ≤
        4 / ((Parameters.modulus parameter : ℝ) * Parameters.anchorWidth parameter) := by
    have hcond (source : Window (legCutoff cutoffScale parameter - 1)) :=
      (conditionalPairAtSource_le_twice cutoffScale parameter mark source first second).trans
        (mul_le_mul_of_nonneg_left (hinactive source first second) (by norm_num : (0 : ℝ) ≤ 2))
    have hh : (∑ source, (inactiveLegSource cutoffScale parameter).weight source *
        conditionalPairAtSource cutoffScale parameter mark source first second) ≤
        4 / ((Parameters.modulus parameter : ℝ) * Parameters.anchorWidth parameter) := by
      calc
        _ ≤ ∑ source, (inactiveLegSource cutoffScale parameter).weight source *
            (4 / ((Parameters.modulus parameter : ℝ) * Parameters.anchorWidth parameter)) := by
          apply Finset.sum_le_sum
          intro source _
          apply mul_le_mul_of_nonneg_left _ (FiniteDist.nonneg _ _)
          exact (hcond source).trans_eq (by ring)
        _ = _ := by rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]
    exact (mul_le_mul_of_nonneg_left hh (by linarith)).trans
      ((mul_le_mul_of_nonneg_right (show 1 - v7Activation cutoffScale parameter ≤ 1 by linarith)
        (show 0 ≤ 4 / ((Parameters.modulus parameter : ℝ) * Parameters.anchorWidth parameter) by positivity)).trans_eq (one_mul _))

  simp only [hcharts, conditionalJointOutput, mul_one, mul_add, Finset.sum_add_distrib]
  apply add_le_add
  · calc
      _ ≤ ∑ mark, primary.weight mark * (4 / ((Parameters.modulus parameter : ℝ) * Parameters.anchorWidth parameter)) :=
        Finset.sum_le_sum fun mark _ => mul_le_mul_of_nonneg_left (hdiff mark) (primary.nonneg mark)
      _ = _ := by rw [← Finset.sum_mul, primary.sum_one, one_mul]
  · simp only [mul_ite, ite_mul, mul_zero, zero_mul, mul_one, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hh := mul_le_mul_of_nonneg_left
      (blurredAnchorKernel_le (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
        (bodyShift cutoffScale parameter) (bodyBlur cutoffScale parameter) first second.val)
      (mul_nonneg (primary.nonneg first) ha0)
    convert hh using 1 <;> ring

end
end AFT.V7Calibration
