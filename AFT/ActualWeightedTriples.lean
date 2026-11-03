import AFT.PublicChartGaussian
import AFT.V7ReferenceLaws

/-! # The actual affine-chart primary-score numerator -/

namespace AFT.V7Calibration

open GaussianSource BoundaryCalibration Filter
open scoped BigOperators Classical Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance weightedTriplesFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
attribute [local instance] actualModulusNeZero

/-- Signed diffuse contribution with the same source retained in both
endpoint and attachment factors. -/
def signedDiffuseJoint (cutoffScale : ℝ) (parameter : ℕ)
    (attached : Window (legCutoff cutoffScale parameter - 1) → ℝ)
    (first second : Fin (Parameters.modulus parameter)) : ℝ :=
  (1 - v7Activation cutoffScale parameter) *
    ∑ source, (inactiveLegSource cutoffScale parameter).weight source *
      signedPairAtSource cutoffScale parameter source first second * attached source

/-- The full canonical primary-score response, with the exact marked
coefficient and the actual diffuse sign functional. -/
def primaryJointNumerator (cutoffScale : ℝ) (parameter : ℕ)
    (profile : Fin (Parameters.modulus parameter) → ℝ)
    (attached : Window (legCutoff cutoffScale parameter - 1) → ℝ)
    (first second : Fin (Parameters.modulus parameter)) : ℝ :=
  (∑ mark, paletteSign (Parameters.modulus parameter) mark * profile mark) *
    signedDiffuseJoint cutoffScale parameter attached first second +
  v7Activation cutoffScale parameter * profile first *
    blurredAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
      (bodyShift cutoffScale parameter) (bodyBlur cutoffScale parameter) first second.val * attached (windowZero _)

theorem conditionalJointOutput_signed (cutoffScale : ℝ) (parameter : ℕ)
    (profile : Fin (Parameters.modulus parameter) → ℝ) (hcanonical : ∑ mark, profile mark = 0)
    (attached : Window (legCutoff cutoffScale parameter - 1) → ℝ)
    (first second : Fin (Parameters.modulus parameter)) :
    (∑ mark, profile mark * conditionalJointOutput cutoffScale parameter mark attached first second) =
      primaryJointNumerator cutoffScale parameter profile attached first second := by
  simp only [conditionalJointOutput, primaryJointNumerator, mul_add, Finset.sum_add_distrib]
  apply congrArg₂ (· + ·)
  · have hdiff : (∑ mark, profile mark * ((1 - v7Activation cutoffScale parameter) *
        ∑ source, (inactiveLegSource cutoffScale parameter).weight source *
          conditionalPairAtSource cutoffScale parameter mark source first second * attached source)) =
        (1 - v7Activation cutoffScale parameter) *
          ∑ source, ((inactiveLegSource cutoffScale parameter).weight source * attached source) *
            ∑ mark, profile mark * conditionalPairAtSource cutoffScale parameter mark source first second := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro source _
      apply Finset.sum_congr rfl
      intro mark _
      ring
    rw [hdiff]
    simp only [conditionalPairAtSource_signed cutoffScale parameter profile hcanonical, signedDiffuseJoint, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro source _
    ring
  · simp only [mul_ite, ite_mul, mul_zero, zero_mul, mul_one, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring

/-- The positive chart families are actually constructed. Their exact
primary-score numerator follows by averaging the original probabilities;
no fair-sign replacement or abstract numerator identity is assumed. -/
theorem actual_primary_score_chart_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
      ∃ charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark,
      ∀ (profile : Fin (Parameters.modulus parameter) → ℝ), (∑ mark, profile mark) = 0 →
      ∀ (attached : Window (legCutoff cutoffScale parameter - 1) → ℝ) (first second : Fin (Parameters.modulus parameter)),
        (∑ mark, (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight mark *
          (profile mark / (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight mark) *
          publicChartRaw cutoffScale parameter mark (charts mark) attached first second) =
          primaryJointNumerator cutoffScale parameter profile attached first second := by
  filter_upwards [public_chart_joint_output_eventually cutoffScale hscale,
    actual_reference_laws_eventually cutoffScale hscale beta hbeta,
    actual_primary_probability_eventually cutoffScale hscale beta hbeta] with parameter hc hl hp
  choose charts hcharts using hc
  refine ⟨charts, ?_⟩
  intro profile hcanonical attached first second
  have hnonzero (mark) : (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight mark ≠ 0 := by
    rw [hl.1]
    exact (hp.1 mark).ne'
  simp only [hcharts, mul_div_cancel₀ _ (hnonzero _)]
  exact conditionalJointOutput_signed cutoffScale parameter profile hcanonical attached first second

end
end AFT.V7Calibration
