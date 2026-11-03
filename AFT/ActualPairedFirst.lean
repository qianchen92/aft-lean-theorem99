import AFT.ActualScoreMarginals
import AFT.PairedScoreOutput
import AFT.ActualResponseFormula

/-! # The true affine-chart paired first response equals the calibrated operator -/

namespace AFT.V7Calibration

open GaussianSource BoundaryCalibration Filter
open scoped BigOperators Classical Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance pairedFirstFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
attribute [local instance] actualModulusNeZero

/-- Literal count of both endpoints of the original chart sampler. -/
def publicChartEndpointMean (cutoffScale : ℝ) (parameter : ℕ) (mark : Fin (Parameters.modulus parameter))
    (charts : PublicChartFamily cutoffScale parameter mark) (output : Fin (Parameters.modulus parameter)) : ℝ :=
  (∑ second, publicChartRaw cutoffScale parameter mark charts (fun _ => 1) output second) +
    (∑ first, publicChartRaw cutoffScale parameter mark charts (fun _ => 1) first output)

theorem publicChartEndpointMean_profile (cutoffScale : ℝ) (parameter : ℕ)
    (charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark)
    (hcharts : ∀ mark first second,
      publicChartRaw cutoffScale parameter mark (charts mark) (fun _ => 1) first second =
        conditionalJointOutput cutoffScale parameter mark (fun _ => 1) first second)
    (profile : Fin (Parameters.modulus parameter) → ℝ) (hcanonical : ∑ mark, profile mark = 0)
    (output : Fin (Parameters.modulus parameter)) :
    (∑ mark, profile mark * publicChartEndpointMean cutoffScale parameter mark (charts mark) output) =
      (∑ second, primaryJointNumerator cutoffScale parameter profile (fun _ => 1) output second) +
        (∑ first, primaryJointNumerator cutoffScale parameter profile (fun _ => 1) first output) := by
  simp only [publicChartEndpointMean, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  apply congrArg₂ (· + ·)
  all_goals
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro other _
    simp only [hcharts]
    exact conditionalJointOutput_signed cutoffScale parameter profile hcanonical (fun _ => 1) _ _

/-- Count of the physical primary pair and the root-only reserved
compensator, weighted by the actual paired score. -/
def actualPairedFirstCount (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark)
    (profile : Fin (Parameters.modulus parameter) → ℝ) (output : Fin (Parameters.modulus parameter)) : ℝ :=
  ∑ mark, ∑ center,
    (actualPrimaryLaw cutoffScale parameter beta).weight mark *
      (actualBodyLaw cutoffScale parameter beta).weight center *
      pairedLift (actualPrimaryLaw cutoffScale parameter beta).weight
        (actualBodyLaw cutoffScale parameter beta).weight
        (fun color position => publicAnchorKernel (Parameters.modulus parameter)
          (Parameters.anchorWidth parameter) color position.val)
        (v7Activation cutoffScale parameter) profile mark center *
      (publicChartEndpointMean cutoffScale parameter mark (charts mark) output +
        rootCompensatorChannel parameter center output)

/-- No response formula is assumed: the positive charts, source averaging,
canonical cancellation and root-only compensation derive precisely ρA. -/
theorem actual_paired_first_response_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
      ∃ charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark,
      ∀ profile : Fin (Parameters.modulus parameter) → ℝ, (∑ mark, profile mark) = 0 →
      ∀ output, actualPairedFirstCount cutoffScale parameter (beta parameter) charts profile output =
        v7Activation cutoffScale parameter * actualResponse cutoffScale parameter profile output := by
  filter_upwards [public_chart_joint_output_eventually cutoffScale hscale,
    actual_reference_laws_eventually cutoffScale hscale beta hbeta,
    actual_primary_probability_eventually cutoffScale hscale beta hbeta,
    actual_anchor_supported_eventually cutoffScale hscale beta hbeta,
    actual_full_anchor_safe_eventually cutoffScale hscale,
    actual_physical_supports_eventually cutoffScale hscale,
    v7Activation_lower_eventually cutoffScale hscale, eventually_ge_atTop 1]
    with parameter hc hl hp hs ha hphysical hactivation hparameter
  choose charts hcharts using hc
  refine ⟨charts, ?_⟩
  intro profile hcanonical output
  have hnonzero : v7Activation cutoffScale parameter ≠ 0 := by
    have hp0 : (0 : ℝ) < parameter := by exact_mod_cast hparameter
    exact ne_of_gt (lt_of_lt_of_le (by positivity : (0 : ℝ) < ((parameter : ℝ) ^ 5)⁻¹) hactivation)
  unfold actualPairedFirstCount
  rw [pairedLift_firstMoment_supported _ _ _ _ _ _ _
    (fun color => by rw [hl.1]; exact (hp.1 color).ne') (hs profile)
    (actualPrimaryLaw cutoffScale parameter (beta parameter)).sum_one
    (actualBodyLaw cutoffScale parameter (beta parameter)).sum_one
    (fun color => (actual_anchor_safe_mass parameter color).1) hcanonical]
  rw [publicChartEndpointMean_profile cutoffScale parameter charts (fun mark first second => hcharts mark (fun _ => 1) first second) profile hcanonical,
    primaryJointNumerator_marginals cutoffScale parameter hphysical.1.1.1 (fun color => (ha color).1),
    rootCompensatorChannel_anchorProfile, actualResponse_physical_formula]
  field_simp

end
end AFT.V7Calibration
