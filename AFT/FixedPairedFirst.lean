import AFT.ActualPairedFirst

/-! # The genuine fixed-compensator-root first response and its exact deviation -/

namespace AFT.V7Calibration

open GaussianSource BoundaryCalibration Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance fixedFirstFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
attribute [local instance] actualModulusNeZero

def integerAnchorProfile (parameter : ℕ) (profile : Fin (Parameters.modulus parameter) → ℝ) (output : ℤ) : ℝ :=
  ∑ color, profile color * publicAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color output

def integerAnchorShiftProfile (parameter : ℕ) (shift : ℤ)
    (profile : Fin (Parameters.modulus parameter) → ℝ) (output : Fin (Parameters.modulus parameter)) : ℝ :=
  integerAnchorProfile parameter profile ((output.val : ℤ) - shift)

theorem integerAnchorProfile_outside (parameter : ℕ) (profile : Fin (Parameters.modulus parameter) → ℝ)
    (output : ℤ) (hout : output < 0 ∨ (Parameters.modulus parameter : ℤ) ≤ output) :
    integerAnchorProfile parameter profile output = 0 := by
  apply Finset.sum_eq_zero
  intro color _
  have hw : Parameters.anchorWidth parameter ≠ 0 := by
    unfold Parameters.anchorWidth
    exact pow_ne_zero _ (by have := Parameters.security_ge_two parameter; omega)
  have hh := (publicAnchorKernel_safe_mass (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
    0 0 hw (Parameters.anchor_clearance parameter) (by norm_num) (by simp) color).2 output (by simpa using hout)
  have hz : publicAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color output = 0 := by
    convert hh using 1
    congr 1
    omega
  exact mul_eq_zero_of_right _ hz

theorem singleRoot_anchorProfile (parameter : ℕ) (shift : ℤ)
    (profile : Fin (Parameters.modulus parameter) → ℝ) (output : Fin (Parameters.modulus parameter)) :
    (∑ center : Fin (Parameters.modulus parameter), applyAnchor (fun color position : Fin (Parameters.modulus parameter) => publicAnchorKernel (Parameters.modulus parameter)
        (Parameters.anchorWidth parameter) color position.val) profile center *
      (if (output.val : ℤ) = (center.val : ℤ) + shift then 1 else 0)) =
      integerAnchorShiftProfile parameter shift profile output := by
  have he : applyAnchor (fun color position : Fin (Parameters.modulus parameter) =>
      publicAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color position.val) profile =
      fun center => integerAnchorProfile parameter profile center.val := by
    funext center
    simp only [applyAnchor, integerAnchorProfile, mul_comm]
  rw [he]
  simp only [mul_ite, mul_one, mul_zero]
  exact integerShiftProfile_function parameter (integerAnchorProfile parameter profile)
    (integerAnchorProfile_outside parameter profile) shift output

def fixedPairedFirstCount (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark)
    (compensatorRoot : ℤ) (profile : Fin (Parameters.modulus parameter) → ℝ)
    (output : Fin (Parameters.modulus parameter)) : ℝ :=
  ∑ mark, ∑ center,
    (actualPrimaryLaw cutoffScale parameter beta).weight mark *
      (actualBodyLaw cutoffScale parameter beta).weight center *
      pairedLift (actualPrimaryLaw cutoffScale parameter beta).weight
        (actualBodyLaw cutoffScale parameter beta).weight
        (fun color position => publicAnchorKernel (Parameters.modulus parameter)
          (Parameters.anchorWidth parameter) color position.val)
        (v7Activation cutoffScale parameter) profile mark center *
      (publicChartEndpointMean cutoffScale parameter mark (charts mark) output +
        (if (output.val : ℤ) = (center.val : ℤ) + compensatorRoot then 1 else 0))

/-- At a fixed compensator root the response differs from ρA by exactly
the averaged-root anchor minus that one integer-translated anchor. -/
theorem fixed_paired_first_response_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
      ∃ charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark,
      ∀ profile : Fin (Parameters.modulus parameter) → ℝ, (∑ mark, profile mark) = 0 →
      ∀ compensatorRoot output,
        fixedPairedFirstCount cutoffScale parameter (beta parameter) charts compensatorRoot profile output =
        v7Activation cutoffScale parameter * actualResponse cutoffScale parameter profile output +
          v7Activation cutoffScale parameter *
            (blurredAnchorMean (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
              (fun root : Window (v7RootCutoff parameter) => (root : ℤ))
              (rootMarginal (v7RootWidth parameter) (v7RootCutoff parameter) (Parameters.bodies parameter)
                (Parameters.bodies_positive parameter)) profile output.val -
              integerAnchorShiftProfile parameter compensatorRoot profile output) := by
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
  intro profile hcanonical compensatorRoot output
  have hnonzero : v7Activation cutoffScale parameter ≠ 0 := by
    have hp0 : (0 : ℝ) < parameter := by exact_mod_cast hparameter
    exact ne_of_gt (lt_of_lt_of_le (by positivity : (0 : ℝ) < ((parameter : ℝ) ^ 5)⁻¹) hactivation)
  unfold fixedPairedFirstCount
  rw [pairedLift_firstMoment_supported _ _ _ _ _ _ _
    (fun color => by rw [hl.1]; exact (hp.1 color).ne') (hs profile)
    (actualPrimaryLaw cutoffScale parameter (beta parameter)).sum_one
    (actualBodyLaw cutoffScale parameter (beta parameter)).sum_one
    (fun color => (actual_anchor_safe_mass parameter color).1) hcanonical]
  rw [publicChartEndpointMean_profile cutoffScale parameter charts (fun mark first second => hcharts mark (fun _ => 1) first second) profile hcanonical,
    primaryJointNumerator_marginals cutoffScale parameter hphysical.1.1.1 (fun color => (ha color).1),
    singleRoot_anchorProfile, actualResponse_physical_formula]
  field_simp
  ring

/-- The same exact first response, retaining the defining positive-chart identities. -/
theorem fixed_paired_first_response_with_charts_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
      ∃ charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark,
      (∀ mark attached first second, publicChartRaw cutoffScale parameter mark (charts mark) attached first second =
        conditionalJointOutput cutoffScale parameter mark attached first second) ∧
      ∀ profile : Fin (Parameters.modulus parameter) → ℝ, (∑ mark, profile mark) = 0 →
      ∀ compensatorRoot output,
        fixedPairedFirstCount cutoffScale parameter (beta parameter) charts compensatorRoot profile output =
        v7Activation cutoffScale parameter * actualResponse cutoffScale parameter profile output +
          v7Activation cutoffScale parameter *
            (blurredAnchorMean (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
              (fun root : Window (v7RootCutoff parameter) => (root : ℤ))
              (rootMarginal (v7RootWidth parameter) (v7RootCutoff parameter) (Parameters.bodies parameter)
                (Parameters.bodies_positive parameter)) profile output.val -
              integerAnchorShiftProfile parameter compensatorRoot profile output) := by
  filter_upwards [public_chart_joint_output_eventually cutoffScale hscale,
    actual_reference_laws_eventually cutoffScale hscale beta hbeta,
    actual_primary_probability_eventually cutoffScale hscale beta hbeta,
    actual_anchor_supported_eventually cutoffScale hscale beta hbeta,
    actual_full_anchor_safe_eventually cutoffScale hscale,
    actual_physical_supports_eventually cutoffScale hscale,
    v7Activation_lower_eventually cutoffScale hscale, eventually_ge_atTop 1]
    with parameter hc hl hp hs ha hphysical hactivation hparameter
  choose charts hcharts using hc
  refine ⟨charts, hcharts, ?_⟩
  intro profile hcanonical compensatorRoot output
  have hnonzero : v7Activation cutoffScale parameter ≠ 0 := by
    have hp0 : (0 : ℝ) < parameter := by exact_mod_cast hparameter
    exact ne_of_gt (lt_of_lt_of_le (by positivity : (0 : ℝ) < ((parameter : ℝ) ^ 5)⁻¹) hactivation)
  unfold fixedPairedFirstCount
  rw [pairedLift_firstMoment_supported _ _ _ _ _ _ _
    (fun color => by rw [hl.1]; exact (hp.1 color).ne') (hs profile)
    (actualPrimaryLaw cutoffScale parameter (beta parameter)).sum_one
    (actualBodyLaw cutoffScale parameter (beta parameter)).sum_one
    (fun color => (actual_anchor_safe_mass parameter color).1) hcanonical]
  rw [publicChartEndpointMean_profile cutoffScale parameter charts (fun mark first second => hcharts mark (fun _ => 1) first second) profile hcanonical,
    primaryJointNumerator_marginals cutoffScale parameter hphysical.1.1.1 (fun color => (ha color).1),
    singleRoot_anchorProfile, actualResponse_physical_formula]
  field_simp
  ring

end
end AFT.V7Calibration
