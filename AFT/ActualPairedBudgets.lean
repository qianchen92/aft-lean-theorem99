import AFT.FixedPairedMoments
import AFT.FixedPairedEnergy
import AFT.ActualFixedResponseEnergy
import AFT.SignedFirstCoefficient

/-! # Actual first and higher coefficient budgets of every paired physical block -/

namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration PhysicalBlockTensors Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance actualPairedBudgetsFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
attribute [local instance] actualModulusNeZero

theorem fixedRootAnchor_profile (parameter : ℕ) (root : ℤ)
    (profile : Fin (Parameters.modulus parameter) → ℝ) :
    applyAnchor (fixedRootAnchor parameter root) profile = integerAnchorShiftProfile parameter root profile := by
  funext output
  simp only [applyAnchor, fixedRootAnchor, integerAnchorShiftProfile, integerAnchorProfile, mul_comm]

theorem marginalRootAnchor_profile (parameter : ℕ)
    (profile : Fin (Parameters.modulus parameter) → ℝ) (output : Fin (Parameters.modulus parameter)) :
    applyAnchor (marginalRootAnchor parameter) profile output =
      blurredAnchorMean (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
        (fun root : Window (v7RootCutoff parameter) => (root : ℤ))
        (rootMarginal (v7RootWidth parameter) (v7RootCutoff parameter) (Parameters.bodies parameter)
          (Parameters.bodies_positive parameter)) profile output.val := by
  simp only [applyAnchor, marginalRootAnchor, blurredAnchorMean, mul_comm]

/-- Positive chart families are constructed once, and the real signed
four-output coefficients obey their first/higher budgets uniformly over
both fixed root coordinates and the common queue. -/
theorem actual_paired_degree_budgets_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
      ∃ charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark,
      (∀ mark attached first second, publicChartRaw cutoffScale parameter mark (charts mark) attached first second =
        conditionalJointOutput cutoffScale parameter mark attached first second) ∧
      ∀ attachedRoot compensatorRoot queue : ℤ,
        |attachedRoot| ≤ (v7RootCutoff parameter : ℤ) →
        |compensatorRoot| ≤ (v7RootCutoff parameter : ℤ) → |queue| ≤ (queueCutoff parameter : ℤ) →
      ∀ profile : Fin (Parameters.modulus parameter) → ℝ, (∑ color, profile color) = 0 →
      (∑ word, fixedPairedChartRaw cutoffScale parameter (beta parameter) charts attachedRoot compensatorRoot queue profile word) = 0 ∧
      BlockFock.tensorEnergy (LocalTensors.degreeTensor
        (fun _ : Fin 4 => actualReferenceLaw cutoffScale parameter (beta parameter))
        (fixedPairedChartRaw cutoffScale parameter (beta parameter) charts attachedRoot compensatorRoot queue profile) 1) ≤
          (fixedResponseEnergyConstant * (parameter : ℝ) ^ 26) *
            profileSquareNorm (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight profile ∧
      ∀ degree : ℕ, BlockFock.tensorEnergy (LocalTensors.degreeTensor
        (fun _ : Fin 4 => actualReferenceLaw cutoffScale parameter (beta parameter))
        (fixedPairedChartRaw cutoffScale parameter (beta parameter) charts attachedRoot compensatorRoot queue profile) degree) ≤
          (409600 * (parameter : ℝ) ^ 46) *
            profileSquareNorm (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight profile := by
  filter_upwards [fixed_paired_first_response_with_charts_eventually cutoffScale hscale beta hbeta,
    fixedPairedChartRaw_mass_eventually cutoffScale hscale beta hbeta,
    fixedPairedChartRaw_count_eventually cutoffScale hscale beta hbeta,
    fixedPairedChartRaw_degree_energy_eventually cutoffScale hscale beta hbeta,
    actual_fixed_response_energy_eventually cutoffScale hscale beta hbeta,
    actual_reference_lower_eventually cutoffScale hscale beta hbeta,
    actual_reference_laws_eventually cutoffScale hscale beta hbeta]
    with parameter hc hm hcount hdegree hfirst hr hl
  obtain ⟨charts, hcharts, hformula⟩ := hc
  refine ⟨charts, hcharts, ?_⟩
  intro ar cr queue har hcr hqueue profile hcanonical
  have hmass := hm charts ar cr queue hcr profile hcanonical
  refine ⟨hmass, ?_, hdegree charts (fun mark first second => hcharts mark (fun _ => 1) first second)
    ar cr queue har hqueue profile hcanonical⟩
  have hmod : (0 : ℝ) < Parameters.modulus parameter := Nat.cast_pos.mpr (Parameters.modulus_prime parameter).pos
  have href (color) : 0 < (actualReferenceLaw cutoffScale parameter (beta parameter)).weight color := by
    rw [hl.2.2]
    exact (by positivity : (0 : ℝ) < 1 / (2 * (Parameters.modulus parameter : ℝ))).trans_le (hr color)
  rw [LocalTensors.degreeTensor_one_energy_zero_mass _ href _ hmass]
  have hprofile : LocalTensors.signedColorCount
      (fixedPairedChartRaw cutoffScale parameter (beta parameter) charts ar cr queue profile) =
      v7Activation cutoffScale parameter • actualResponse cutoffScale parameter profile +
        v7Activation cutoffScale parameter • applyAnchor (marginalRootAnchor parameter) profile -
        v7Activation cutoffScale parameter • applyAnchor (fixedRootAnchor parameter cr) profile := by
    funext output
    rw [← fourOutputCount_eq_signedColorCount]
    rw [hcount charts ar cr queue hcr profile hcanonical output,
      hformula profile hcanonical cr output]
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      marginalRootAnchor_profile, fixedRootAnchor_profile]
    ring
  rw [hprofile, hl.1, hl.2.2]
  exact hfirst cr hcr profile

end
end AFT.V7Calibration
