import AFT.FixedPairedPrimaryDensity
import AFT.ActualPairedLiftSharp

/-! # Sharp primary-reference energy of the actual raw paired numerator -/

namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance fixedPrimaryEnergyFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
attribute [local instance] actualModulusNeZero

/-- The physical four-output raw numerator has Hilbert operator norm
O(λ⁴) in the calibrated primary references. Both local roots stay fixed. -/
theorem fixedPairedChartRaw_primary_energy_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark,
    (∀ mark first second, publicChartRaw cutoffScale parameter mark (charts mark) (fun _ => 1) first second =
      conditionalJointOutput cutoffScale parameter mark (fun _ => 1) first second) →
    ∀ attachedRoot compensatorRoot queue : ℤ,
      |attachedRoot| ≤ (v7RootCutoff parameter : ℤ) → |queue| ≤ (queueCutoff parameter : ℤ) →
    ∀ profile : Fin (Parameters.modulus parameter) → ℝ, (∑ color, profile color) = 0 →
    profileSquareNorm (FiniteDist.independent (fun _ : Fin 4 => actualPrimaryLaw cutoffScale parameter (beta parameter))).weight
      (fixedPairedChartRaw cutoffScale parameter (beta parameter) charts attachedRoot compensatorRoot queue profile) ≤
    (26912768 * (parameter : ℝ) ^ 8) * profileSquareNorm (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight profile := by
  filter_upwards [fixedPairedKernel_primary_density_eventually cutoffScale hscale beta hbeta,
    actual_paired_lift_square_sharp_eventually cutoffScale hscale beta hbeta,
    actual_primary_law_quarter_lower_eventually cutoffScale hscale beta hbeta]
    with parameter hd hl hp charts hc ar cr queue har hqueue profile hcanonical
  let primary := actualPrimaryLaw cutoffScale parameter (beta parameter)
  let body := actualBodyLaw cutoffScale parameter (beta parameter)
  let reference := FiniteDist.independent (fun _ : Fin 4 => primary)
  let kernel := fixedPairedKernel cutoffScale parameter (beta parameter) charts ar cr queue
  let score := fun input : Fin (Parameters.modulus parameter) × Fin (Parameters.modulus parameter) =>
    pairedLift primary.weight body.weight
      (fun color position => publicAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color position.val)
      (v7Activation cutoffScale parameter) profile input.1 input.2
  have hmod : (0 : ℝ) < Parameters.modulus parameter := Nat.cast_pos.mpr (Parameters.modulus_prime parameter).pos
  have href (word) : 0 < reference.weight word := by
    change 0 < ∏ slot : Fin 4, primary.weight (word slot)
    apply Finset.prod_pos
    intro slot _
    exact (by positivity : (0 : ℝ) < 1 / (4 * (Parameters.modulus parameter : ℝ))).trans_le (hp (word slot))
  have he := signedChannel_profile_energy_le (primary.prod body) reference.weight kernel
    (34816 * (parameter : ℝ) ^ 8) href (by positivity)
    (fixedPairedKernel_nonneg cutoffScale parameter (beta parameter) charts ar cr queue)
    (fixedPairedKernel_mass_le cutoffScale parameter (beta parameter) charts ar cr queue)
    (hd charts hc ar cr queue har hqueue) score
  have hraw : (fun word => ∑ input, (primary.prod body).weight input * score input * kernel input word) =
      fixedPairedChartRaw cutoffScale parameter (beta parameter) charts ar cr queue profile := by
    funext word
    exact (fixedPairedChartRaw_expectation _ _ _ _ _ _ _ _ _).symm
  rw [hraw] at he
  have hlift : (primary.prod body).l2Sq score ≤ 773 * profileSquareNorm primary.weight profile := by
    simpa only [FiniteDist.l2Sq, FiniteDist.expectation, Fintype.sum_prod_type, FiniteDist.prod_weight,
      score, primary, body] using hl profile hcanonical
  exact he.trans ((mul_le_mul_of_nonneg_left hlift
    (by positivity : 0 ≤ 34816 * (parameter : ℝ) ^ 8)).trans_eq (by ring))

end
end AFT.V7Calibration
