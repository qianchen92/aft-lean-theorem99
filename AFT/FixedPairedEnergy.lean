import AFT.FixedPairedDensity
import AFT.LocalTensors

/-! # Full signed energy of the genuine fixed-root paired block -/

namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance fixedEnergyFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
attribute [local instance] actualModulusNeZero

/-- The real four-output signed channel has a uniform degree-independent
square budget. The primary score can be arbitrary except for canonicality. -/
theorem fixedPairedChartRaw_energy_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
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
    profileSquareNorm (FiniteDist.independent (fun _ : Fin 4 => actualReferenceLaw cutoffScale parameter (beta parameter))).weight
      (fixedPairedChartRaw cutoffScale parameter (beta parameter) charts attachedRoot compensatorRoot queue profile) ≤
    (25600 * (parameter : ℝ) ^ 46) * profileSquareNorm (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight profile := by
  filter_upwards [fixedPairedKernel_density_power_eventually cutoffScale hscale beta hbeta,
    actual_paired_lift_square_eventually cutoffScale hscale beta hbeta,
    actual_reference_lower_eventually cutoffScale hscale beta hbeta,
    actual_reference_laws_eventually cutoffScale hscale beta hbeta, eventually_ge_atTop 2]
    with parameter hd hl hr hw hparameter charts hc ar cr queue har hqueue profile hcanonical
  let primary := actualPrimaryLaw cutoffScale parameter (beta parameter)
  let body := actualBodyLaw cutoffScale parameter (beta parameter)
  let reference := FiniteDist.independent (fun _ : Fin 4 => actualReferenceLaw cutoffScale parameter (beta parameter))
  let kernel := fixedPairedKernel cutoffScale parameter (beta parameter) charts ar cr queue
  let score := fun input : Fin (Parameters.modulus parameter) × Fin (Parameters.modulus parameter) =>
    pairedLift primary.weight body.weight
      (fun color position => publicAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color position.val)
      (v7Activation cutoffScale parameter) profile input.1 input.2
  have hmod : (0 : ℝ) < Parameters.modulus parameter := Nat.cast_pos.mpr (Parameters.modulus_prime parameter).pos
  have href (word) : 0 < reference.weight word := by
    change 0 < ∏ slot : Fin 4, (actualReferenceLaw cutoffScale parameter (beta parameter)).weight (word slot)
    apply Finset.prod_pos
    intro slot _
    rw [hw.2.2]
    exact (by positivity : (0 : ℝ) < 1 / (2 * (Parameters.modulus parameter : ℝ))).trans_le (hr (word slot))
  have he := signedChannel_profile_energy_le (primary.prod body) reference.weight kernel
    (5120 * (parameter : ℝ) ^ 38) href (by positivity)
    (fixedPairedKernel_nonneg cutoffScale parameter (beta parameter) charts ar cr queue)
    (fixedPairedKernel_mass_le cutoffScale parameter (beta parameter) charts ar cr queue)
    (hd charts hc ar cr queue har hqueue) score
  have hraw : (fun word => ∑ input, (primary.prod body).weight input * score input * kernel input word) =
      fixedPairedChartRaw cutoffScale parameter (beta parameter) charts ar cr queue profile := by
    funext word
    exact (fixedPairedChartRaw_expectation _ _ _ _ _ _ _ _ _).symm
  rw [hraw] at he
  have hlift : (primary.prod body).l2Sq score ≤
      (1 + v7Activation cutoffScale parameter ^ 2 * (2 * Parameters.modulus parameter / (Parameters.anchorWidth parameter : ℝ))) *
        profileSquareNorm primary.weight profile := by
    simpa only [FiniteDist.l2Sq, FiniteDist.expectation, Fintype.sum_prod_type, FiniteDist.prod_weight,
      score, primary, body] using hl profile hcanonical
  let x : ℝ := parameter
  have hx : 0 < x := by dsimp [x]; exact_mod_cast (by omega : 0 < parameter)
  have hx1 : 1 ≤ x := by dsimp [x]; exact_mod_cast (by omega : 1 ≤ parameter)
  have hq : (Parameters.modulus parameter : ℝ) ≤ 2 * x ^ 40 := by
    dsimp only [x]
    exact_mod_cast (show Parameters.modulus parameter ≤ 2 * parameter ^ 40 by
      simpa only [Parameters.security_eq parameter hparameter] using (Parameters.modulus_bounds parameter).2)
  have hA : (Parameters.anchorWidth parameter : ℝ) = x ^ 32 := by
    simp only [Parameters.anchorWidth, Parameters.security_eq parameter hparameter, Nat.cast_pow, x]
  have ha0 : 0 ≤ v7Activation cutoffScale parameter := by
    unfold v7Activation GaussianSource.activation
    exact mul_nonneg (by positivity) (FiniteDist.nonneg _ _)
  have ha1 : v7Activation cutoffScale parameter ≤ 1 := activation_le_one _ _ _ _
  have ha2 : v7Activation cutoffScale parameter ^ 2 ≤ 1 := by nlinarith
  have hratio : 2 * (Parameters.modulus parameter : ℝ) / Parameters.anchorWidth parameter ≤ 4 * x ^ 8 := by
    rw [hA]
    calc
      _ ≤ 2 * (2 * x ^ 40) / x ^ 32 := by gcongr
      _ = _ := by field_simp; ring
  have hfactor : 1 + v7Activation cutoffScale parameter ^ 2 *
      (2 * Parameters.modulus parameter / (Parameters.anchorWidth parameter : ℝ)) ≤ 5 * x ^ 8 := by
    have hh := mul_le_mul ha2 hratio (by positivity : (0 : ℝ) ≤ 2 * Parameters.modulus parameter / (Parameters.anchorWidth parameter : ℝ)) (by norm_num : (0 : ℝ) ≤ 1)
    have hx8 : 1 ≤ x ^ 8 := one_le_pow₀ hx1
    nlinarith
  have hn := profileSquareNorm_nonneg primary.weight profile primary.nonneg
  calc
    _ ≤ (5120 * x ^ 38) * (primary.prod body).l2Sq score := he
    _ ≤ (5120 * x ^ 38) * ((5 * x ^ 8) * profileSquareNorm primary.weight profile) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact hlift.trans (mul_le_mul_of_nonneg_right hfactor hn)
    _ = _ := by dsimp [x, primary]; ring

/-- Every actual homogeneous coefficient inherits the same fixed four-slot
factor, without any dependence on the number of colors. -/
theorem fixedPairedChartRaw_degree_energy_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
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
    ∀ degree : ℕ,
      BlockFock.tensorEnergy (LocalTensors.degreeTensor
        (fun _ : Fin 4 => actualReferenceLaw cutoffScale parameter (beta parameter))
        (fixedPairedChartRaw cutoffScale parameter (beta parameter) charts attachedRoot compensatorRoot queue profile) degree) ≤
      (409600 * (parameter : ℝ) ^ 46) * profileSquareNorm (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight profile := by
  filter_upwards [fixedPairedChartRaw_energy_eventually cutoffScale hscale beta hbeta,
    actual_reference_lower_eventually cutoffScale hscale beta hbeta,
    actual_reference_laws_eventually cutoffScale hscale beta hbeta] with parameter he hr hl charts hc ar cr queue har hq profile hp degree
  have hmod : (0 : ℝ) < Parameters.modulus parameter := Nat.cast_pos.mpr (Parameters.modulus_prime parameter).pos
  have href (slot : Fin 4) (color) : 0 < (actualReferenceLaw cutoffScale parameter (beta parameter)).weight color := by
    rw [hl.2.2]
    exact (by positivity : (0 : ℝ) < 1 / (2 * (Parameters.modulus parameter : ℝ))).trans_le (hr color)
  have hh := LocalTensors.degreeTensor_energy_le (fun _ : Fin 4 => actualReferenceLaw cutoffScale parameter (beta parameter)) href
    (fixedPairedChartRaw cutoffScale parameter (beta parameter) charts ar cr queue profile) degree
  change _ ≤ (2 : ℝ) ^ Fintype.card (Fin 4) * densitySquareNorm _ _ at hh
  rw [densityScore_square] at hh
  norm_num only [Fintype.card_fin, Nat.reducePow] at hh
  calc
    _ ≤ 16 * profileSquareNorm (FiniteDist.independent (fun _ : Fin 4 => actualReferenceLaw cutoffScale parameter (beta parameter))).weight
        (fixedPairedChartRaw cutoffScale parameter (beta parameter) charts ar cr queue profile) := hh
    _ ≤ 16 * ((25600 * (parameter : ℝ) ^ 46) * profileSquareNorm (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight profile) :=
      mul_le_mul_of_nonneg_left (he charts hc ar cr queue har hq profile hp) (by norm_num)
    _ = _ := by ring

end
end AFT.V7Calibration
