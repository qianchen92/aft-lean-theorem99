import AFT.ResponseEnergy
import AFT.ActualResponseFormula
import AFT.PrimarySup
import AFT.V7ReferenceLower
import AFT.ActivationUpper

/-! # Sharp first-degree energy of the actual calibrated response -/

namespace AFT.V7Calibration

open Filter GaussianSource
open scoped BigOperators Classical Topology
noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

def responseEnergyConstant : ℝ := 48 * (Real.exp (2 * Real.pi) / 1000) + 544

theorem applyAnchor_blur_height {Color : Type*} [Fintype Color]
    (primary : Color → ℝ) (kernel : Color → Color → ℝ) (height : ℝ)
    (hp : ∀ color, 0 ≤ primary color) (hm : ∑ color, primary color = 1)
    (hk : ∀ color output, kernel color output ≤ height) (output : Color) :
    applyAnchor kernel primary output ≤ height := by
  unfold applyAnchor
  calc
    _ ≤ ∑ color, height * primary color := Finset.sum_le_sum fun color _ =>
      mul_le_mul_of_nonneg_right (hk color output) (hp color)
    _ = height := by rw [← Finset.mul_sum, hm, mul_one]

/-- This is the physical response multiplied by its true activation, in
the actual calibrated reference norm. No response-energy hypothesis is used. -/
theorem actual_response_energy_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ profile : Fin (Parameters.modulus parameter) → ℝ,
      profileSquareNorm (actualReferenceMean cutoffScale parameter (beta parameter))
        (v7Activation cutoffScale parameter • GaussianSource.actualResponse cutoffScale parameter profile) ≤
      responseEnergyConstant * (parameter : ℝ) ^ 26 *
        profileSquareNorm (actualPrimary cutoffScale parameter (beta parameter)) profile := by
  have hs := base_sign_estimates_eventually cutoffScale hscale (boundaryHalf cutoffScale)
    (bodyShift cutoffScale) (bodyBlur cutoffScale) (startsPlus cutoffScale) (startsMinus cutoffScale)
    (pairSourceShift cutoffScale) (pairSourceLaw cutoffScale)
    ((actual_physical_supports_eventually cutoffScale hscale).mono fun _ h => h.1)
  filter_upwards [hs, actual_anchor_margin_eventually cutoffScale hscale,
    actual_primary_upper_eventually cutoffScale hscale beta hbeta,
    actual_base_primary_upper_eventually cutoffScale hscale,
    actual_primary_probability_eventually cutoffScale hscale beta hbeta,
    actual_reference_lower_eventually cutoffScale hscale beta hbeta,
    v7Activation_upper_rpow_eventually cutoffScale hscale, eventually_ge_atTop 2]
    with parameter hs hm hpmax hbmax hp hr ha hp2 profile
  let x : ℝ := parameter
  let q : ℝ := Parameters.modulus parameter
  let a := v7Activation cutoffScale parameter
  let p := actualPrimary cutoffScale parameter (beta parameter)
  let r := actualReferenceMean cutoffScale parameter (beta parameter)
  let v := signResponse parameter cutoffScale (boundaryHalf cutoffScale parameter)
    (startsPlus cutoffScale parameter) (startsMinus cutoffScale parameter)
    (pairSourceShift cutoffScale parameter) (pairSourceLaw cutoffScale parameter)
  let first := fun color output : Fin (Parameters.modulus parameter) =>
    blurredAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
      (fun sample => bodyShift cutoffScale parameter sample.1) (pairSourceLaw cutoffScale parameter) color output.val
  let second := fun color output : Fin (Parameters.modulus parameter) =>
    blurredAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
      (compensatorRootShift cutoffScale parameter) (pairSourceLaw cutoffScale parameter) color output.val
  let c : ℝ := Real.exp (2 * Real.pi) / 1000
  have hx : 0 < x := by dsimp [x]; exact_mod_cast (by omega : 0 < parameter)
  have hx1 : 1 ≤ x := by dsimp [x]; exact_mod_cast (by omega : 1 ≤ parameter)
  have hq : 0 < q := by dsimp [q]; exact_mod_cast (Parameters.modulus_prime parameter).pos
  have ha0 : 0 < a := activation_positive _ _ _ _
    (legFeatureCount_positive cutoffScale parameter hscale (by omega))
  have ha1 : a ≤ 1 := activation_le_one _ _ _ _
  have ha2 : a ^ 2 ≤ 1 := by nlinarith
  have hwidth : (Parameters.anchorWidth parameter : ℝ) = x ^ 32 := by
    simp only [Parameters.anchorWidth, Parameters.security_eq parameter hp2, Nat.cast_pow, x]
  have hqw : q ≤ 2 * x ^ 40 := by
    dsimp only [q, x]
    exact_mod_cast (show Parameters.modulus parameter ≤ 2 * parameter ^ 40 by
      simpa only [Parameters.security_eq parameter hp2] using (Parameters.modulus_bounds parameter).2)
  have hn : (Parameters.dimension parameter : ℝ) = q * x ^ 20 := by
    simp only [Parameters.dimension, Parameters.meanDensity, Parameters.security_eq parameter hp2,
      Nat.cast_mul, Nat.cast_pow, q, x]
  have hlegs : (Parameters.legs parameter : ℝ) = x ^ 30 := by
    simp only [Parameters.legs, Parameters.security_eq parameter hp2, Nat.cast_pow, x]
  have hrpos (color) : 0 < r color := (by positivity : 0 < 1 / (2 * q)).trans_le (hr color)
  have hapos : 0 ≤ c := by dsimp [c]; positivity
  have hau : a ≤ c / x ^ 4 := by
    apply ha.trans
    apply div_le_div_of_nonneg_left hapos (by positivity)
    rw [← Real.rpow_natCast x 4]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hvmax (color) : |v color| ≤ 2 / x ^ 10 := by
    have hh := (hs.2.1 color).trans (mul_le_mul_of_nonneg_left (hbmax color) ha0.le)
    change |v color| ≤ a * (2 * Parameters.dimension parameter /
      (Parameters.legs parameter * a * Parameters.modulus parameter)) at hh
    rw [hn, hlegs] at hh
    exact hh.trans_eq (by change a * (2 * (q * x ^ 20) / (x ^ 30 * a * q)) = _; field_simp)
  have hdiag (color) : p color ≤ (6 * q / (a * x ^ 10)) * r color := by
    apply (hpmax color).trans
    have hh := mul_le_mul_of_nonneg_left (hr color) (by positivity : 0 ≤ 6 * q / (a * x ^ 10))
    apply le_trans _ hh
    change 3 / (a * x ^ 10) ≤ (6 * q / (a * x ^ 10)) * (1 / (2 * q))
    apply le_of_eq
    field_simp
    ring
  have hv (color) : |v color| ≤ (4 * q / x ^ 10) * r color := by
    apply (hvmax color).trans
    have hh := mul_le_mul_of_nonneg_left (hr color) (by positivity : 0 ≤ 4 * q / x ^ 10)
    apply le_trans _ hh
    change 2 / x ^ 10 ≤ (4 * q / x ^ 10) * (1 / (2 * q))
    apply le_of_eq
    field_simp
    ring
  have hv1 : (∑ color, |v color|) ≤ 32 * (x ^ 32 / q) := by
    simpa only [hwidth] using hs.2.2.1
  have hw : Parameters.anchorWidth parameter ≠ 0 := by
    unfold Parameters.anchorWidth
    exact pow_ne_zero _ (by have := Parameters.security_ge_two parameter; omega)
  have hfm (color) : ∑ output, first color output = 1 :=
    (blurredAnchorKernel_safe_mass _ _ (Parameters.safeMargin parameter) _ _ hw
      (Parameters.anchor_clearance parameter) (by positivity) hm.1 color).1
  have hsm (color) : ∑ output, second color output = 1 :=
    (blurredAnchorKernel_safe_mass _ _ (Parameters.safeMargin parameter) _ _ hw
      (Parameters.anchor_clearance parameter) (by positivity) hm.2 color).1
  have hanchor (kernel : Fin (Parameters.modulus parameter) → Fin (Parameters.modulus parameter) → ℝ)
      (hk : ∀ color output, kernel color output ≤ (Parameters.anchorWidth parameter : ℝ)⁻¹) (output) :
      applyAnchor kernel p output ≤ (2 * q / x ^ 32) * r output := by
    have hh := applyAnchor_blur_height p kernel _ (fun color => (hp.1 color).le) hp.2 hk output
    rw [hwidth] at hh
    apply hh.trans
    have hl := mul_le_mul_of_nonneg_left (hr output) (by positivity : 0 ≤ 2 * q / x ^ 32)
    apply le_trans _ hl
    change (x ^ 32)⁻¹ ≤ (2 * q / x ^ 32) * (1 / (2 * q))
    apply le_of_eq
    field_simp
  have he := four_channel_response_energy p r (paletteSign (Parameters.modulus parameter)) v first second
    a (6 * q / (a * x ^ 10)) (4 * q / x ^ 10) (32 * (x ^ 32 / q)) (2 * q / x ^ 32)
    hp.1 hp.2 hrpos hdiag (paletteSign_abs_le _) (by positivity) hv hv1
    (fun color output => blurredAnchorKernel_nonneg _ _ _ _ _ _)
    (fun color output => blurredAnchorKernel_nonneg _ _ _ _ _ _)
    hfm hsm (hanchor first (fun color output => blurredAnchorKernel_le _ _ _ _ _ _))
    (hanchor second (fun color output => blurredAnchorKernel_le _ _ _ _ _ _)) profile
  have hformula : a • GaussianSource.actualResponse cutoffScale parameter profile =
      a • profile + (signFunctional (paletteSign (Parameters.modulus parameter)) profile) • v +
        a • applyAnchor first profile - a • applyAnchor second profile := by
    funext output
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, actualResponse_apply_formula,
      signFunctional, applyAnchor]
    change a * (profile output + a⁻¹ * (∑ color, paletteSign (Parameters.modulus parameter) color * profile color) * v output +
      ∑ color, profile color * (first color output - second color output)) = _
    simp only [mul_sub, Finset.sum_sub_distrib]
    have hm1 : (∑ color, profile color * first color output) = ∑ color, first color output * profile color := by
      apply Finset.sum_congr rfl; intro color _; ring
    have hm2 : (∑ color, profile color * second color output) = ∑ color, second color output * profile color := by
      apply Finset.sum_congr rfl; intro color _; ring
    rw [hm1, hm2]
    field_simp
    ring
  have hdiagcost : a ^ 2 * (6 * q / (a * x ^ 10)) ≤ 12 * c * x ^ 26 := by
    have heq : a ^ 2 * (6 * q / (a * x ^ 10)) = 6 * a * q / x ^ 10 := by field_simp
    rw [heq]
    calc
      _ ≤ 6 * (c / x ^ 4) * (2 * x ^ 40) / x ^ 10 := by gcongr
      _ = _ := by field_simp; ring
  have hsigncost : (4 * q / x ^ 10) * (32 * (x ^ 32 / q)) ≤ 128 * x ^ 26 := by
    have heq : (4 * q / x ^ 10) * (32 * (x ^ 32 / q)) = 128 * x ^ 22 := by field_simp; ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx1 (by norm_num : 22 ≤ 26)) (by norm_num)
  have hanchorcost : 2 * a ^ 2 * (2 * q / x ^ 32) ≤ 8 * x ^ 26 := by
    calc
      _ ≤ 2 * 1 * (2 * (2 * x ^ 40) / x ^ 32) := by gcongr
      _ = 8 * x ^ 8 := by field_simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx1 (by norm_num : 8 ≤ 26)) (by norm_num)
  change profileSquareNorm r (a • GaussianSource.actualResponse cutoffScale parameter profile) ≤ _
  rw [hformula]
  apply he.trans
  apply mul_le_mul_of_nonneg_right _ (profileSquareNorm_nonneg p profile (fun color => (hp.1 color).le))
  change _ ≤ responseEnergyConstant * x ^ 26
  unfold responseEnergyConstant
  change _ ≤ (48 * c + 544) * x ^ 26
  nlinarith only [hdiagcost, hsigncost, hanchorcost]

end
end AFT.V7Calibration
