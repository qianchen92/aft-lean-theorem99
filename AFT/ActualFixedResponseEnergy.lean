import AFT.ActualResponseEnergy

/-! # Fixed-root compensation retains the sharp first-response scale -/

namespace AFT.V7Calibration

open Filter GaussianSource
open scoped BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- Any genuine public anchor with the physical width has the same energy
budget, uniformly over its fixed or averaged shift. -/
theorem actual_anchor_energy_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
      ∀ kernel : Fin (Parameters.modulus parameter) → Fin (Parameters.modulus parameter) → ℝ,
      (∀ color output, 0 ≤ kernel color output) →
      (∀ color, ∑ output, kernel color output = 1) →
      (∀ color output, kernel color output ≤ (Parameters.anchorWidth parameter : ℝ)⁻¹) →
      ∀ profile,
      profileSquareNorm (actualReferenceMean cutoffScale parameter (beta parameter))
        (v7Activation cutoffScale parameter • applyAnchor kernel profile) ≤
      4 * (parameter : ℝ) ^ 8 * profileSquareNorm (actualPrimary cutoffScale parameter (beta parameter)) profile := by
  filter_upwards [actual_primary_probability_eventually cutoffScale hscale beta hbeta,
    actual_reference_lower_eventually cutoffScale hscale beta hbeta,
    eventually_ge_atTop 2] with parameter hp hr hp2 kernel hk hm hh profile
  let q : ℝ := Parameters.modulus parameter
  let x : ℝ := parameter
  let a := v7Activation cutoffScale parameter
  let p := actualPrimary cutoffScale parameter (beta parameter)
  let r := actualReferenceMean cutoffScale parameter (beta parameter)
  have hx : 0 < x := by dsimp [x]; exact_mod_cast (by omega : 0 < parameter)
  have hq : 0 < q := by dsimp [q]; exact_mod_cast (Parameters.modulus_prime parameter).pos
  have ha0 : 0 ≤ a := (activation_positive _ _ _ _
    (legFeatureCount_positive cutoffScale parameter hscale (by omega))).le
  have ha1 : a ≤ 1 := activation_le_one _ _ _ _
  have ha2 : a ^ 2 ≤ 1 := by nlinarith
  have hwidth : (Parameters.anchorWidth parameter : ℝ) = x ^ 32 := by
    simp only [Parameters.anchorWidth, Parameters.security_eq parameter hp2, Nat.cast_pow, x]
  have hqw : q ≤ 2 * x ^ 40 := by
    dsimp only [q, x]
    exact_mod_cast (show Parameters.modulus parameter ≤ 2 * parameter ^ 40 by
      simpa only [Parameters.security_eq parameter hp2] using (Parameters.modulus_bounds parameter).2)
  have hrpos (color) : 0 < r color := (by positivity : 0 < 1 / (2 * q)).trans_le (hr color)
  have hbound (output) : applyAnchor kernel p output ≤ (2 * q / x ^ 32) * r output := by
    have ht := applyAnchor_blur_height p kernel _ (fun color => (hp.1 color).le) hp.2 hh output
    rw [hwidth] at ht
    apply ht.trans
    have hl := mul_le_mul_of_nonneg_left (hr output) (by positivity : 0 ≤ 2 * q / x ^ 32)
    apply le_trans _ hl
    change (x ^ 32)⁻¹ ≤ (2 * q / x ^ 32) * (1 / (2 * q))
    apply le_of_eq
    field_simp
  have he := applyAnchor_profileSquareNorm_le p r kernel profile (2 * q / x ^ 32)
    hp.1 hrpos hk hm hbound
  have hn := profileSquareNorm_nonneg p profile (fun color => (hp.1 color).le)
  have hc : a ^ 2 * (2 * q / x ^ 32) ≤ 4 * x ^ 8 := by
    calc
      _ ≤ 1 * (2 * (2 * x ^ 40) / x ^ 32) := by gcongr
      _ = _ := by field_simp; ring
  change profileSquareNorm r (a • applyAnchor kernel profile) ≤ _
  rw [profileSquareNorm_smul]
  exact (mul_le_mul_of_nonneg_left he (sq_nonneg a)).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hc hn)

def fixedResponseEnergyConstant : ℝ := 4 * responseEnergyConstant + 32

/-- The literal root-only anchor at a fixed root. -/
def fixedRootAnchor (parameter : ℕ) (root : ℤ) :
    Fin (Parameters.modulus parameter) → Fin (Parameters.modulus parameter) → ℝ :=
  fun color output => publicAnchorKernel (Parameters.modulus parameter)
    (Parameters.anchorWidth parameter) color ((output.val : ℤ) - root)

def marginalRootAnchor (parameter : ℕ) :
    Fin (Parameters.modulus parameter) → Fin (Parameters.modulus parameter) → ℝ :=
  fun color output => blurredAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
    (fun root : Window (v7RootCutoff parameter) => (root : ℤ))
    (rootMarginal (v7RootWidth parameter) (v7RootCutoff parameter) (Parameters.bodies parameter)
      (Parameters.bodies_positive parameter)) color output.val

/-- The independent reserved root is held fixed. Its correction to the
averaged calibrated response is charged in the same `λ²⁶` square budget. -/
theorem actual_fixed_response_energy_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ root : ℤ, |root| ≤ (v7RootCutoff parameter : ℤ) →
      ∀ profile : Fin (Parameters.modulus parameter) → ℝ,
      profileSquareNorm (actualReferenceMean cutoffScale parameter (beta parameter))
        (v7Activation cutoffScale parameter • GaussianSource.actualResponse cutoffScale parameter profile +
          v7Activation cutoffScale parameter • applyAnchor (marginalRootAnchor parameter) profile -
          v7Activation cutoffScale parameter • applyAnchor (fixedRootAnchor parameter root) profile) ≤
      fixedResponseEnergyConstant * (parameter : ℝ) ^ 26 *
        profileSquareNorm (actualPrimary cutoffScale parameter (beta parameter)) profile := by
  filter_upwards [actual_response_energy_eventually cutoffScale hscale beta hbeta,
    actual_anchor_energy_eventually cutoffScale hscale beta hbeta,
    actual_reference_lower_eventually cutoffScale hscale beta hbeta,
    actual_primary_probability_eventually cutoffScale hscale beta hbeta,
    eventually_ge_atTop 2] with parameter he ha hr hp hp2 root hroot profile
  have hm : (Parameters.safeMargin parameter : ℤ) + v7RootCutoff parameter ≤ Parameters.anchorWidth parameter := by
    have hh : 25 ≤ parameter ^ 30 := by have hh := Nat.pow_le_pow_left hp2 30; omega
    have ht := Nat.mul_le_mul_right (parameter ^ 2) hh
    have hpower : 25 * parameter ^ 2 ≤ Parameters.anchorWidth parameter := by
      simpa only [Parameters.anchorWidth, Parameters.security_eq parameter hp2, ← pow_add] using ht
    simp only [Parameters.safeMargin, Parameters.security_eq parameter hp2, v7RootCutoff]
    omega
  have hw : Parameters.anchorWidth parameter ≠ 0 := by
    unfold Parameters.anchorWidth
    exact pow_ne_zero _ (by have := Parameters.security_ge_two parameter; omega)
  have hfixed := ha (fixedRootAnchor parameter root)
    (fun color output => publicAnchorKernel_nonneg _ _ _ _)
    (fun color => (publicAnchorKernel_safe_mass _ _ (Parameters.safeMargin parameter) root hw
      (Parameters.anchor_clearance parameter) (by positivity) (by linarith) color).1)
    (fun color output => publicAnchorKernel_le _ _ _ _) profile
  have hmarginal := ha (marginalRootAnchor parameter)
    (fun color output => blurredAnchorKernel_nonneg _ _ _ _ _ _)
    (fun color => (blurredAnchorKernel_safe_mass _ _ (Parameters.safeMargin parameter) _ _ hw
      (Parameters.anchor_clearance parameter) (by positivity) (by
        intro sample
        have hh := Finset.mem_Icc.mp sample.property
        have hs := abs_le.mpr hh
        linarith) color).1)
    (fun color output => blurredAnchorKernel_le _ _ _ _ _ _) profile
  let r := actualReferenceMean cutoffScale parameter (beta parameter)
  have hr0 (color) : 0 ≤ r color := le_trans (by positivity) (hr color)
  have hf := profileSquareNorm_four_le r
    (v7Activation cutoffScale parameter • GaussianSource.actualResponse cutoffScale parameter profile)
    (v7Activation cutoffScale parameter • applyAnchor (marginalRootAnchor parameter) profile)
    0 (v7Activation cutoffScale parameter • applyAnchor (fixedRootAnchor parameter root) profile) hr0
  have hz : profileSquareNorm r (0 : Fin (Parameters.modulus parameter) → ℝ) = 0 := by
    simp [profileSquareNorm]
  simp only [add_zero, hz] at hf
  have hx1 : (1 : ℝ) ≤ parameter := by exact_mod_cast (by omega : 1 ≤ parameter)
  have hpow : (parameter : ℝ) ^ 8 ≤ (parameter : ℝ) ^ 26 := pow_le_pow_right₀ hx1 (by norm_num)
  have hn := profileSquareNorm_nonneg (actualPrimary cutoffScale parameter (beta parameter)) profile
    (fun color => (hp.1 color).le)
  have hscalePow := mul_le_mul_of_nonneg_right hpow hn
  have hresp := he profile
  change _ ≤ fixedResponseEnergyConstant * (parameter : ℝ) ^ 26 * _
  unfold fixedResponseEnergyConstant
  nlinarith only [hf, hfixed, hmarginal, hresp, hscalePow]

end
end AFT.V7Calibration
