import AFT.BackgroundMeanBounds

/-! # Sharp referenceV7 body mean exponents -/

namespace AFT.V7Calibration

open Filter
open scoped Topology BigOperators

noncomputable section

def bodyMeanRelativeConstant : ℝ := 10 * (Real.exp (2 * Real.pi) / 1000) + 320

def bodyMeanSquareConstant : ℝ := 160 * bodyMeanRelativeConstant

/-- The actual body compensation has exactly the exponent required by
Section 9, using the true activation and actual prime-sized population. -/
theorem bodyCompensation_power_bound (parameter : ℕ) (cutoffScale : ℝ) (hp : 2 ≤ parameter)
    (hactivation : GaussianSource.v7Activation cutoffScale parameter ≤
      (Real.exp (2 * Real.pi) / 1000) / (parameter : ℝ) ^ (17 / 4 : ℝ)) :
    bodyCompensation parameter cutoffScale ≤
      (2 * (Real.exp (2 * Real.pi) / 1000)) / (parameter : ℝ) ^ (137 / 4 : ℝ) := by
  have hp0 : (0 : ℝ) < parameter := by exact_mod_cast (by omega : 0 < parameter)
  have hdim : (parameter : ℝ) ^ 60 ≤ Parameters.dimension parameter := by
    exact_mod_cast (show parameter ^ 60 ≤ Parameters.dimension parameter by
      simpa only [Parameters.security_eq parameter hp] using (Parameters.dimension_bounds parameter).1)
  have hpop : (Parameters.dimension parameter : ℝ) ≤ 2 * Parameters.bodies parameter := by
    have hh := Parameters.population_identity parameter
    have hm := Parameters.legs_le_half_bodies parameter
    exact_mod_cast (by omega : Parameters.dimension parameter ≤ 2 * Parameters.bodies parameter)
  have hN : (parameter : ℝ) ^ 60 / 2 ≤ Parameters.bodies parameter := by linarith
  have hm : (Parameters.legs parameter : ℝ) = (parameter : ℝ) ^ 30 := by
    simp only [Parameters.legs, Parameters.security_eq parameter hp, Nat.cast_pow]
  have heq : (parameter : ℝ) ^ 30 * (parameter : ℝ) ^ (17 / 4 : ℝ) =
      (parameter : ℝ) ^ (137 / 4 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hp0]
    norm_num
  unfold bodyCompensation
  rw [hm]
  calc
    _ ≤ ((parameter : ℝ) ^ 30 * ((Real.exp (2 * Real.pi) / 1000) /
        (parameter : ℝ) ^ (17 / 4 : ℝ))) / ((parameter : ℝ) ^ 60 / 2) := by
      apply div_le_div₀ (by positivity)
        (mul_le_mul_of_nonneg_left hactivation (by positivity)) (by positivity) hN
    _ = _ := by
      rw [← heq]
      have hpow : (parameter : ℝ) ^ 60 = ((parameter : ℝ) ^ 30) ^ 2 := by ring
      rw [hpow]
      field_simp

/-- The explicit relative mean bound and boundary fringe mass combine to
produce the stated squared-norm exponent `289/4`. -/
theorem body_mean_scalar_power_bound (parameter : ℕ) (cutoffScale : ℝ) (hp : 2 ≤ parameter)
    (hmargin : 4 * (Parameters.safeMargin parameter : ℝ) ≤ Parameters.modulus parameter)
    (hactivation : GaussianSource.v7Activation cutoffScale parameter ≤
      (Real.exp (2 * Real.pi) / 1000) / (parameter : ℝ) ^ (17 / 4 : ℝ)) :
    let relative := 5 * bodyCompensation parameter cutoffScale +
      8 * (Parameters.safeMargin parameter : ℝ) /
        ((Parameters.modulus parameter : ℝ) - 2 * Parameters.safeMargin parameter)
    relative ≤ bodyMeanRelativeConstant / (parameter : ℝ) ^ (137 / 4 : ℝ) ∧
    relative * (8 * (Parameters.safeMargin parameter : ℝ) / Parameters.modulus parameter) ≤
      bodyMeanSquareConstant / (parameter : ℝ) ^ (289 / 4 : ℝ) := by
  dsimp only
  have hp' : (1 : ℝ) ≤ parameter := by exact_mod_cast (by omega : 1 ≤ parameter)
  have hp0 : (0 : ℝ) < parameter := by positivity
  have hq : (parameter : ℝ) ^ 40 ≤ Parameters.modulus parameter := by
    exact_mod_cast (show parameter ^ 40 ≤ Parameters.modulus parameter by
      simpa only [Parameters.security_eq parameter hp] using (Parameters.modulus_bounds parameter).1)
  have hq0 : (0 : ℝ) < Parameters.modulus parameter := lt_of_lt_of_le (by positivity) hq
  have hm : (Parameters.safeMargin parameter : ℝ) = 20 * (parameter : ℝ) ^ 2 := by
    simp only [Parameters.safeMargin, Parameters.security_eq parameter hp, Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat]
  have hsafe : (parameter : ℝ) ^ 40 / 2 ≤
      (Parameters.modulus parameter : ℝ) - 2 * Parameters.safeMargin parameter := by linarith
  have hfringe : 8 * (Parameters.safeMargin parameter : ℝ) / Parameters.modulus parameter ≤
      160 / (parameter : ℝ) ^ 38 := by
    rw [hm]
    calc
      _ ≤ (8 * (20 * (parameter : ℝ) ^ 2)) / (parameter : ℝ) ^ 40 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hq
      _ = _ := by field_simp; ring
  have hsafeBound : 8 * (Parameters.safeMargin parameter : ℝ) /
        ((Parameters.modulus parameter : ℝ) - 2 * Parameters.safeMargin parameter) ≤
      320 / (parameter : ℝ) ^ 38 := by
    calc
      _ ≤ (8 * (Parameters.safeMargin parameter : ℝ)) / ((parameter : ℝ) ^ 40 / 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hsafe
      _ = _ := by rw [hm]; field_simp; ring
  have hconvert : 320 / (parameter : ℝ) ^ 38 ≤ 320 / (parameter : ℝ) ^ (137 / 4 : ℝ) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hp' (by norm_num : (137 / 4 : ℝ) ≤ (38 : ℕ))
  have hdelta := bodyCompensation_power_bound parameter cutoffScale hp hactivation
  have hrel : 5 * bodyCompensation parameter cutoffScale +
      8 * (Parameters.safeMargin parameter : ℝ) /
        ((Parameters.modulus parameter : ℝ) - 2 * Parameters.safeMargin parameter) ≤
      bodyMeanRelativeConstant / (parameter : ℝ) ^ (137 / 4 : ℝ) := by
    have hh := add_le_add (mul_le_mul_of_nonneg_left hdelta (by norm_num : (0 : ℝ) ≤ 5)) (hsafeBound.trans hconvert)
    convert hh using 1
    unfold bodyMeanRelativeConstant
    ring
  refine ⟨hrel, ?_⟩
  calc
    _ ≤ (bodyMeanRelativeConstant / (parameter : ℝ) ^ (137 / 4 : ℝ)) *
        (160 / (parameter : ℝ) ^ 38) := mul_le_mul hrel hfringe (by positivity) (by unfold bodyMeanRelativeConstant; positivity)
    _ = _ := by
      have heq : (parameter : ℝ) ^ (137 / 4 : ℝ) * (parameter : ℝ) ^ 38 =
          (parameter : ℝ) ^ (289 / 4 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hp0]
        norm_num
      unfold bodyMeanSquareConstant
      rw [← heq]
      ring

/-- The original Section 9 exponents for the actual body and reference
means, with all analytic and numerical bounds proved. -/
theorem body_reference_power_bounds_eventually {σ τ : ℕ → Type*}
    [∀ parameter, Fintype (σ parameter)] [∀ parameter, Fintype (τ parameter)]
    (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ) (boundary : ℕ → ℤ)
    (bodyShifts : (parameter : ℕ) → σ parameter → ℤ)
    (bodyLaw : (parameter : ℕ) → FiniteDist (σ parameter))
    (startsPlus startsMinus sources : (parameter : ℕ) → τ parameter → ℤ)
    (sourceLaw : (parameter : ℕ) → FiniteDist (τ parameter))
    (hmodel : ∀ᶠ parameter in atTop,
      PhysicalSupports parameter cutoffScale (boundary parameter)
        (startsPlus parameter) (startsMinus parameter) (sources parameter) ∧
      (∀ index, |bodyShifts parameter index| ≤ (Parameters.safeMargin parameter : ℤ) - boundary parameter) ∧
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
      let p := primary parameter cutoffScale (beta parameter) (boundary parameter)
        (bodyShifts parameter) (bodyLaw parameter) (startsPlus parameter) (startsMinus parameter)
        (sources parameter) (sourceLaw parameter)
      let B := bodyMean parameter (bodyShifts parameter) (bodyLaw parameter)
      let r := referenceMean parameter cutoffScale (beta parameter) (boundary parameter)
      (∀ color, |B color - r color| ≤
        (bodyMeanRelativeConstant / (parameter : ℝ) ^ (137 / 4 : ℝ)) * p color) ∧
      profileSquareNorm p (B - r) ≤
        bodyMeanSquareConstant / (parameter : ℝ) ^ (289 / 4 : ℝ) := by
  filter_upwards [body_reference_bounds_eventually cutoffScale hscale beta boundary bodyShifts bodyLaw
    startsPlus startsMinus sources sourceLaw hmodel,
    primary_estimates_eventually cutoffScale hscale beta boundary bodyShifts bodyLaw startsPlus startsMinus sources sourceLaw hmodel,
    GaussianSource.v7Activation_upper_rpow_eventually cutoffScale hscale,
    v7_primaryCalibration_clearance_eventually cutoffScale hscale boundary (hmodel.mono fun _ h => h.1.1),
    eventually_ge_atTop 2] with parameter hb hp ha hclear hlarge
  dsimp only at hb hp ⊢
  have hs := body_mean_scalar_power_bound parameter cutoffScale hlarge (by exact_mod_cast hclear.1) ha
  refine ⟨?_, hb.2.trans hs.2⟩
  intro color
  apply (hb.1 color).trans
  apply mul_le_mul_of_nonneg_right hs.1
  exact le_trans (by positivity) (hp.1 color)


end

end AFT.V7Calibration
