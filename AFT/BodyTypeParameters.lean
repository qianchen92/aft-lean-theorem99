import AFT.BodyCoreDifference

/-! # The actual V7 body type input and primary fringe exponents -/

namespace AFT.V7Calibration

open Filter GaussianSource
open scoped BigOperators Classical Topology

noncomputable section

theorem bodyCompensation_coarse (cutoffScale : ℝ) (parameter : ℕ) (hscale : 1 ≤ cutoffScale) (hp : 2 ≤ parameter) :
    bodyCompensation parameter cutoffScale ≤ 2 / (parameter : ℝ) ^ 30 := by
  have hp0 : (0 : ℝ) < parameter := by exact_mod_cast (show 0 < parameter by omega)
  have hdim : (parameter : ℝ)^60 ≤ Parameters.dimension parameter := by
    exact_mod_cast (show parameter^60 ≤ Parameters.dimension parameter by simpa only [Parameters.security_eq parameter hp] using (Parameters.dimension_bounds parameter).1)
  have hN : (parameter : ℝ)^60 / 2 ≤ Parameters.bodies parameter := by
    have hi := Parameters.population_identity parameter
    have hm := Parameters.legs_le_half_bodies parameter
    have hh : (Parameters.dimension parameter : ℝ) ≤ 2 * Parameters.bodies parameter := by exact_mod_cast (show Parameters.dimension parameter ≤ 2 * Parameters.bodies parameter by omega)
    linarith
  have ha0 : 0 ≤ v7Activation cutoffScale parameter := (activation_positive _ _ _ _ (legFeatureCount_positive cutoffScale parameter hscale (by omega))).le
  have ha1 : v7Activation cutoffScale parameter ≤ 1 := (activation_le_one_hundredth _ _ _ _).trans (by norm_num)
  unfold bodyCompensation
  have hm : (Parameters.legs parameter : ℝ) = (parameter : ℝ)^30 := by simp only [Parameters.legs, Parameters.security_eq parameter hp, Nat.cast_pow]
  rw [hm]
  calc
    _ ≤ ((parameter : ℝ)^30 * 1) / ((parameter : ℝ)^60 / 2) :=
      div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left ha1 (by positivity)) (by positivity) hN
    _ = _ := by field_simp

theorem body_shift_fraction (cutoffScale : ℝ) (parameter : ℕ) (hp : 2 ≤ parameter)
    (hcut : legCutoff cutoffScale parameter ≤ parameter ^ 2) (shift : ℤ)
    (hshift : |shift| ≤ maxBodyShift cutoffScale parameter) :
    (shift.natAbs : ℝ) / Parameters.modulus parameter ≤ 5 / (parameter : ℝ)^38 ∧
      |shift| + v7RootCutoff parameter ≤ (Parameters.safeMargin parameter : ℤ) := by
  have hp0 : (0 : ℝ) < parameter := by exact_mod_cast (show 0 < parameter by omega)
  have hmax : maxBodyShift cutoffScale parameter ≤ 5 * parameter ^ 2 := by
    simp only [maxBodyShift, v7RootCutoff, queueCutoff]
    omega
  have hnat : shift.natAbs ≤ 5 * parameter ^ 2 := by
    have hh : |shift| ≤ (5 * parameter ^ 2 : ℕ) := hshift.trans (by exact_mod_cast hmax)
    exact_mod_cast (show (shift.natAbs : ℤ) ≤ (5 * parameter^2 : ℕ) by simpa only [Int.natCast_natAbs] using hh)
  have hq : (parameter : ℝ)^40 ≤ Parameters.modulus parameter := by
    exact_mod_cast (show parameter^40 ≤ Parameters.modulus parameter by simpa only [Parameters.security_eq parameter hp] using (Parameters.modulus_bounds parameter).1)
  constructor
  · calc
      _ ≤ (5 * (parameter : ℝ)^2) / (parameter : ℝ)^40 :=
        div_le_div₀ (by positivity) (by exact_mod_cast hnat) (by positivity) hq
      _ = _ := by field_simp
  · have hh : |shift| ≤ (5 * parameter^2 : ℕ) := hshift.trans (by exact_mod_cast hmax)
    simp only [Parameters.safeMargin, Parameters.security_eq parameter hp, v7RootCutoff]
    omega

def centeredBodyFringeSquareConstant : ℝ := 1920 * (Real.exp (2 * Real.pi) / 1000) + 57600

/-- Uniform physical body shifts preserve the `lambda^-38` safe-input
energy and the sharp `lambda^(-289/4)` primary-fringe energy. -/
theorem actual_body_type_power_bounds (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ shift : ℤ, |shift| ≤ maxBodyShift cutoffScale parameter →
      (∑ color, bodyCanonicalInput cutoffScale parameter (beta parameter) shift color) = 0 ∧
      (∀ color, color ∉ safePalette parameter → bodyCanonicalInput cutoffScale parameter (beta parameter) shift color = 0) ∧
      (∀ color, |bodyCanonicalInput cutoffScale parameter (beta parameter) shift color| ≤
        5 * actualBodyCenter cutoffScale parameter (beta parameter) color) ∧
      profileSquareNorm (actualBodyCenter cutoffScale parameter (beta parameter))
        (bodyCanonicalInput cutoffScale parameter (beta parameter) shift) ≤ 1088 / (parameter : ℝ)^38 ∧
      (∑ color, bodyCenteredOutside cutoffScale parameter (beta parameter) shift color) = 0 ∧
      profileSquareNorm (actualPrimary cutoffScale parameter (beta parameter))
        (bodyCenteredOutside cutoffScale parameter (beta parameter) shift) ≤
        centeredBodyFringeSquareConstant / (parameter : ℝ) ^ (289 / 4 : ℝ) := by
  filter_upwards [actual_body_fringe_bounds_eventually cutoffScale hscale beta hbeta,
    actual_centered_body_fringe_eventually cutoffScale hscale beta hbeta,
    actual_body_center_probability_eventually cutoffScale hscale beta hbeta,
    actual_primary_probability_eventually cutoffScale hscale beta hbeta,
    actual_reference_probability_eventually cutoffScale hscale beta hbeta,
    v7Activation_upper_rpow_eventually cutoffScale hscale,
    legCutoff_le_square_eventually cutoffScale hscale, eventually_ge_atTop 2]
    with parameter hf hc hb hp hr ha hcut hlarge shift hshift
  have hp1 : (1 : ℝ) ≤ parameter := by exact_mod_cast (show 1 ≤ parameter by omega)
  have hp0 : (0 : ℝ) < parameter := by positivity
  have hfra := body_shift_fraction cutoffScale parameter hlarge hcut shift hshift
  have hclear : |shift| ≤ (Parameters.safeMargin parameter : ℤ) := by have := hfra.2; omega
  have hin := actual_body_canonical_input_square cutoffScale parameter (beta parameter) shift hp.2
    (fun color => (hp.1 color).le) hb.1 hb.2.1 hb.2.2 (hf shift).2.1
  have hd0 := (bodyCompensation_anchor_bound cutoffScale parameter hscale (by omega)).1
  have hd := bodyCompensation_coarse cutoffScale parameter hscale hlarge
  have hdsharp := bodyCompensation_power_bound parameter cutoffScale hlarge ha
  have hA : (Parameters.anchorWidth parameter : ℝ) = (parameter : ℝ)^32 := by simp only [Parameters.anchorWidth, Parameters.security_eq parameter hlarge, Nat.cast_pow]
  have hq : (Parameters.modulus parameter : ℝ) ≤ 2 * (parameter : ℝ)^40 := by
    exact_mod_cast (show Parameters.modulus parameter ≤ 2 * parameter^40 by simpa only [Parameters.security_eq parameter hlarge] using (Parameters.modulus_bounds parameter).2)
  have hqA : (Parameters.modulus parameter : ℝ) / Parameters.anchorWidth parameter ≤ 2 * (parameter : ℝ)^8 := by
    rw [hA]
    calc
      _ ≤ (2 * (parameter : ℝ)^40) / (parameter : ℝ)^32 := div_le_div_of_nonneg_right hq (by positivity)
      _ = _ := by field_simp
  have hpow8 : 1 ≤ (parameter : ℝ)^8 := one_le_pow₀ hp1
  have hdSq : bodyCompensation parameter cutoffScale ^ 2 ≤ (2 / (parameter : ℝ)^30)^2 := (sq_le_sq₀ hd0 (by positivity)).mpr hd
  have hcomp : 2 * bodyCompensation parameter cutoffScale ^ 2 *
      (8 + 4 * (Parameters.modulus parameter : ℝ) / Parameters.anchorWidth parameter) ≤ 128 / (parameter : ℝ)^38 := by
    have hfactor : 8 + 4 * (Parameters.modulus parameter : ℝ) / Parameters.anchorWidth parameter ≤ 16 * (parameter : ℝ)^8 := by
      simp only [div_eq_mul_inv] at hqA ⊢
      nlinarith
    have hh := mul_le_mul (mul_le_mul_of_nonneg_left hdSq (by norm_num : (0 : ℝ) ≤ 2)) hfactor
      (by positivity : 0 ≤ 8 + 4 * (Parameters.modulus parameter : ℝ) / Parameters.anchorWidth parameter) (by positivity)
    have heq : 2 * (2 / (parameter : ℝ)^30)^2 * (16 * (parameter : ℝ)^8) = 128 / (parameter : ℝ)^52 := by field_simp; ring
    rw [heq] at hh
    exact hh.trans (div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_right₀ hp1 (by omega : 38 ≤ 52)))
  have hsafeSq : profileSquareNorm (actualBodyCenter cutoffScale parameter (beta parameter))
      (bodyCanonicalInput cutoffScale parameter (beta parameter) shift) ≤ 1088 / (parameter : ℝ)^38 := by
    have hh := mul_le_mul_of_nonneg_left hfra.1 (by norm_num : (0 : ℝ) ≤ 192)
    have hi := hin.2
    simp only [div_eq_mul_inv] at hi hh hcomp ⊢
    linarith
  refine ⟨bodyCanonicalInput_mass cutoffScale parameter (beta parameter) shift hb.1 hb.2.2 hclear,
    bodyCanonicalInput_support cutoffScale parameter (beta parameter) shift hb.2.2,
    hin.1, hsafeSq, bodyCenteredOutside_mass cutoffScale parameter (beta parameter) shift hb.2.2 hr.2 hfra.2, ?_⟩
  let mu := bodyOutsideMass parameter (actualBodyCenter cutoffScale parameter (beta parameter)) shift
  have hmu0 : 0 ≤ mu := (bodyOutsideMass_bounds parameter _
    (fun color => (div_nonneg ((actualCoreLaw parameter).nonneg color) (by norm_num)).trans (hb.2.1 color).1) hb.1 shift).1
  have hmu : mu ≤ 60 / (parameter : ℝ)^38 := by
    have hh := (hf shift).1
    have hhh := mul_le_mul_of_nonneg_left hfra.1 (by norm_num : (0 : ℝ) ≤ 12)
    dsimp only [mu]
    simp only [div_eq_mul_inv] at hh hhh ⊢
    linarith
  have hmuSq := (sq_le_sq₀ hmu0 (by positivity)).mpr hmu
  have hfringe : 192 * bodyCompensation parameter cutoffScale * (shift.natAbs : ℝ) / Parameters.modulus parameter ≤
      (1920 * (Real.exp (2 * Real.pi) / 1000)) / (parameter : ℝ) ^ (289 / 4 : ℝ) := by
    have hh := mul_le_mul hdsharp hfra.1 (by positivity : 0 ≤ (shift.natAbs : ℝ) / Parameters.modulus parameter) (by positivity)
    have hh' := mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 192)
    have heq : (parameter : ℝ) ^ (137 / 4 : ℝ) * (parameter : ℝ)^38 = (parameter : ℝ) ^ (289 / 4 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hp0]
      norm_num
    calc
      _ ≤ 192 * (((2 * (Real.exp (2 * Real.pi) / 1000)) / (parameter : ℝ) ^ (137 / 4 : ℝ)) * (5 / (parameter : ℝ)^38)) := by
        convert hh' using 1
        ring
      _ = _ := by rw [← heq]; ring
  have hmassSq : 16 * mu^2 ≤ 57600 / (parameter : ℝ) ^ (289 / 4 : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hmuSq (by norm_num : (0 : ℝ) ≤ 16)
    have heq : 16 * (60 / (parameter : ℝ)^38)^2 = 57600 / (parameter : ℝ)^76 := by field_simp; ring
    rw [heq] at hh
    apply hh.trans (div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_)
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hp1 (by norm_num : (289 / 4 : ℝ) ≤ (76 : ℕ))
  have hc' := (hc shift).2
  change profileSquareNorm _ _ ≤ 192 * bodyCompensation parameter cutoffScale * (shift.natAbs : ℝ) / Parameters.modulus parameter + 16 * mu^2 at hc'
  exact hc'.trans ((add_le_add hfringe hmassSq).trans_eq (by unfold centeredBodyFringeSquareConstant; ring))

end
end AFT.V7Calibration
