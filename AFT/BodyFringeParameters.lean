import AFT.BodyTranslation

/-! # Instantiating every body fringe bound at the actual V7 laws -/

namespace AFT.V7Calibration

open Filter GaussianSource
open scoped BigOperators Classical Topology

noncomputable section

theorem bodyCompensation_anchor_bound (cutoffScale : ℝ) (parameter : ℕ) (hscale : 1 ≤ cutoffScale)
    (hp : 1 ≤ parameter) :
    0 ≤ bodyCompensation parameter cutoffScale ∧ bodyCompensation parameter cutoffScale ≤ 1 ∧
      bodyCompensation parameter cutoffScale * Parameters.safeSize parameter ≤ Parameters.anchorWidth parameter := by
  have ha : 0 < v7Activation cutoffScale parameter := activation_positive _ _ _ _ (legFeatureCount_positive cutoffScale parameter hscale hp)
  have ha1 : v7Activation cutoffScale parameter ≤ 1 := (activation_le_one_hundredth _ _ _ _).trans (by norm_num)
  have hN : (0 : ℝ) < Parameters.bodies parameter := by exact_mod_cast Parameters.bodies_positive parameter
  have hqDim : Parameters.modulus parameter ≤ Parameters.dimension parameter := by
    have hden : 1 ≤ Parameters.meanDensity parameter := by
      unfold Parameters.meanDensity
      exact Nat.one_le_pow _ _ (by have := Parameters.security_ge_two parameter; omega)
    simpa only [Parameters.dimension, mul_one] using Nat.mul_le_mul_left (Parameters.modulus parameter) hden
  have hqN : Parameters.modulus parameter ≤ 2 * Parameters.bodies parameter := by
    have hi := Parameters.population_identity parameter
    have hm := Parameters.legs_le_half_bodies parameter
    omega
  have hmA : 2 * Parameters.legs parameter ≤ Parameters.anchorWidth parameter := by
    have hh : 2 ≤ Parameters.security parameter ^ 2 := by have hh := Nat.pow_le_pow_left (Parameters.security_ge_two parameter) 2; omega
    have hh' := Nat.mul_le_mul_right (Parameters.security parameter ^ 30) hh
    simpa only [Parameters.legs, Parameters.anchorWidth, ← pow_add] using hh'
  have hWq : Parameters.safeSize parameter ≤ Parameters.modulus parameter := by unfold Parameters.safeSize; omega
  have hmul : (Parameters.legs parameter : ℝ) * Parameters.safeSize parameter ≤
      Parameters.bodies parameter * (Parameters.anchorWidth parameter : ℝ) := by
    have hh1 := Nat.mul_le_mul_left (Parameters.legs parameter) (hWq.trans hqN)
    have hh2 := Nat.mul_le_mul_left (Parameters.bodies parameter) hmA
    have hh : Parameters.legs parameter * Parameters.safeSize parameter ≤ Parameters.bodies parameter * Parameters.anchorWidth parameter := by nlinarith
    exact_mod_cast hh
  have hdelta : 0 ≤ bodyCompensation parameter cutoffScale := by unfold bodyCompensation; positivity
  refine ⟨hdelta, ?_, ?_⟩
  · have hh := mul_le_mul (legs_fraction_small parameter) ha1 ha.le (by norm_num : (0 : ℝ) ≤ 1 / 772)
    have heq : bodyCompensation parameter cutoffScale = ((Parameters.legs parameter : ℝ) / Parameters.bodies parameter) * v7Activation cutoffScale parameter := by unfold bodyCompensation; ring
    rw [heq]
    linarith
  · change ((Parameters.legs parameter : ℝ) * v7Activation cutoffScale parameter / Parameters.bodies parameter) * Parameters.safeSize parameter ≤ _
    calc
      _ = ((Parameters.legs parameter : ℝ) * Parameters.safeSize parameter * v7Activation cutoffScale parameter) / Parameters.bodies parameter := by ring
      _ ≤ ((Parameters.legs parameter : ℝ) * Parameters.safeSize parameter) / Parameters.bodies parameter := by
        apply div_le_div_of_nonneg_right _ hN.le
        simpa only [mul_one] using mul_le_mul_of_nonneg_left ha1 (by positivity : 0 ≤ (Parameters.legs parameter : ℝ) * Parameters.safeSize parameter)
      _ ≤ ((Parameters.bodies parameter : ℝ) * Parameters.anchorWidth parameter) / Parameters.bodies parameter := div_le_div_of_nonneg_right hmul hN.le
      _ = _ := by field_simp

theorem actualBodyCenter_translation_short_bound (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (hscale : 1 ≤ cutoffScale) (hp : 1 ≤ parameter)
    (hn : ∀ color, 0 ≤ actualPrimary cutoffScale parameter beta color)
    (hm : ∑ color, actualPrimary cutoffScale parameter beta color = 1) (shift : ℤ) :
    (∑ output, |integerShiftProfile parameter (actualBodyCenter cutoffScale parameter beta) shift output -
      actualBodyCenter cutoffScale parameter beta output|) ≤
      12 * (shift.natAbs : ℝ) / Parameters.modulus parameter := by
  have hd := bodyCompensation_anchor_bound cutoffScale parameter hscale hp
  have hW : (0 : ℝ) < Parameters.safeSize parameter := by exact_mod_cast Parameters.safeSize_positive parameter
  have hA : (0 : ℝ) < Parameters.anchorWidth parameter := by
    simp only [Parameters.anchorWidth, Nat.cast_pow]
    have hh : (0 : ℝ) < Parameters.security parameter := by exact_mod_cast (show 0 < Parameters.security parameter by have := Parameters.security_ge_two parameter; omega)
    positivity
  have hq : (0 : ℝ) < Parameters.modulus parameter := by exact_mod_cast (Parameters.modulus_prime parameter).pos
  have hratio : bodyCompensation parameter cutoffScale / Parameters.anchorWidth parameter ≤ 1 / (Parameters.safeSize parameter : ℝ) :=
    (div_le_div_iff₀ hA hW).mpr (by simpa only [one_mul] using hd.2.2)
  have hWq : (Parameters.modulus parameter : ℝ) / 2 ≤ Parameters.safeSize parameter := by
    have hm := safeMargin_quarter parameter
    have hs := Parameters.safeSize_positive parameter
    have hnat : Parameters.modulus parameter ≤ 2 * Parameters.safeSize parameter := by unfold Parameters.safeSize at *; omega
    have hh : (Parameters.modulus parameter : ℝ) ≤ 2 * Parameters.safeSize parameter := by exact_mod_cast hnat
    linarith
  have hinv : 1 / (Parameters.safeSize parameter : ℝ) ≤ 2 / (Parameters.modulus parameter : ℝ) := by
    exact (div_le_div_iff₀ hW hq).mpr (by linarith)
  have hh := actualBodyCenter_translation_l1 cutoffScale parameter beta hn hm hd.1 shift
  have hterm1 := mul_le_mul_of_nonneg_left hd.2.1 (by positivity : 0 ≤ 2 * (shift.natAbs : ℝ) / Parameters.safeSize parameter)
  have hterm2 := mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ 2 * (shift.natAbs : ℝ))
  have hlast := mul_le_mul_of_nonneg_left hinv (by positivity : 0 ≤ 6 * (shift.natAbs : ℝ))
  simp only [div_eq_mul_inv] at hh hterm1 hterm2 hlast ⊢
  nlinarith

/-- The exact actual calibration dominates the root-only deficit. -/
theorem actual_root_deficit_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ color,
      1 / (Parameters.safeSize parameter : ℝ) - actualRootBodyMean parameter color ≤
        4 * bodyCompensation parameter cutoffScale * actualPrimary cutoffScale parameter (beta parameter) color := by
  have hmodel := ((actual_physical_supports_eventually cutoffScale hscale).and hbeta).mono
    (fun parameter h => And.intro h.1.1 (And.intro h.1.2 h.2))
  filter_upwards [body_deficit_eventually cutoffScale hscale beta (boundaryHalf cutoffScale)
    (bodyShift cutoffScale) (bodyBlur cutoffScale) (startsPlus cutoffScale) (startsMinus cutoffScale)
    (pairSourceShift cutoffScale) (pairSourceLaw cutoffScale) hmodel] with parameter hd color
  have hsafe := Parameters.safeSize_positive parameter
  have hwidth : 2 * Parameters.safeMargin parameter < Parameters.modulus parameter := by unfold Parameters.safeSize at hsafe; omega
  have hcast : (Parameters.safeSize parameter : ℝ) = (Parameters.modulus parameter : ℝ) - 2 * Parameters.safeMargin parameter := by
    unfold Parameters.safeSize
    rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat]
  have hh := root_bodyMean_deficit_le_twice cutoffScale parameter color.val hwidth
  rw [hcast]
  change (1 / ((Parameters.modulus parameter : ℝ) - 2 * Parameters.safeMargin parameter) -
    actualRootBodyMean parameter color) ≤ _ at hh
  have hd' : 1 / ((Parameters.modulus parameter : ℝ) - 2 * Parameters.safeMargin parameter) -
      actualBodyMean cutoffScale parameter color ≤
      2 * bodyCompensation parameter cutoffScale * actualPrimary cutoffScale parameter (beta parameter) color := hd color
  change _ ≤ 2 * (1 / ((Parameters.modulus parameter : ℝ) - 2 * Parameters.safeMargin parameter) - actualBodyMean cutoffScale parameter color) at hh
  linarith

/-- All body shifts use the actual calibrated profile and actual root law.
The squared fringe norm retains both the compensation and edge-mass gains. -/
theorem actual_body_fringe_bounds_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ shift : ℤ,
      let P := actualBodyCenter cutoffScale parameter (beta parameter)
      let outside := bodyOutside parameter P shift
      bodyOutsideMass parameter P shift ≤ 12 * (shift.natAbs : ℝ) / Parameters.modulus parameter ∧
      profileSquareNorm P (bodyInside parameter P shift) ≤ 96 * (shift.natAbs : ℝ) / Parameters.modulus parameter ∧
      (∀ color, |bodyInside parameter P shift color| ≤ 4 * P color) ∧
      (∀ color, 0 ≤ rootProfileOperator parameter outside color ∧ rootProfileOperator parameter outside color ≤
        8 * bodyCompensation parameter cutoffScale * actualPrimary cutoffScale parameter (beta parameter) color) ∧
      profileSquareNorm (actualPrimary cutoffScale parameter (beta parameter)) (rootProfileOperator parameter outside) ≤
        96 * bodyCompensation parameter cutoffScale * (shift.natAbs : ℝ) / Parameters.modulus parameter := by
  filter_upwards [actual_body_center_probability_eventually cutoffScale hscale beta hbeta,
    actual_primary_probability_eventually cutoffScale hscale beta hbeta,
    actual_root_deficit_eventually cutoffScale hscale beta hbeta, eventually_ge_atTop 1]
    with parameter hb hp hdef hlarge shift
  dsimp only
  let P := actualBodyCenter cutoffScale parameter (beta parameter)
  let outside := bodyOutside parameter P shift
  have hP (color) : 0 ≤ P color := (div_nonneg ((actualCoreLaw parameter).nonneg color) (by norm_num)).trans (hb.2.1 color).1
  have ho (color) : 0 ≤ outside color := bodyOutside_nonneg parameter P hP shift color
  have hdelta := (bodyCompensation_anchor_bound cutoffScale parameter hscale hlarge).1
  have hvar := actualBodyCenter_translation_short_bound cutoffScale parameter (beta parameter) hscale hlarge (fun color => (hp.1 color).le) hp.2 shift
  have hmass := (bodyOutsideMass_le_variation parameter P hP hb.2.2 shift).trans hvar
  have hpoint (color) : rootProfileOperator parameter outside color ≤
      8 * bodyCompensation parameter cutoffScale * actualPrimary cutoffScale parameter (beta parameter) color := by
    have hh := bodyOutside_root_deficit parameter P (fun color => (hb.2.1 color).2) shift color
    have hd := hdef color
    change rootProfileOperator parameter outside color ≤ _ at hh
    linarith
  refine ⟨hmass, ?_, bodyInside_relative parameter P hb.1 hb.2.1 shift,
    fun color => ⟨rootProfileOperator_nonneg parameter outside ho color, hpoint color⟩, ?_⟩
  · exact (bodyInside_square_le_variation parameter P hb.1 hb.2.1 shift).trans
      ((mul_le_mul_of_nonneg_left hvar (by norm_num : (0 : ℝ) ≤ 8)).trans_eq (by ring))
  · have hh := profileSquareNorm_le_relative_mul_l1 (actualPrimary cutoffScale parameter (beta parameter))
        (rootProfileOperator parameter outside) (8 * bodyCompensation parameter cutoffScale) hp.1 (by
          intro color
          rw [abs_of_nonneg (rootProfileOperator_nonneg parameter outside ho color)]
          exact hpoint color)
    have hmass' := (rootProfileOperator_mass_le parameter outside ho).trans hmass
    simp_rw [abs_of_nonneg (rootProfileOperator_nonneg parameter outside ho _)] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left hmass' (by positivity)).trans_eq (by ring))

end
end AFT.V7Calibration
