import AFT.BodyTypeParameters
import AFT.V7ReferenceLower

/-! # Actual shifted body/reference energies for the full histogram tail -/

namespace AFT.V7Calibration

open Filter GaussianSource
open scoped BigOperators Classical Topology

noncomputable section

theorem actual_body_core_counting_square (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (hp : ∀ color, 0 ≤ actualPrimary cutoffScale parameter beta color)
    (hpm : ∑ color, actualPrimary cutoffScale parameter beta color = 1) :
    (∑ color, (actualBodyCenter cutoffScale parameter beta color - (actualCoreLaw parameter).weight color)^2) ≤
      bodyCompensation parameter cutoffScale ^ 2 *
        (4 / (Parameters.modulus parameter : ℝ) + 2 / Parameters.anchorWidth parameter) := by
  let p := actualPrimary cutoffScale parameter beta
  let P := actualBodyCenter cutoffScale parameter beta
  let core := (actualCoreLaw parameter).weight
  let anchor : Fin (Parameters.modulus parameter) → ℝ := fun color =>
    anchorMean (Parameters.modulus parameter) (Parameters.anchorWidth parameter) p color.val
  let delta := bodyCompensation parameter cutoffScale
  have hq : (0 : ℝ) < Parameters.modulus parameter := by exact_mod_cast (Parameters.modulus_prime parameter).pos
  have hanchor0 (color) : 0 ≤ anchor color := Finset.sum_nonneg fun input _ =>
    mul_nonneg (hp input) (publicAnchorKernel_nonneg _ _ _ _)
  have hanchor1 : ∑ color, anchor color = 1 := by
    dsimp only [anchor, anchorMean]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, (actual_anchor_safe_mass parameter _).1, mul_one]
    exact hpm
  have hanchorUpper (color) : anchor color ≤ 1 / (Parameters.anchorWidth parameter : ℝ) := by
    calc
      _ ≤ ∑ input, p input * (1 / (Parameters.anchorWidth parameter : ℝ)) := by
        apply Finset.sum_le_sum
        intro input _
        simpa only [one_div] using mul_le_mul_of_nonneg_left (publicAnchorKernel_le (Parameters.modulus parameter) (Parameters.anchorWidth parameter) input color.val) (hp input)
      _ = _ := by rw [← Finset.sum_mul, hpm, one_mul]
  have hcount := probability_difference_counting_sq core anchor
    (2 / (Parameters.modulus parameter : ℝ)) (1 / (Parameters.anchorWidth parameter : ℝ))
    (actualCoreLaw parameter).nonneg hanchor0 (actualCoreLaw parameter).sum_one hanchor1
    (actualCoreLaw_bounds parameter).1 hanchorUpper
  have heq (color) : P color - core color = delta * (core color - anchor color) := by
    dsimp only [P, core, delta, anchor, p, actualBodyCenter, calibratedBodyProfile,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  change (∑ color, (P color - core color)^2) ≤ _
  simp_rw [heq, mul_pow]
  rw [← Finset.mul_sum]
  exact (mul_le_mul_of_nonneg_left hcount (sq_nonneg delta)).trans_eq (by dsimp only [delta]; ring)


theorem actual_core_uniform_l1 (parameter : ℕ) :
    (∑ color, |(actualCoreLaw parameter).weight color - 1 / (Parameters.modulus parameter : ℝ)|) ≤
      4 * (Parameters.safeMargin parameter : ℝ) / Parameters.modulus parameter := by
  have hq : (0 : ℝ) < Parameters.modulus parameter := by exact_mod_cast (Parameters.modulus_prime parameter).pos
  have hW : (0 : ℝ) < Parameters.safeSize parameter := by exact_mod_cast Parameters.safeSize_positive parameter
  have hWq : (Parameters.safeSize parameter : ℝ) ≤ Parameters.modulus parameter := by
    exact_mod_cast (show Parameters.safeSize parameter ≤ Parameters.modulus parameter by unfold Parameters.safeSize; omega)
  have hinv := one_div_le_one_div_of_le hW hWq
  have hh := probability_uniform_l1_le (actualCoreLaw parameter).weight (1 / (Parameters.safeSize parameter : ℝ))
    (by simpa only [Fintype.card_fin] using hq) (actualCoreLaw parameter).sum_one (actualCoreLaw parameter).nonneg
    (actualCoreLaw_upper parameter) (by simpa only [Fintype.card_fin, one_div] using hinv)
  simp only [Fintype.card_fin] at hh
  have hwidth : (Parameters.safeSize parameter : ℝ) = (Parameters.modulus parameter : ℝ) - 2 * Parameters.safeMargin parameter := by
    have hs := Parameters.safeSize_positive parameter
    unfold Parameters.safeSize at hs ⊢
    rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat]
  simp only [one_div] at hh ⊢
  apply hh.trans_eq
  rw [inv_div_inv, hwidth]
  field_simp
  ring

theorem body_compensation_energy_power (cutoffScale : ℝ) (parameter : ℕ) (hscale : 1 ≤ cutoffScale) (hp : 2 ≤ parameter) :
    bodyCompensation parameter cutoffScale ^ 2 *
      (8 + 4 * (Parameters.modulus parameter : ℝ) / Parameters.anchorWidth parameter) ≤ 64 / (parameter : ℝ)^38 := by
  have hp1 : (1 : ℝ) ≤ parameter := by exact_mod_cast (show 1 ≤ parameter by omega)
  have hp0 : (0 : ℝ) < parameter := by positivity
  have hd0 := (bodyCompensation_anchor_bound cutoffScale parameter hscale (by omega)).1
  have hd := bodyCompensation_coarse cutoffScale parameter hscale hp
  have hA : (Parameters.anchorWidth parameter : ℝ) = (parameter : ℝ)^32 := by simp only [Parameters.anchorWidth, Parameters.security_eq parameter hp, Nat.cast_pow]
  have hq : (Parameters.modulus parameter : ℝ) ≤ 2 * (parameter : ℝ)^40 := by
    exact_mod_cast (show Parameters.modulus parameter ≤ 2 * parameter^40 by simpa only [Parameters.security_eq parameter hp] using (Parameters.modulus_bounds parameter).2)
  have hqA : (Parameters.modulus parameter : ℝ) / Parameters.anchorWidth parameter ≤ 2 * (parameter : ℝ)^8 := by
    rw [hA]
    calc
      _ ≤ (2 * (parameter : ℝ)^40) / (parameter : ℝ)^32 := div_le_div_of_nonneg_right hq (by positivity)
      _ = _ := by field_simp
  have hpow8 : 1 ≤ (parameter : ℝ)^8 := one_le_pow₀ hp1
  have hdSq := (sq_le_sq₀ hd0 (by positivity)).mpr hd
  have hfactor : 8 + 4 * (Parameters.modulus parameter : ℝ) / Parameters.anchorWidth parameter ≤ 16 * (parameter : ℝ)^8 := by
    simp only [div_eq_mul_inv] at hqA ⊢
    nlinarith
  have hh := mul_le_mul hdSq hfactor
    (by positivity : 0 ≤ 8 + 4 * (Parameters.modulus parameter : ℝ) / Parameters.anchorWidth parameter) (by positivity)
  have heq : (2 / (parameter : ℝ)^30)^2 * (16 * (parameter : ℝ)^8) = 64 / (parameter : ℝ)^52 := by field_simp; ring
  rw [heq] at hh
  exact hh.trans (div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_right₀ hp1 (by omega : 38 ≤ 52)))

theorem profileSquareNorm_three_le {Color : Type*} [Fintype Color] (reference first second third : Color → ℝ)
    (hr : ∀ color, 0 ≤ reference color) :
    profileSquareNorm reference (first + second + third) ≤
      3 * (profileSquareNorm reference first + profileSquareNorm reference second + profileSquareNorm reference third) := by
  unfold profileSquareNorm
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro color _
  change (first color + second color + third color)^2 / reference color ≤ _
  have hh : (first color + second color + third color)^2 ≤
      3 * (first color^2 + second color^2 + third color^2) := by
    nlinarith [sq_nonneg (first color - second color), sq_nonneg (first color - third color), sq_nonneg (second color - third color)]
  exact (div_le_div_of_nonneg_right hh (hr color)).trans_eq (by ring)

/-- Every physical shifted body singleton is measured against the actual
histogram reference. The energy has the original `lambda^-38` exponent. -/
theorem actual_shifted_body_reference_energy_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ shift : ℤ, |shift| ≤ maxBodyShift cutoffScale parameter →
      profileSquareNorm (actualReferenceMean cutoffScale parameter (beta parameter))
        (integerShiftProfile parameter (actualBodyCenter cutoffScale parameter (beta parameter)) shift -
          actualReferenceMean cutoffScale parameter (beta parameter)) ≤ 5472 / (parameter : ℝ)^38 := by
  filter_upwards [actual_body_center_probability_eventually cutoffScale hscale beta hbeta,
    actual_primary_probability_eventually cutoffScale hscale beta hbeta,
    actual_reference_probability_eventually cutoffScale hscale beta hbeta,
    actual_reference_lower_eventually cutoffScale hscale beta hbeta,
    actual_primary_uniform_l1_eventually cutoffScale hscale beta hbeta,
    legCutoff_le_square_eventually cutoffScale hscale, eventually_ge_atTop 2]
    with parameter hb hp hr hlower hL1 hcut hlarge shift hshift
  let P := actualBodyCenter cutoffScale parameter (beta parameter)
  let core := (actualCoreLaw parameter).weight
  let r := actualReferenceMean cutoffScale parameter (beta parameter)
  let shifted := integerShiftProfile parameter P shift
  have hparam : (0 : ℝ) < parameter := by exact_mod_cast (show 0 < parameter by omega)
  have hq : (0 : ℝ) < Parameters.modulus parameter := by exact_mod_cast (Parameters.modulus_prime parameter).pos
  have hr0 (color) : 0 < r color := lt_of_lt_of_le (by positivity) (hlower color)
  have hP0 (color) : 0 ≤ P color := (div_nonneg ((actualCoreLaw parameter).nonneg color) (by norm_num)).trans (hb.2.1 color).1
  have hPupper (color) : P color ≤ 4 / (Parameters.modulus parameter : ℝ) := by
    have hh := (actualCoreLaw_bounds parameter).1 color
    have h := (hb.2.1 color).2
    dsimp only [P]
    simp only [div_eq_mul_inv] at hh ⊢
    linarith
  have hsh0 (color) : 0 ≤ shifted color := integerShiftProfile_nonneg parameter P hP0 shift color
  have hshU (color) : shifted color ≤ 4 / (Parameters.modulus parameter : ℝ) :=
    integerShiftProfile_bound parameter P _ (by positivity) hPupper shift color
  have hshiftFraction := (body_shift_fraction cutoffScale parameter hlarge hcut shift hshift).1
  have htranslated : profileSquareNorm r (shifted - P) ≤ 480 / (parameter : ℝ)^38 := by
    have hdensity (color) : |(shifted - P) color| ≤ 8 * r color := by
      have hh : 4 / (Parameters.modulus parameter : ℝ) ≤ 8 * r color := by
        have hh := mul_le_mul_of_nonneg_left (hlower color) (by norm_num : (0 : ℝ) ≤ 8)
        convert hh using 1; ring
      exact abs_le.mpr ⟨by dsimp only [Pi.sub_apply]; linarith [hP0 color, hsh0 color, hPupper color, hshU color],
        by dsimp only [Pi.sub_apply]; linarith [hP0 color, hsh0 color, hPupper color, hshU color]⟩
    have hn := profileSquareNorm_le_relative_mul_l1 r (shifted - P) 8 hr0 hdensity
    have hv := actualBodyCenter_translation_short_bound cutoffScale parameter (beta parameter) hscale (by omega)
      (fun color => (hp.1 color).le) hp.2 shift
    have hfrac := mul_le_mul_of_nonneg_left hshiftFraction (by norm_num : (0 : ℝ) ≤ 96)
    change (∑ color, |(shifted - P) color|) ≤ _ at hv
    have hh := mul_le_mul_of_nonneg_left hv (by norm_num : (0 : ℝ) ≤ 8)
    simp only [div_eq_mul_inv] at hh hfrac ⊢
    linarith
  have hcomp : profileSquareNorm r (P - core) ≤ 64 / (parameter : ℝ)^38 := by
    have hh := profileSquareNorm_le_counting r (P - core) Finset.univ
      (1 / (2 * (Parameters.modulus parameter : ℝ))) (by positivity)
      (fun color _ => hlower color) (by intro color hc; exact False.elim (hc (Finset.mem_univ color)))
    have hc := actual_body_core_counting_square cutoffScale parameter (beta parameter) (fun color => (hp.1 color).le) hp.2
    have hc' := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ (1 / (2 * (Parameters.modulus parameter : ℝ)))⁻¹)
    have heq : (1 / (2 * (Parameters.modulus parameter : ℝ)))⁻¹ *
        (bodyCompensation parameter cutoffScale ^ 2 * (4 / (Parameters.modulus parameter : ℝ) + 2 / Parameters.anchorWidth parameter)) =
        bodyCompensation parameter cutoffScale ^ 2 * (8 + 4 * (Parameters.modulus parameter : ℝ) / Parameters.anchorWidth parameter) := by
      field_simp
      ring
    rw [heq] at hc'
    exact (hh.trans hc').trans (body_compensation_energy_power cutoffScale parameter hscale hlarge)
  have hcoreL1 : (∑ color, |core color - 1 / (Parameters.modulus parameter : ℝ)|) ≤ 80 / (parameter : ℝ)^38 := by
    have hh := actual_core_uniform_l1 parameter
    have hqpow : (parameter : ℝ)^40 ≤ Parameters.modulus parameter := by
      exact_mod_cast (show parameter^40 ≤ Parameters.modulus parameter by simpa only [Parameters.security_eq parameter hlarge] using (Parameters.modulus_bounds parameter).1)
    have hm : (Parameters.safeMargin parameter : ℝ) = 20 * (parameter : ℝ)^2 := by
      simp only [Parameters.safeMargin, Parameters.security_eq parameter hlarge, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
    apply hh.trans
    rw [hm]
    calc
      _ ≤ (4 * (20 * (parameter : ℝ)^2)) / (parameter : ℝ)^40 := div_le_div_of_nonneg_left (by positivity) (by positivity) hqpow
      _ = _ := by
        field_simp
        norm_num
  have hcoreRefL1 : (∑ color, |core color - r color|) ≤ 160 / (parameter : ℝ)^38 := by
    calc
      _ ≤ ∑ color, (|core color - 1 / (Parameters.modulus parameter : ℝ)| + |r color - 1 / (Parameters.modulus parameter : ℝ)|) := by
        apply Finset.sum_le_sum
        intro color _
        simpa only [abs_sub_comm (1 / (Parameters.modulus parameter : ℝ)) (r color)] using
          abs_sub_le (core color) (1 / (Parameters.modulus parameter : ℝ)) (r color)
      _ ≤ _ := by
        rw [Finset.sum_add_distrib]
        have hh := hL1.2
        change (∑ color, |r color - _|) ≤ _ at hh
        simp only [div_eq_mul_inv] at hcoreL1 hh ⊢
        linarith
  have hcoreRef : profileSquareNorm r (core - r) ≤ 1280 / (parameter : ℝ)^38 := by
    have hdensity (color) : |(core - r) color| ≤ 8 * r color := by
      have hu := (actualCoreLaw_bounds parameter).1 color
      have hrU := (hr.1 color).2
      have hcn := (actualCoreLaw parameter).nonneg color
      have hrn := (hr.1 color).1
      have hh : 4 / (Parameters.modulus parameter : ℝ) ≤ 8 * r color := by
        have hh := mul_le_mul_of_nonneg_left (hlower color) (by norm_num : (0 : ℝ) ≤ 8)
        convert hh using 1; ring
      change |core color - r color| ≤ _
      have ha := abs_sub (core color) (r color)
      rw [abs_of_nonneg hcn, abs_of_nonneg hrn] at ha
      dsimp only [core, r] at *
      simp only [div_eq_mul_inv] at hu hrU hh
      linarith
    have hh := profileSquareNorm_le_relative_mul_l1 r (core - r) 8 hr0 hdensity
    exact hh.trans ((mul_le_mul_of_nonneg_left hcoreRefL1 (by norm_num : (0 : ℝ) ≤ 8)).trans_eq (by ring))
  have hid : shifted - r = (shifted - P) + (P - core) + (core - r) := by funext color; simp only [Pi.sub_apply, Pi.add_apply]; ring
  change profileSquareNorm r (shifted - r) ≤ _
  rw [hid]
  have hh := profileSquareNorm_three_le r (shifted - P) (P - core) (core - r) (fun color => (hr0 color).le)
  simp only [div_eq_mul_inv] at htranslated hcomp hcoreRef ⊢
  linarith

end
end AFT.V7Calibration
