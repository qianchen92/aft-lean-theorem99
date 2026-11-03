import AFT.V7ReferenceLower

/-! # The actual calibrated primary's pointwise height -/

namespace AFT

open Filter
open scoped BigOperators Classical Topology

noncomputable section

theorem boundary_perturbation_point_bound {Color : Type*} [Fintype Color] [DecidableEq Color]
    (boundary : Finset Color) (change bound : ℝ) (hbound : 0 ≤ bound)
    (hcard : boundary.card ≤ boundaryᶜ.card) (hchange : |change| ≤ bound * boundary.card)
    (color : Color) :
    |change * (uniformFiniteProfile boundary color - uniformFiniteProfile boundaryᶜ color)| ≤ bound := by
  classical
  by_cases hc : color ∈ boundary
  · have hb : (0 : ℝ) < boundary.card := by exact_mod_cast Finset.card_pos.mpr ⟨color, hc⟩
    simp only [uniformFiniteProfile, hc, Finset.mem_compl, not_true_eq_false, if_true,
      if_false, sub_zero, abs_mul, abs_of_nonneg (inv_nonneg.mpr hb.le)]
    exact (mul_le_mul_of_nonneg_right hchange (inv_nonneg.mpr hb.le)).trans_eq
      (by field_simp)
  · have hi : (0 : ℝ) < boundaryᶜ.card := by
      exact_mod_cast Finset.card_pos.mpr ⟨color, Finset.mem_compl.mpr hc⟩
    simp only [uniformFiniteProfile, hc, Finset.mem_compl, not_false_eq_true, if_false,
      if_true, zero_sub, abs_mul, abs_neg, abs_of_nonneg (inv_nonneg.mpr hi.le)]
    apply (mul_le_mul_of_nonneg_right hchange (inv_nonneg.mpr hi.le)).trans
    calc
      _ ≤ (bound * (boundaryᶜ.card : ℝ)) * (boundaryᶜ.card : ℝ)⁻¹ := by
        gcongr
      _ = _ := by field_simp

namespace V7Calibration
open GaussianSource TrimmedSlice

theorem actual_base_primary_upper_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) :
    ∀ᶠ parameter : ℕ in atTop, ∀ color,
      actualBasePrimary cutoffScale parameter color ≤
        2 * Parameters.dimension parameter /
          (Parameters.legs parameter * v7Activation cutoffScale parameter * Parameters.modulus parameter) := by
  have hphysical := (actual_physical_supports_eventually cutoffScale hscale).mono fun _ h => h.1
  filter_upwards [hphysical,
    v7_primaryCalibration_clearance_eventually cutoffScale hscale (boundaryHalf cutoffScale)
      (hphysical.mono fun _ h => h.1), eventually_ge_atTop 2]
    with parameter hphysical hclear hp
  have hq : (0 : ℝ) < Parameters.modulus parameter := by exact_mod_cast (Parameters.modulus_prime parameter).pos
  have hm : (0 : ℝ) < Parameters.legs parameter := by
    simp only [Parameters.legs, Parameters.security_eq parameter hp, Nat.cast_pow]; positivity
  have ha : 0 < v7Activation cutoffScale parameter := activation_positive _ _ _ _
    (legFeatureCount_positive cutoffScale parameter hscale (by omega))
  have ha1 : v7Activation cutoffScale parameter ≤ 1 := activation_le_one _ _ _ _
  have hw : Parameters.anchorWidth parameter ≠ 0 := by
    unfold Parameters.anchorWidth
    exact pow_ne_zero _ (by have := Parameters.security_ge_two parameter; omega)
  have hslice : 2 * boundaryHalf cutoffScale parameter + 3 * (Parameters.anchorWidth parameter : ℤ) < Parameters.modulus parameter := by
    have hh := hclear.2
    have hcut : (0 : ℤ) ≤ legCutoff cutoffScale parameter := by positivity
    have hqi : (0 : ℤ) < Parameters.modulus parameter := by exact_mod_cast (Parameters.modulus_prime parameter).pos
    omega
  have hdenom : (Parameters.modulus parameter : ℝ) / 2 ≤
      Parameters.modulus parameter - 2 * boundaryHalf cutoffScale parameter - 3 * Parameters.anchorWidth parameter := by
    have hh : (2 : ℝ) * (3 * Parameters.anchorWidth parameter + 2 * boundaryHalf cutoffScale parameter + legCutoff cutoffScale parameter) ≤ Parameters.modulus parameter := by exact_mod_cast hclear.2
    linarith [show (0 : ℝ) ≤ legCutoff cutoffScale parameter by positivity]
  intro color
  have hu (starts : pairSample cutoffScale parameter → ℤ)
      (hs : ∀ index shift, shift ∈ anchorInterval (starts index) (Parameters.anchorWidth parameter) →
        |shift| ≤ 3 * (Parameters.anchorWidth parameter : ℤ)) :
      mixedLaw (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter) starts (fun _ => 0)
        (pairSourceLaw cutoffScale parameter).weight (Parameters.anchorWidth parameter) color.val ≤
        2 / (Parameters.modulus parameter : ℝ) := by
    have hh := mixedLaw_zero_le (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter)
      (3 * Parameters.anchorWidth parameter) starts (pairSourceLaw cutoffScale parameter).weight
      (Parameters.anchorWidth parameter) hw (pairSourceLaw cutoffScale parameter).nonneg
      (pairSourceLaw cutoffScale parameter).sum_one hs hslice color.val
    simp only [Int.cast_natCast, Int.cast_mul, Int.cast_ofNat] at hh
    apply hh.trans
    calc
      _ ≤ 1 / ((Parameters.modulus parameter : ℝ) / 2) :=
        one_div_le_one_div_of_le (by positivity) hdenom
      _ = _ := by ring
  have hup := hu _ hphysical.2.1
  have hum := hu _ hphysical.2.2.1
  have hshiftPlus := mixedLaw_nonneg (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter)
    (startsPlus cutoffScale parameter) (pairSourceShift cutoffScale parameter)
    (pairSourceLaw cutoffScale parameter).weight (Parameters.anchorWidth parameter) color.val
    (pairSourceLaw cutoffScale parameter).nonneg
  have hshiftMinus := mixedLaw_nonneg (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter)
    (startsMinus cutoffScale parameter) (pairSourceShift cutoffScale parameter)
    (pairSourceLaw cutoffScale parameter).weight (Parameters.anchorWidth parameter) color.val
    (pairSourceLaw cutoffScale parameter).nonneg
  have hbody : 0 ≤ blurredSafeLaw (Parameters.modulus parameter) (Parameters.safeMargin parameter)
      (bodyShift cutoffScale parameter) (bodyBlur cutoffScale parameter).weight color.val :=
    Finset.sum_nonneg fun index _ => mul_nonneg ((bodyBlur cutoffScale parameter).nonneg index)
      (intervalAnchorLaw_nonneg _ _ _)
  have hpop : (Parameters.bodies parameter : ℝ) + 2 * Parameters.legs parameter = Parameters.dimension parameter :=
    by exact_mod_cast Parameters.population_identity parameter
  have hfour : (4 : ℝ) * Parameters.legs parameter ≤ Parameters.dimension parameter :=
    by exact_mod_cast Parameters.four_legs_le_dimension parameter
  unfold actualBasePrimary basePrimary actualFairBasePrimary basePrimaryProfile
  simp only [fairMixedLaw, Int.cast_natCast, hpop]
  apply (div_le_iff₀ (mul_pos hm ha)).mpr
  have heq : (2 * Parameters.dimension parameter /
      (Parameters.legs parameter * v7Activation cutoffScale parameter * Parameters.modulus parameter)) *
      (Parameters.legs parameter * v7Activation cutoffScale parameter) =
      2 * Parameters.dimension parameter / Parameters.modulus parameter := by field_simp
  rw [heq]
  have ht := mul_le_mul_of_nonneg_left (show
    (mixedLaw (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter) (startsPlus cutoffScale parameter) (fun _ => 0) (pairSourceLaw cutoffScale parameter).weight (Parameters.anchorWidth parameter) color.val +
      mixedLaw (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter) (startsMinus cutoffScale parameter) (fun _ => 0) (pairSourceLaw cutoffScale parameter).weight (Parameters.anchorWidth parameter) color.val) / 2 ≤
      2 / (Parameters.modulus parameter : ℝ) by linarith)
    (show 0 ≤ 2 * Parameters.legs parameter * v7Activation cutoffScale parameter by positivity)
  have hloss := mul_nonneg (show 0 ≤ (Parameters.bodies parameter : ℝ) + Parameters.legs parameter * v7Activation cutoffScale parameter by positivity) hbody
  have hfour' : 4 * Parameters.legs parameter * v7Activation cutoffScale parameter ≤ Parameters.dimension parameter := by
    exact (mul_le_mul_of_nonneg_left ha1 (by positivity)).trans (by simpa using hfour)
  have hlast := div_le_div_of_nonneg_right hfour' hq.le
  have hshiftLoss := mul_nonneg (show (0 : ℝ) ≤ 2 * Parameters.legs parameter by positivity)
    (div_nonneg (add_nonneg hshiftPlus hshiftMinus) (by norm_num : (0 : ℝ) ≤ 2))
  simp only [div_eq_mul_inv] at ht hlast ⊢
  nlinarith only [ht, hloss, hlast, hshiftLoss]

theorem actual_primary_upper_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ color,
      actualPrimary cutoffScale parameter (beta parameter) color ≤
        3 / (v7Activation cutoffScale parameter * (parameter : ℝ) ^ 10) := by
  filter_upwards [hbeta, body_support_scales_eventually cutoffScale hscale,
    actual_base_primary_upper_eventually cutoffScale hscale, eventually_ge_atTop 2]
    with parameter hb hs hbaseup hp
  have hq : (0 : ℝ) < Parameters.modulus parameter := by exact_mod_cast (Parameters.modulus_prime parameter).pos
  have hm : (0 : ℝ) < Parameters.legs parameter := by
    simp only [Parameters.legs, Parameters.security_eq parameter hp, Nat.cast_pow]; positivity
  have hn : (0 : ℝ) < Parameters.dimension parameter := by
    simp only [Parameters.dimension, Parameters.meanDensity, Parameters.security_eq parameter hp, Nat.cast_mul, Nat.cast_pow]; positivity
  have ha : 0 < v7Activation cutoffScale parameter := activation_positive _ _ _ _
    (legFeatureCount_positive cutoffScale parameter hscale (by omega))
  let boundary := boundaryPalette (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter)
  let scale := (Parameters.legs parameter : ℝ) * v7Activation cutoffScale parameter / Parameters.dimension parameter
  let change := repairedBoundaryMass parameter cutoffScale (beta parameter) (boundaryHalf cutoffScale parameter) -
    v7BaseBoundaryMass cutoffScale parameter (boundaryHalf cutoffScale parameter)
  have hsmall : 2 * (boundary.card : ℝ) ≤ Parameters.modulus parameter := by
    have hmargin := safeMargin_quarter parameter
    have hcard := boundaryPalette_card (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter) hs.2.2.1 (by have hh := hs.2.2.2; omega)
    have hcard' : (boundary.card : ℝ) ≤ 2 * Parameters.safeMargin parameter := by
      have hh : (boundary.card : ℝ) = 2 * boundaryHalf cutoffScale parameter := by exact_mod_cast hcard
      rw [hh]
      exact_mod_cast (show 2 * boundaryHalf cutoffScale parameter ≤ 2 * (Parameters.safeMargin parameter : ℤ) by linarith [hs.2.2.2])
    have hh : (4 : ℝ) * Parameters.safeMargin parameter ≤ Parameters.modulus parameter := by exact_mod_cast hmargin
    linarith
  have hmass := beta_boundary_mass_bounds (Parameters.dimension parameter) (Parameters.legs parameter) (v7Activation cutoffScale parameter)
    (boundary.card / (Parameters.modulus parameter : ℝ)) (beta parameter) hn hm ha (by positivity) hb.1 hb.2
  have hbase : (Parameters.dimension parameter : ℝ) * (boundary.card / (Parameters.modulus parameter : ℝ)) /
      (Parameters.legs parameter * v7Activation cutoffScale parameter) =
      v7BaseBoundaryMass cutoffScale parameter (boundaryHalf cutoffScale parameter) := by unfold v7BaseBoundaryMass; dsimp only [boundary]; ring
  rw [hbase] at hmass
  change v7BaseBoundaryMass cutoffScale parameter (boundaryHalf cutoffScale parameter) / 2 ≤
      repairedBoundaryMass parameter cutoffScale (beta parameter) (boundaryHalf cutoffScale parameter) ∧
    repairedBoundaryMass parameter cutoffScale (beta parameter) (boundaryHalf cutoffScale parameter) ≤
      2 * v7BaseBoundaryMass cutoffScale parameter (boundaryHalf cutoffScale parameter) at hmass
  have hchange : |change| ≤ v7BaseBoundaryMass cutoffScale parameter (boundaryHalf cutoffScale parameter) := by
    have hb0 : 0 ≤ v7BaseBoundaryMass cutoffScale parameter (boundaryHalf cutoffScale parameter) := by unfold v7BaseBoundaryMass; positivity
    dsimp only [change]
    exact abs_le.mpr ⟨by linarith [hmass.1], by linarith [hmass.2]⟩
  let bound := (Parameters.dimension parameter : ℝ) /
    (Parameters.legs parameter * v7Activation cutoffScale parameter * Parameters.modulus parameter)
  have hb0 : 0 ≤ bound := by dsimp only [bound]; positivity
  have hchange' : |change| ≤ bound * boundary.card := by
    apply hchange.trans_eq
    dsimp only [bound, boundary, v7BaseBoundaryMass]
    ring
  have hcard : boundary.card ≤ boundaryᶜ.card := by
    have hc : (boundary.card : ℝ) + boundaryᶜ.card = Parameters.modulus parameter := by
      exact_mod_cast (show boundary.card + boundaryᶜ.card = Parameters.modulus parameter by simpa only [Fintype.card_fin] using boundary.card_add_card_compl)
    have hh : (boundary.card : ℝ) ≤ boundaryᶜ.card := by linarith
    exact_mod_cast hh
  have hbound : bound = 1 / (v7Activation cutoffScale parameter * (parameter : ℝ) ^ 10) := by
    dsimp only [bound]
    simp only [Parameters.dimension, Parameters.meanDensity, Parameters.legs,
      Parameters.security_eq parameter hp, Nat.cast_mul, Nat.cast_pow]
    have hx : (0 : ℝ) < parameter := by exact_mod_cast (by omega : 0 < parameter)
    field_simp
  intro color
  have hr := boundary_perturbation_point_bound boundary change bound hb0 hcard hchange' color
  have hbase : actualBasePrimary cutoffScale parameter color ≤ 2 * bound := by
    simpa only [bound, mul_div_assoc] using hbaseup color
  have heq : actualPrimary cutoffScale parameter (beta parameter) color =
      actualBasePrimary cutoffScale parameter color + change *
        (uniformFiniteProfile boundary color - uniformFiniteProfile boundaryᶜ color) := by
    rfl
  rw [heq]
  have hh := le_abs_self (change *
    (uniformFiniteProfile boundary color - uniformFiniteProfile boundaryᶜ color))
  have hthree : 3 * bound = 3 / (v7Activation cutoffScale parameter * (parameter : ℝ) ^ 10) := by
    rw [hbound]; ring
  calc
    _ ≤ 2 * bound + bound := add_le_add hbase (hh.trans hr)
    _ = _ := by linarith only [hthree]

theorem actual_primary_height_power_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ color,
      actualPrimary cutoffScale parameter (beta parameter) color ≤
        (3 * activationConstant cutoffScale) / (parameter : ℝ) ^ (23 / 4 : ℝ) := by
  filter_upwards [actual_primary_upper_eventually cutoffScale hscale beta hbeta, eventually_ge_atTop 2]
    with parameter h hp color
  have hx : (0 : ℝ) < parameter := by exact_mod_cast (by omega : 0 < parameter)
  have heq : (parameter : ℝ) ^ (17 / 4 : ℝ) * (parameter : ℝ) ^ (23 / 4 : ℝ) =
      (parameter : ℝ) ^ 10 := by
    rw [← Real.rpow_add hx]; norm_num
    exact Real.rpow_natCast _ 10
  have hi := v7Activation_inverse_upper cutoffScale parameter hscale (by omega)
  apply (h color).trans
  calc
    _ = (3 / (parameter : ℝ) ^ 10) * (v7Activation cutoffScale parameter)⁻¹ := by ring
    _ ≤ (3 / (parameter : ℝ) ^ 10) * (activationConstant cutoffScale * (parameter : ℝ) ^ (17 / 4 : ℝ)) := by gcongr
    _ = _ := by rw [← heq]; field_simp

end V7Calibration
end
end AFT
