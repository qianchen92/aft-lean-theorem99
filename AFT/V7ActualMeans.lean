import AFT.BodyBlurParameters

/-! # Calibrated means with every protected source and blur instantiated -/

namespace AFT.V7Calibration

open Filter GaussianSource
open scoped BigOperators Classical Topology

noncomputable section

def actualPrimary (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) :
    Fin (Parameters.modulus parameter) → ℝ :=
  primary parameter cutoffScale beta (boundaryHalf cutoffScale parameter)
    (bodyShift cutoffScale parameter) (bodyBlur cutoffScale parameter)
    (startsPlus cutoffScale parameter) (startsMinus cutoffScale parameter)
    (pairSourceShift cutoffScale parameter) (pairSourceLaw cutoffScale parameter)

def actualBodyMean (cutoffScale : ℝ) (parameter : ℕ) : Fin (Parameters.modulus parameter) → ℝ :=
  bodyMean parameter (bodyShift cutoffScale parameter) (bodyBlur cutoffScale parameter)

def actualReferenceMean (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) :
    Fin (Parameters.modulus parameter) → ℝ :=
  referenceMean parameter cutoffScale beta (boundaryHalf cutoffScale parameter)

def actualRootBodyMean (parameter : ℕ) : Fin (Parameters.modulus parameter) → ℝ :=
  bodyMean parameter (fun z : Window (v7RootCutoff parameter) => (z : ℤ))
    (rootMarginal (v7RootWidth parameter) (v7RootCutoff parameter) (Parameters.bodies parameter)
      (Parameters.bodies_positive parameter))

/-- Exact powers for the actual protected Gaussian/placement model. The
only remaining condition selects the typical beta regime itself. -/
theorem actual_body_mean_bounds (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
      (∀ color, |actualBodyMean cutoffScale parameter color - actualReferenceMean cutoffScale parameter (beta parameter) color| ≤
        (bodyMeanRelativeConstant / (parameter : ℝ) ^ (137 / 4 : ℝ)) * actualPrimary cutoffScale parameter (beta parameter) color) ∧
      profileSquareNorm (actualPrimary cutoffScale parameter (beta parameter))
        (actualBodyMean cutoffScale parameter - actualReferenceMean cutoffScale parameter (beta parameter)) ≤
        bodyMeanSquareConstant / (parameter : ℝ) ^ (289 / 4 : ℝ) := by
  apply body_reference_power_bounds_eventually cutoffScale hscale beta (boundaryHalf cutoffScale)
    (bodyShift cutoffScale) (bodyBlur cutoffScale) (startsPlus cutoffScale) (startsMinus cutoffScale)
    (pairSourceShift cutoffScale) (pairSourceLaw cutoffScale)
  filter_upwards [actual_physical_supports_eventually cutoffScale hscale, hbeta] with parameter hs hb
  exact ⟨hs.1, hs.2, hb⟩

/-- The exact unshifted root mean obeys the same exponents as the full
body mean. The proof uses the actual component of mass at least one half. -/
theorem actual_root_body_mean_bounds (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
      (∀ color, |actualRootBodyMean parameter color - actualReferenceMean cutoffScale parameter (beta parameter) color| ≤
        (2 * bodyMeanRelativeConstant / (parameter : ℝ) ^ (137 / 4 : ℝ)) * actualPrimary cutoffScale parameter (beta parameter) color) ∧
      profileSquareNorm (actualPrimary cutoffScale parameter (beta parameter))
        (actualRootBodyMean parameter - actualReferenceMean cutoffScale parameter (beta parameter)) ≤
        (2 * bodyMeanSquareConstant) / (parameter : ℝ) ^ (289 / 4 : ℝ) := by
  have hmodel := ((actual_physical_supports_eventually cutoffScale hscale).and hbeta).mono
    (fun parameter h => And.intro h.1.1 (And.intro h.1.2 h.2))
  have hphysical := hmodel.mono fun _ h => h.1
  filter_upwards [hmodel, body_support_scales_eventually cutoffScale hscale,
    body_reference_bounds_eventually cutoffScale hscale beta (boundaryHalf cutoffScale)
      (bodyShift cutoffScale) (bodyBlur cutoffScale) (startsPlus cutoffScale) (startsMinus cutoffScale)
      (pairSourceShift cutoffScale) (pairSourceLaw cutoffScale) hmodel,
    body_deficit_eventually cutoffScale hscale beta (boundaryHalf cutoffScale)
      (bodyShift cutoffScale) (bodyBlur cutoffScale) (startsPlus cutoffScale) (startsMinus cutoffScale)
      (pairSourceShift cutoffScale) (pairSourceLaw cutoffScale) hmodel,
    primary_estimates_eventually cutoffScale hscale beta (boundaryHalf cutoffScale)
      (bodyShift cutoffScale) (bodyBlur cutoffScale) (startsPlus cutoffScale) (startsMinus cutoffScale)
      (pairSourceShift cutoffScale) (pairSourceLaw cutoffScale) hmodel,
    v7_primaryCalibration_clearance_eventually cutoffScale hscale (boundaryHalf cutoffScale) (hphysical.mono fun _ h => h.1),
    v7Activation_upper_rpow_eventually cutoffScale hscale, eventually_ge_atTop 2]
    with parameter hm hs hb hd hp hclear ha hlarge
  dsimp only at hb hp
  let p := actualPrimary cutoffScale parameter (beta parameter)
  let B := actualBodyMean cutoffScale parameter
  let B0 := actualRootBodyMean parameter
  let r := actualReferenceMean cutoffScale parameter (beta parameter)
  let relative := 5 * bodyCompensation parameter cutoffScale +
    8 * (Parameters.safeMargin parameter : ℝ) /
      ((Parameters.modulus parameter : ℝ) - 2 * Parameters.safeMargin parameter)
  let upper := 1 / ((Parameters.modulus parameter : ℝ) - 2 * Parameters.safeMargin parameter)
  have hq : (0 : ℝ) < Parameters.modulus parameter := by exact_mod_cast (Parameters.modulus_prime parameter).pos
  have hsmall : 4 * (Parameters.safeMargin parameter : ℝ) ≤ Parameters.modulus parameter := by exact_mod_cast hclear.1
  have hsafe : 0 < (Parameters.modulus parameter : ℝ) - 2 * Parameters.safeMargin parameter := by linarith
  have hwidth : 2 * Parameters.safeMargin parameter < Parameters.modulus parameter := by exact_mod_cast (sub_pos.mp hsafe)
  have hp0 (color) : 0 < p color := lt_of_lt_of_le (by positivity) (hp.1 color)
  have hapos : 0 < v7Activation cutoffScale parameter := activation_positive _ _ _ _
    (legFeatureCount_positive cutoffScale parameter hscale (by omega))
  have hdelta : 0 ≤ bodyCompensation parameter cutoffScale := by unfold bodyCompensation; positivity
  have hmargin0 : (0 : ℝ) ≤ Parameters.safeMargin parameter := Nat.cast_nonneg _
  have hrel : 2 * bodyCompensation parameter cutoffScale ≤ relative := by
    dsimp only [relative]
    have hh : 0 ≤ 8 * (Parameters.safeMargin parameter : ℝ) /
      ((Parameters.modulus parameter : ℝ) - 2 * Parameters.safeMargin parameter) := by positivity
    linarith
  have hrootupper (color) : B0 color ≤ upper := by
    simpa only [B0, actualRootBodyMean, bodyMean, upper, Int.cast_natCast] using TrimmedSlice.blurredSafeLaw_le (Parameters.modulus parameter) (Parameters.safeMargin parameter)
      (fun z : Window (v7RootCutoff parameter) => (z : ℤ))
      (rootMarginal (v7RootWidth parameter) (v7RootCutoff parameter) (Parameters.bodies parameter)
        (Parameters.bodies_positive parameter)).weight
      (rootMarginal (v7RootWidth parameter) (v7RootCutoff parameter) (Parameters.bodies parameter)
        (Parameters.bodies_positive parameter)).nonneg
      (rootMarginal (v7RootWidth parameter) (v7RootCutoff parameter) (Parameters.bodies parameter)
        (Parameters.bodies_positive parameter)).sum_one (by exact_mod_cast hwidth) color.val
  have hpoint (color) : |B0 color - r color| ≤ 2 * relative * p color := by
    have hroot := root_bodyMean_deficit_le_twice cutoffScale parameter color.val hwidth
    change upper - B0 color ≤ 2 * (upper - B color) at hroot
    have hdiff : |B0 color - B color| ≤ upper - B color := by
      exact abs_le.mpr ⟨by linarith, by linarith [hrootupper color]⟩
    have hbd : upper - B color ≤ 2 * bodyCompensation parameter cutoffScale * p color := hd color
    have hbr : |B color - r color| ≤ relative * p color := hb.1 color
    have hmul := mul_le_mul_of_nonneg_right hrel (hp0 color).le
    exact (abs_sub_le (B0 color) (B color) (r color)).trans (by linarith)
  have hrootL1 : (∑ color, |B0 color - 1 / (Parameters.modulus parameter : ℝ)|) ≤
      4 * (Parameters.safeMargin parameter : ℝ) / Parameters.modulus parameter := by
    have hrootShift (z : Window (v7RootCutoff parameter)) : |(z : ℤ)| ≤ (Parameters.safeMargin parameter : ℤ) := by
      have hz := abs_le.mpr (Finset.mem_Icc.mp z.property)
      have hcut : v7RootCutoff parameter ≤ maxBodyShift cutoffScale parameter := by unfold maxBodyShift; omega
      exact hz.trans (by exact_mod_cast hcut.trans hs.1)
    simpa only [B0, actualRootBodyMean, bodyMean, Int.cast_natCast, one_div] using TrimmedSlice.blurredSafeLaw_palette_l1_le
      (Parameters.modulus parameter) (Parameters.safeMargin parameter) (fun z : Window (v7RootCutoff parameter) => (z : ℤ))
      (rootMarginal (v7RootWidth parameter) (v7RootCutoff parameter) (Parameters.bodies parameter)
        (Parameters.bodies_positive parameter)).weight (by positivity)
      (rootMarginal _ _ _ (Parameters.bodies_positive parameter)).sum_one
      (rootMarginal _ _ _ (Parameters.bodies_positive parameter)).nonneg (by exact_mod_cast hwidth) hrootShift
  have hrL1 := referenceMean_l1_le parameter cutoffScale (beta parameter) (boundaryHalf cutoffScale parameter)
    hscale (by omega) hm.2.2.1 hm.2.2.2
  have hcard : ((boundaryPalette (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter)).card : ℝ) ≤
      2 * Parameters.safeMargin parameter := by
    have hh := boundaryPalette_card (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter) hs.2.2.1
      (by have hh := hs.2.2.2; exact_mod_cast (show 2 * boundaryHalf cutoffScale parameter ≤ (Parameters.modulus parameter : ℤ) by omega))
    have hh' : ((boundaryPalette (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter)).card : ℝ) =
        2 * boundaryHalf cutoffScale parameter := by exact_mod_cast hh
    rw [hh']
    exact_mod_cast (show 2 * boundaryHalf cutoffScale parameter ≤ 2 * (Parameters.safeMargin parameter : ℤ) by linarith [hs.2.2.2])
  have hrL1' : (∑ color, |r color - 1 / (Parameters.modulus parameter : ℝ)|) ≤
      4 * (Parameters.safeMargin parameter : ℝ) / Parameters.modulus parameter := by
    exact hrL1.trans (div_le_div_of_nonneg_right (by linarith) hq.le)
  have hL1 : (∑ color, |B0 color - r color|) ≤ 8 * (Parameters.safeMargin parameter : ℝ) / Parameters.modulus parameter := by
    calc
      _ ≤ ∑ color, (|B0 color - 1 / (Parameters.modulus parameter : ℝ)| + |r color - 1 / (Parameters.modulus parameter : ℝ)|) := by
        apply Finset.sum_le_sum
        intro color _
        simpa only [abs_sub_comm (1 / (Parameters.modulus parameter : ℝ)) (r color)] using
          abs_sub_le (B0 color) (1 / (Parameters.modulus parameter : ℝ)) (r color)
      _ ≤ _ := by rw [Finset.sum_add_distrib]; exact (add_le_add hrootL1 hrL1').trans_eq (by ring)
  have hscalar := body_mean_scalar_power_bound parameter cutoffScale hlarge hsmall ha
  have hrel0 : 0 ≤ relative := (mul_nonneg (by norm_num) hdelta).trans hrel
  refine ⟨?_, ?_⟩
  · intro color
    apply (hpoint color).trans
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscalar.1 (by norm_num : (0 : ℝ) ≤ 2)) (hp0 color).le
    convert hh using 1; ring
  · have hn := profileSquareNorm_le_relative_mul_l1 p (B0 - r) (2 * relative) hp0 (by simpa using hpoint)
    have hh := hn.trans (mul_le_mul_of_nonneg_left hL1 (by positivity))
    have hs' := mul_le_mul_of_nonneg_left hscalar.2 (by norm_num : (0 : ℝ) ≤ 2)
    exact hh.trans (by convert hs' using 1 <;> ring)


end

end AFT.V7Calibration
