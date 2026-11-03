import AFT.ActualPairEnergy

/-! # Sharp first marginals of the actual activated endpoint pair -/

namespace AFT.V7Calibration

open Filter GaussianSource TrimmedSlice
open scoped BigOperators Classical Topology

noncomputable section

theorem actual_inactive_pair_marginal_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) :
    ∀ᶠ parameter : ℕ in atTop, ∀ source : Window (legCutoff cutoffScale parameter - 1),
      (∀ first, (∑ second, inactivePairAtSource cutoffScale parameter source first second) ≤
        2 / (Parameters.modulus parameter : ℝ)) ∧
      (∀ first second, inactivePairAtSource cutoffScale parameter source first second =
        inactivePairAtSource cutoffScale parameter source second first) := by
  have hphysical := (actual_physical_supports_eventually cutoffScale hscale).mono fun _ h => h.1
  filter_upwards [hphysical,
    v7_primaryCalibration_clearance_eventually cutoffScale hscale (boundaryHalf cutoffScale)
      (hphysical.mono fun _ h => h.1)] with parameter hs hclear source
  have hw : Parameters.anchorWidth parameter ≠ 0 := by
    unfold Parameters.anchorWidth
    exact pow_ne_zero _ (by have := Parameters.security_ge_two parameter; omega)
  have hq : (0 : ℝ) < Parameters.modulus parameter := by exact_mod_cast (Parameters.modulus_prime parameter).pos
  have hsource : |(source : ℤ)| ≤ legCutoff cutoffScale parameter :=
    (abs_le.mpr (Finset.mem_Icc.mp source.property)).trans (by exact_mod_cast Nat.sub_le (legCutoff cutoffScale parameter) 1)
  have hden : (Parameters.modulus parameter : ℝ) / 2 ≤ Parameters.modulus parameter -
      2 * boundaryHalf cutoffScale parameter - 3 * Parameters.anchorWidth parameter - legCutoff cutoffScale parameter := by
    have hh : (2 : ℝ) * (3 * Parameters.anchorWidth parameter + 2 * boundaryHalf cutoffScale parameter +
      legCutoff cutoffScale parameter) ≤ Parameters.modulus parameter := by exact_mod_cast hclear.2
    linarith
  have hc : 2 * boundaryHalf cutoffScale parameter + 3 * (Parameters.anchorWidth parameter : ℤ) +
      legCutoff cutoffScale parameter < Parameters.modulus parameter := by
    have hh := hclear.2
    have hq' : (0 : ℤ) < Parameters.modulus parameter := by exact_mod_cast (Parameters.modulus_prime parameter).pos
    omega
  have hone (starts : bodySample cutoffScale parameter → ℤ)
      (hstarts : ∀ sample shift, shift ∈ anchorInterval (starts sample) (Parameters.anchorWidth parameter) →
        |shift| ≤ 3 * (Parameters.anchorWidth parameter : ℤ)) (first : Fin (Parameters.modulus parameter)) :
      (∑ second, mixedPair (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter)
        starts (fun _ => (source : ℤ)) (bodyBlur cutoffScale parameter).weight (Parameters.anchorWidth parameter) first second) ≤
          2 / (Parameters.modulus parameter : ℝ) := by
    rw [mixedPair_first_marginal _ _ _ _ _ _ hs.1.1]
    have hh := mixedLaw_le _ _ _ _ starts (fun _ => (source : ℤ)) (bodyBlur cutoffScale parameter).weight
      (Parameters.anchorWidth parameter) hw (bodyBlur cutoffScale parameter).nonneg (bodyBlur cutoffScale parameter).sum_one
      hstarts (fun _ => hsource) hc first.val
    simp only [Int.cast_natCast, Int.cast_mul, Int.cast_ofNat] at hh
    exact hh.trans ((one_div_le_one_div_of_le (by positivity) hden).trans_eq (by ring))
  refine ⟨?_, ?_⟩
  · intro first
    have hp := hone (fun sample => (Parameters.anchorWidth parameter : ℤ) + bodyShift cutoffScale parameter sample)
      (fun sample shift hshift => hs.2.1 (sample, source) shift hshift) first
    have hm := hone (fun sample => -(2 * (Parameters.anchorWidth parameter : ℤ)) + 1 + bodyShift cutoffScale parameter sample)
      (fun sample shift hshift => hs.2.2.1 (sample, source) shift hshift) first
    simp only [inactivePairAtSource, ← Finset.sum_div, Finset.sum_add_distrib]
    linarith
  · intro first second
    simp only [inactivePairAtSource, mixedPair_symmetric _ _ _ _ _ _ first second]

theorem averagedInactivePair_marginal_le (cutoffScale : ℝ) (parameter : ℕ)
    (hpair : ∀ source : Window (legCutoff cutoffScale parameter - 1),
      (∀ first, (∑ second, inactivePairAtSource cutoffScale parameter source first second) ≤
        2 / (Parameters.modulus parameter : ℝ)) ∧
      (∀ first second, inactivePairAtSource cutoffScale parameter source first second =
        inactivePairAtSource cutoffScale parameter source second first)) (color : Fin (Parameters.modulus parameter)) :
    (∑ second, averagedInactivePair cutoffScale parameter color second) ≤ 2 / (Parameters.modulus parameter : ℝ) ∧
      (∑ first, averagedInactivePair cutoffScale parameter first color) ≤ 2 / (Parameters.modulus parameter : ℝ) := by
  have hfirst (color : Fin (Parameters.modulus parameter)) :
      (∑ second, averagedInactivePair cutoffScale parameter color second) ≤ 2 / (Parameters.modulus parameter : ℝ) := by
    unfold averagedInactivePair
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum]
    calc
      _ ≤ ∑ source, (inactiveLegSource cutoffScale parameter).weight source * (2 / (Parameters.modulus parameter : ℝ)) :=
        Finset.sum_le_sum fun source _ => mul_le_mul_of_nonneg_left ((hpair source).1 color)
          ((inactiveLegSource cutoffScale parameter).nonneg source)
      _ = _ := by rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]
  refine ⟨hfirst color, ?_⟩
  have heq (first second) : averagedInactivePair cutoffScale parameter first second =
      averagedInactivePair cutoffScale parameter second first := by
    simp only [averagedInactivePair, (hpair _).2 first second]
  simpa only [heq] using hfirst color

/-- The first endpoint retains the sharp squared-primary cost; the second
endpoint is bounded by the actual companion height, not by primary height. -/
theorem actual_pair_marginal_bounds_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ color,
      (∑ second, localPairMixture cutoffScale parameter (beta parameter) color second) ≤
        v7Activation cutoffScale parameter * actualPrimary cutoffScale parameter (beta parameter) color +
          2 / (Parameters.modulus parameter : ℝ) ∧
      (∑ first, localPairMixture cutoffScale parameter (beta parameter) first color) ≤
        1 / (Parameters.anchorWidth parameter : ℝ) + 2 / (Parameters.modulus parameter : ℝ) := by
  filter_upwards [actual_inactive_pair_marginal_eventually cutoffScale hscale,
    actual_inactive_pair_bounds_eventually cutoffScale hscale,
    actual_full_anchor_safe_eventually cutoffScale hscale,
    actual_primary_probability_eventually cutoffScale hscale beta hbeta] with parameter hm hi hc hp color
  have hd := averagedInactivePair_marginal_le cutoffScale parameter hm color
  have hn := (averagedInactivePair_bounds cutoffScale parameter hi).1
  let a := v7Activation cutoffScale parameter
  have ha0 : 0 ≤ a := by
    dsimp only [a, v7Activation, GaussianSource.activation]
    exact mul_nonneg (by positivity) (FiniteDist.nonneg _ _)
  have ha1 : a ≤ 1 := activation_le_one _ _ _ _
  have hinactiveFirst : (1 - a) * (∑ second, averagedInactivePair cutoffScale parameter color second) ≤
      2 / (Parameters.modulus parameter : ℝ) :=
    (mul_le_mul_of_nonneg_right (show 1 - a ≤ 1 by linarith) (Finset.sum_nonneg fun second _ => hn color second)).trans
      (by simpa only [one_mul] using hd.1)
  have hinactiveSecond : (1 - a) * (∑ first, averagedInactivePair cutoffScale parameter first color) ≤
      2 / (Parameters.modulus parameter : ℝ) :=
    (mul_le_mul_of_nonneg_right (show 1 - a ≤ 1 by linarith) (Finset.sum_nonneg fun first _ => hn first color)).trans
      (by simpa only [one_mul] using hd.2)
  have hmarkedFirst : (∑ second, actualMarkedPair cutoffScale parameter (beta parameter) color second) =
      actualPrimary cutoffScale parameter (beta parameter) color := by
    simp only [actualMarkedPair, ← Finset.mul_sum, (hc color).1, mul_one]
  have hmarkedSecond : (∑ first, actualMarkedPair cutoffScale parameter (beta parameter) first color) ≤
      (Parameters.anchorWidth parameter : ℝ)⁻¹ := by
    calc
      _ ≤ ∑ first, actualPrimary cutoffScale parameter (beta parameter) first * (Parameters.anchorWidth parameter : ℝ)⁻¹ :=
        Finset.sum_le_sum fun first _ => mul_le_mul_of_nonneg_left (blurredAnchorKernel_le _ _ _ _ _ _) (hp.1 first).le
      _ = _ := by rw [← Finset.sum_mul, hp.2, one_mul]
  simp only [localPairMixture, Finset.sum_add_distrib, ← Finset.mul_sum]
  refine ⟨?_, ?_⟩
  · rw [hmarkedFirst]
    linarith
  · have hs := mul_le_mul_of_nonneg_left hmarkedSecond ha0
    have ha := mul_le_mul_of_nonneg_right ha1 (show 0 ≤ (Parameters.anchorWidth parameter : ℝ)⁻¹ by positivity)
    simp only [one_mul, ← one_div] at hs ha
    linarith

end

end AFT.V7Calibration
