import AFT.ActivatedPair
import AFT.PrimarySquare
import AFT.MarkedOutput
import AFT.V7ReferenceLaws

/-! # All physical endpoint energy bounds with the actual V7 parameters -/

namespace AFT.V7Calibration

open Filter GaussianSource TrimmedSlice
open scoped BigOperators Classical Topology

noncomputable section

/-- Each actual inactive pair is normalized and has its integer-window
point height. Both signs and the true slice denominator are retained. -/
theorem actual_inactive_pair_bounds_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) :
    ∀ᶠ parameter : ℕ in atTop, ∀ source : Window (legCutoff cutoffScale parameter - 1),
      (∀ first second, 0 ≤ inactivePairAtSource cutoffScale parameter source first second) ∧
      (∑ first, ∑ second, inactivePairAtSource cutoffScale parameter source first second) = 1 ∧
      (∀ first second, inactivePairAtSource cutoffScale parameter source first second ≤
        2 / ((Parameters.anchorWidth parameter : ℝ) * Parameters.modulus parameter)) := by
  have hphysical := (actual_physical_supports_eventually cutoffScale hscale).mono fun _ h => h.1
  filter_upwards [hphysical,
    v7_primaryCalibration_clearance_eventually cutoffScale hscale (boundaryHalf cutoffScale)
      (hphysical.mono fun _ h => h.1)] with parameter hs hclear source
  have hw : Parameters.anchorWidth parameter ≠ 0 := by
    unfold Parameters.anchorWidth
    exact pow_ne_zero _ (by have := Parameters.security_ge_two parameter; omega)
  have hq : (0 : ℝ) < Parameters.modulus parameter := by exact_mod_cast (Parameters.modulus_prime parameter).pos
  have hA : (0 : ℝ) < Parameters.anchorWidth parameter := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hw)
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
        |shift| ≤ 3 * (Parameters.anchorWidth parameter : ℤ)) :
      (∀ first second, 0 ≤ mixedPair (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter)
        starts (fun _ => (source : ℤ)) (bodyBlur cutoffScale parameter).weight (Parameters.anchorWidth parameter) first second) ∧
      (∑ first, ∑ second, mixedPair (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter)
        starts (fun _ => (source : ℤ)) (bodyBlur cutoffScale parameter).weight (Parameters.anchorWidth parameter) first second) = 1 ∧
      (∀ first second, mixedPair (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter)
        starts (fun _ => (source : ℤ)) (bodyBlur cutoffScale parameter).weight (Parameters.anchorWidth parameter) first second ≤
          2 / ((Parameters.anchorWidth parameter : ℝ) * Parameters.modulus parameter)) := by
    refine ⟨mixedPair_nonneg _ _ _ _ _ _ (bodyBlur cutoffScale parameter).nonneg, ?_, ?_⟩
    · exact mixedPair_mass _ _ _ _ _ hw _ _ _ (bodyBlur cutoffScale parameter).sum_one hs.1.1 hstarts (fun _ => hsource) hc
    · intro first second
      have hh := mixedPair_le _ _ _ _ _ starts (fun _ => (source : ℤ)) (bodyBlur cutoffScale parameter).weight
        (bodyBlur cutoffScale parameter).nonneg (bodyBlur cutoffScale parameter).sum_one hstarts (fun _ => hsource) hc first second
      simp only [Int.cast_natCast, Int.cast_mul, Int.cast_ofNat] at hh
      apply hh.trans
      calc
        _ ≤ 1 / ((Parameters.anchorWidth parameter : ℝ) * ((Parameters.modulus parameter : ℝ) / 2)) :=
          one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hden hA.le)
        _ = _ := by ring
  have hp := hone (fun sample => (Parameters.anchorWidth parameter : ℤ) + bodyShift cutoffScale parameter sample)
    (fun sample shift hshift => hs.2.1 (sample, source) shift hshift)
  have hm := hone (fun sample => -(2 * (Parameters.anchorWidth parameter : ℤ)) + 1 + bodyShift cutoffScale parameter sample)
    (fun sample shift hshift => hs.2.2.1 (sample, source) shift hshift)
  refine ⟨fun first second => div_nonneg (add_nonneg (hp.1 first second) (hm.1 first second)) (by norm_num), ?_, ?_⟩
  · simp only [inactivePairAtSource, ← Finset.sum_div, Finset.sum_add_distrib, hp.2.1, hm.2.1]
    norm_num
  · intro first second
    dsimp only [inactivePairAtSource]
    linarith [hp.2.2 first second, hm.2.2 first second]

/-- The real inactive source average retains normalization and the same
window height; no independent replacement of the source is used. -/
theorem averagedInactivePair_bounds (cutoffScale : ℝ) (parameter : ℕ)
    (hpair : ∀ source : Window (legCutoff cutoffScale parameter - 1),
      (∀ first second, 0 ≤ inactivePairAtSource cutoffScale parameter source first second) ∧
      (∑ first, ∑ second, inactivePairAtSource cutoffScale parameter source first second) = 1 ∧
      (∀ first second, inactivePairAtSource cutoffScale parameter source first second ≤
        2 / ((Parameters.anchorWidth parameter : ℝ) * Parameters.modulus parameter))) :
    (∀ first second, 0 ≤ averagedInactivePair cutoffScale parameter first second) ∧
      (∑ first, ∑ second, averagedInactivePair cutoffScale parameter first second) = 1 ∧
      (∀ first second, averagedInactivePair cutoffScale parameter first second ≤
        2 / ((Parameters.anchorWidth parameter : ℝ) * Parameters.modulus parameter)) := by
  refine ⟨fun first second => Finset.sum_nonneg fun source _ =>
    mul_nonneg ((inactiveLegSource cutoffScale parameter).nonneg source) ((hpair source).1 first second), ?_, ?_⟩
  · unfold averagedInactivePair
    have hswap (first) :
        (∑ second, ∑ source, (inactiveLegSource cutoffScale parameter).weight source *
          inactivePairAtSource cutoffScale parameter source first second) =
        ∑ source, (inactiveLegSource cutoffScale parameter).weight source *
          ∑ second, inactivePairAtSource cutoffScale parameter source first second := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    simp_rw [hswap]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, (hpair _).2.1, mul_one]
    exact (inactiveLegSource cutoffScale parameter).sum_one
  · intro first second
    calc
      _ ≤ ∑ source, (inactiveLegSource cutoffScale parameter).weight source *
          (2 / ((Parameters.anchorWidth parameter : ℝ) * Parameters.modulus parameter)) :=
        Finset.sum_le_sum fun source _ => mul_le_mul_of_nonneg_left ((hpair source).2.2 first second)
          ((inactiveLegSource cutoffScale parameter).nonneg source)
      _ = _ := by rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]

/-- Actual marked companion channel, justified by its exact integer support. -/
def actualCompanionLaw (cutoffScale : ℝ) (parameter : ℕ)
    (hmass : ∀ color, (∑ output : Fin (Parameters.modulus parameter),
      blurredAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
        (bodyShift cutoffScale parameter) (bodyBlur cutoffScale parameter) color output.val) = 1)
    (color : Fin (Parameters.modulus parameter)) : FiniteDist (Fin (Parameters.modulus parameter)) where
  weight output := blurredAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
    (bodyShift cutoffScale parameter) (bodyBlur cutoffScale parameter) color output.val
  nonneg _output := blurredAnchorKernel_nonneg _ _ _ _ _ _
  sum_one := hmass color

/-- Full physical pair energy, before substituting powers of the security
parameter. The activation appears squared in the marked branch. -/
theorem actual_pair_energy_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
      BlockDensity.pairEnergy (actualReferenceMean cutoffScale parameter (beta parameter))
        (actualReferenceMean cutoffScale parameter (beta parameter))
        (localPairMixture cutoffScale parameter (beta parameter)) ≤
      8 * (v7Activation cutoffScale parameter) ^ 2 * (Parameters.modulus parameter : ℝ) ^ 2 /
        Parameters.anchorWidth parameter * (∑ color, actualPrimary cutoffScale parameter (beta parameter) color ^ 2) +
      16 * (Parameters.modulus parameter : ℝ) / Parameters.anchorWidth parameter := by
  filter_upwards [actual_inactive_pair_bounds_eventually cutoffScale hscale,
    actual_full_anchor_safe_eventually cutoffScale hscale,
    actual_reference_lower_eventually cutoffScale hscale beta hbeta] with parameter hinactive hcompanion href
  have hpair := averagedInactivePair_bounds cutoffScale parameter hinactive
  let q : ℝ := Parameters.modulus parameter
  let width : ℝ := Parameters.anchorWidth parameter
  let activation := v7Activation cutoffScale parameter
  let reference := actualReferenceMean cutoffScale parameter (beta parameter)
  have hq : 0 < q := by dsimp only [q]; exact_mod_cast (Parameters.modulus_prime parameter).pos
  have hw : 0 < width := by
    dsimp only [width, Parameters.anchorWidth]
    exact_mod_cast pow_pos (show 0 < Parameters.security parameter by have := Parameters.security_ge_two parameter; omega) 32
  have ha0 : 0 ≤ activation := by
    dsimp only [activation, v7Activation, GaussianSource.activation]
    exact mul_nonneg (by positivity) (FiniteDist.nonneg _ _)
  have ha1 : activation ≤ 1 := activation_le_one _ _ _ _
  have hr (color) : 0 ≤ reference color := (by positivity : 0 ≤ 1 / (2 * q)).trans (href color)
  let companion := actualCompanionLaw cutoffScale parameter (fun color => (hcompanion color).1)
  have hm := BlockDensity.marked_pair_energy_le reference reference
    (actualPrimary cutoffScale parameter (beta parameter)) companion activation (1 / (2 * q)) (1 / (2 * q)) width⁻¹
    (by positivity) (by positivity) href href (fun first second => blurredAnchorKernel_le _ _ _ _ _ _)
  have hd := BlockDensity.diffuse_pair_energy_le reference reference
    (fun first second => (1 - activation) * averagedInactivePair cutoffScale parameter first second)
    (1 / (2 * q)) (1 / (2 * q)) (2 / (width * q))
    (by positivity) (by positivity) (by positivity) href href
    (fun first second => mul_nonneg (by linarith) (hpair.1 first second))
    (fun first second => (mul_le_mul_of_nonneg_right (show 1 - activation ≤ 1 by linarith) (hpair.1 first second)).trans
      (by simpa only [one_mul] using hpair.2.2 first second))
    (by simp only [← Finset.mul_sum, hpair.2.1, mul_one]; linarith)
  have h := BlockDensity.pairEnergy_add_le reference hr
    (fun first second => (1 - activation) * averagedInactivePair cutoffScale parameter first second)
    (fun first second => activation * actualMarkedPair cutoffScale parameter (beta parameter) first second)
  change BlockDensity.pairEnergy reference reference (localPairMixture cutoffScale parameter (beta parameter)) ≤ _ at h
  have hm' : BlockDensity.pairEnergy reference reference
      (fun first second => activation * actualMarkedPair cutoffScale parameter (beta parameter) first second) ≤
      (activation ^ 2 * width⁻¹ / ((1 / (2 * q)) * (1 / (2 * q)))) *
        ∑ color, actualPrimary cutoffScale parameter (beta parameter) color ^ 2 := by
    simpa only [actualMarkedPair, companion, actualCompanionLaw, mul_assoc] using hm
  calc
    _ ≤ 2 * (2 / (width * q) / ((1 / (2 * q)) * (1 / (2 * q)))) +
        2 * ((activation ^ 2 * width⁻¹ / ((1 / (2 * q)) * (1 / (2 * q)))) *
          ∑ color, actualPrimary cutoffScale parameter (beta parameter) color ^ 2) :=
      h.trans (add_le_add (mul_le_mul_of_nonneg_left hd (by norm_num)) (mul_le_mul_of_nonneg_left hm' (by norm_num)))
    _ = _ := by change _ = 8 * activation ^ 2 * q ^ 2 / width * _ + 16 * q / width; field_simp; ring

/-- The complete endpoint energy has the actual V7 `λ³⁰` scale, with no
local analytic estimate left as a hypothesis. -/
theorem actual_pair_energy_power_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
      BlockDensity.pairEnergy (actualReferenceMean cutoffScale parameter (beta parameter))
        (actualReferenceMean cutoffScale parameter (beta parameter))
        (localPairMixture cutoffScale parameter (beta parameter)) ≤
          24640 * (parameter : ℝ) ^ 30 := by
  filter_upwards [actual_pair_energy_eventually cutoffScale hscale beta hbeta,
    actual_marked_primary_square_eventually cutoffScale hscale beta hbeta,
    eventually_ge_atTop 2] with parameter hp hs hlarge
  let q : ℝ := Parameters.modulus parameter
  let x : ℝ := parameter
  have hx : 0 < x := by dsimp only [x]; exact_mod_cast (by omega : 0 < parameter)
  have hx1 : 1 ≤ x := by dsimp only [x]; exact_mod_cast (by omega : 1 ≤ parameter)
  have hq : 0 < q := by dsimp only [q]; exact_mod_cast (Parameters.modulus_prime parameter).pos
  have hqBound : q ≤ 2 * x ^ 40 := by
    dsimp only [q, x]
    exact_mod_cast (show Parameters.modulus parameter ≤ 2 * parameter ^ 40 by
      simpa only [Parameters.security_eq parameter hlarge] using (Parameters.modulus_bounds parameter).2)
  have hwidth : (Parameters.anchorWidth parameter : ℝ) = x ^ 32 := by
    simp only [Parameters.anchorWidth, Parameters.security_eq parameter hlarge, Nat.cast_pow, x]
  have hfirst : 8 * (v7Activation cutoffScale parameter) ^ 2 * q ^ 2 / (x ^ 32) *
      (∑ color, actualPrimary cutoffScale parameter (beta parameter) color ^ 2) ≤ 24608 * x ^ 30 := by
    calc
      _ = (8 * q ^ 2 / x ^ 32) * ((v7Activation cutoffScale parameter) ^ 2 *
          ∑ color, actualPrimary cutoffScale parameter (beta parameter) color ^ 2) := by ring
      _ ≤ (8 * (2 * x ^ 40) ^ 2 / x ^ 32) * (769 / x ^ 18) := by
        apply mul_le_mul _ hs (by positivity) (by positivity)
        gcongr
      _ = _ := by field_simp; ring
  have hsecond : 16 * q / x ^ 32 ≤ 32 * x ^ 30 := by
    calc
      _ ≤ 16 * (2 * x ^ 40) / x ^ 32 := by gcongr
      _ = 32 * x ^ 8 := by field_simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx1 (by norm_num : 8 ≤ 30)) (by norm_num)
  rw [hwidth] at hp
  change _ ≤ 24640 * x ^ 30
  linarith

end

end AFT.V7Calibration
