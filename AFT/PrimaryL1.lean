import AFT.V7ActualMeans
import AFT.ActivationSharp

/-! # Total variation of the actual calibrated primary distribution -/

namespace AFT

open Filter
open scoped BigOperators Classical Topology

noncomputable section

theorem basePrimaryProfile_uniform_l1_le {ι : Type*} [Fintype ι]
    (bodies legs activation : ℝ) (uniform body shifted unshifted : ι → ℝ)
    (bodyBound sliceBound : ℝ) (hN : 0 ≤ bodies) (hm : 0 < legs)
    (ha : 0 < activation) (ha1 : activation ≤ 1)
    (hbody : (∑ c, |body c - uniform c|) ≤ bodyBound)
    (hshift : (∑ c, |shifted c - uniform c|) ≤ sliceBound)
    (hunshift : (∑ c, |unshifted c - uniform c|) ≤ sliceBound) :
    (∑ c, |basePrimaryProfile (bodies + 2 * legs) bodies legs activation uniform body shifted unshifted c - uniform c|) ≤
      ((bodies + 2 * legs) / (legs * activation)) * bodyBound + (4 / activation) * sliceBound := by
  have hf (c) : basePrimaryProfile (bodies + 2 * legs) bodies legs activation uniform body shifted unshifted c - uniform c =
      -((bodies + legs * activation) / (legs * activation)) * (body c - uniform c) -
        (2 / activation) * (shifted c - uniform c) + 2 * (unshifted c - uniform c) := by
    unfold basePrimaryProfile
    field_simp
    ring
  have hb0 : 0 ≤ bodyBound := (Finset.sum_nonneg fun _ _ => abs_nonneg _).trans hbody
  have hs0 : 0 ≤ sliceBound := (Finset.sum_nonneg fun _ _ => abs_nonneg _).trans hshift
  have hpoint (c) : |basePrimaryProfile (bodies + 2 * legs) bodies legs activation uniform body shifted unshifted c - uniform c| ≤
      ((bodies + legs * activation) / (legs * activation)) * |body c - uniform c| +
        (2 / activation) * |shifted c - uniform c| + 2 * |unshifted c - uniform c| := by
    rw [hf]
    calc
      _ ≤ |-((bodies + legs * activation) / (legs * activation)) * (body c - uniform c) -
        (2 / activation) * (shifted c - uniform c)| + |2 * (unshifted c - uniform c)| := abs_add_le _ _
      _ ≤ _ := by
        have hh := abs_sub (-((bodies + legs * activation) / (legs * activation)) * (body c - uniform c))
          ((2 / activation) * (shifted c - uniform c))
        simp only [abs_mul, abs_neg, abs_of_nonneg (show 0 ≤ (bodies + legs * activation) / (legs * activation) by positivity),
          abs_of_nonneg (show 0 ≤ 2 / activation by positivity), abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)] at hh ⊢
        linarith
  have hsum := Finset.sum_le_sum fun c (_ : c ∈ Finset.univ) => hpoint c
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hcoeff : (bodies + legs * activation) / (legs * activation) ≤ (bodies + 2 * legs) / (legs * activation) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  have htwo : (2 : ℝ) ≤ 2 / activation := (le_div_iff₀ ha).mpr (by linarith)
  calc
    _ ≤ ((bodies + legs * activation) / (legs * activation)) * bodyBound +
        (2 / activation) * sliceBound + 2 * sliceBound := hsum.trans (by gcongr)
    _ ≤ ((bodies + 2 * legs) / (legs * activation)) * bodyBound +
        (2 / activation) * sliceBound + (2 / activation) * sliceBound := by
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_right hcoeff hb0) le_rfl)
        (mul_le_mul_of_nonneg_right htwo hs0)
    _ = _ := by ring

namespace TrimmedSlice

theorem fairMixedLaw_palette_l1_le {τ : Type*} [Fintype τ]
    (modulus : ℕ) (boundary shiftBound cutoff : ℤ) (width : ℕ) (hwidth : width ≠ 0)
    (startsPlus startsMinus sources : τ → ℤ) (weights : τ → ℝ)
    (hweights : ∀ i, 0 ≤ weights i) (hmass : ∑ i, weights i = 1) (hboundary : 0 ≤ boundary)
    (hplus : ∀ i s, s ∈ anchorInterval (startsPlus i) width → |s| ≤ shiftBound)
    (hminus : ∀ i s, s ∈ anchorInterval (startsMinus i) width → |s| ≤ shiftBound)
    (hsources : ∀ i, |sources i| ≤ cutoff)
    (hclearance : 2 * boundary + shiftBound + cutoff < modulus) :
    (∑ color : Fin modulus, |fairMixedLaw modulus boundary startsPlus startsMinus sources weights width color.val -
      (modulus : ℝ)⁻¹|) ≤ 2 * ((shiftBound : ℝ) + cutoff + 2 * boundary) / modulus := by
  have hp := mixedLaw_palette_l1_le modulus boundary shiftBound cutoff width hwidth startsPlus sources weights
    hweights hmass hboundary hplus hsources hclearance
  have hm := mixedLaw_palette_l1_le modulus boundary shiftBound cutoff width hwidth startsMinus sources weights
    hweights hmass hboundary hminus hsources hclearance
  calc
    _ ≤ ∑ color : Fin modulus, (|mixedLaw modulus boundary startsPlus sources weights width color.val - (modulus : ℝ)⁻¹| +
        |mixedLaw modulus boundary startsMinus sources weights width color.val - (modulus : ℝ)⁻¹|) / 2 := by
      apply Finset.sum_le_sum
      intro color _
      unfold fairMixedLaw
      have heq (a b u : ℝ) : (a + b) / 2 - u = ((a - u) + (b - u)) / 2 := by ring
      rw [heq, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)
    _ ≤ _ := by rw [← Finset.sum_div, Finset.sum_add_distrib]; linarith

end TrimmedSlice

namespace V7Calibration
open GaussianSource

def actualBasePrimary (cutoffScale : ℝ) (parameter : ℕ) : Fin (Parameters.modulus parameter) → ℝ :=
  basePrimary parameter cutoffScale (boundaryHalf cutoffScale parameter)
    (bodyShift cutoffScale parameter) (bodyBlur cutoffScale parameter)
    (startsPlus cutoffScale parameter) (startsMinus cutoffScale parameter)
    (pairSourceShift cutoffScale parameter) (pairSourceLaw cutoffScale parameter)

/-- The true signed calibration numerator is close to palette uniform.
The activation is retained explicitly for the later anchor estimate. -/
theorem actual_base_primary_l1_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) :
    ∀ᶠ parameter : ℕ in atTop,
      (∑ color, |actualBasePrimary cutoffScale parameter color - 1 / (Parameters.modulus parameter : ℝ)|) ≤
        112 / (v7Activation cutoffScale parameter * (parameter : ℝ) ^ 8) := by
  have hphysical := (actual_physical_supports_eventually cutoffScale hscale).mono fun _ h => h.1
  filter_upwards [actual_physical_supports_eventually cutoffScale hscale,
    body_support_scales_eventually cutoffScale hscale,
    legCutoff_le_square_eventually cutoffScale hscale,
    v7_primaryCalibration_clearance_eventually cutoffScale hscale (boundaryHalf cutoffScale) (hphysical.mono fun _ h => h.1),
    eventually_ge_atTop 2] with parameter hphysical hscales hcut hclear hp
  have hx : (0 : ℝ) < parameter := by exact_mod_cast (by omega : 0 < parameter)
  have hq : (0 : ℝ) < Parameters.modulus parameter := by exact_mod_cast (Parameters.modulus_prime parameter).pos
  have hm : (0 : ℝ) < Parameters.legs parameter := by
    simp only [Parameters.legs, Parameters.security_eq parameter hp, Nat.cast_pow]; positivity
  have ha : 0 < v7Activation cutoffScale parameter := activation_positive _ _ _ _ (legFeatureCount_positive cutoffScale parameter hscale (by omega))
  have ha1 : v7Activation cutoffScale parameter ≤ 1 :=
    (activation_le_one_hundredth _ _ _ _).trans (by norm_num)
  have hmargin : (Parameters.safeMargin parameter : ℝ) = 20 * (parameter : ℝ) ^ 2 := by
    simp only [Parameters.safeMargin, Parameters.security_eq parameter hp, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  have hanchor : (Parameters.anchorWidth parameter : ℝ) = (parameter : ℝ) ^ 32 := by
    simp only [Parameters.anchorWidth, Parameters.security_eq parameter hp, Nat.cast_pow]
  have hlegs : (Parameters.legs parameter : ℝ) = (parameter : ℝ) ^ 30 := by
    simp only [Parameters.legs, Parameters.security_eq parameter hp, Nat.cast_pow]
  have hdim : (Parameters.dimension parameter : ℝ) = (Parameters.modulus parameter : ℝ) * (parameter : ℝ) ^ 20 := by
    simp only [Parameters.dimension, Parameters.meanDensity, Parameters.security_eq parameter hp, Nat.cast_mul, Nat.cast_pow]
  have hpop : (Parameters.bodies parameter : ℝ) + 2 * Parameters.legs parameter = Parameters.dimension parameter := by
    exact_mod_cast Parameters.population_identity parameter
  have hqpow : (parameter : ℝ) ^ 40 ≤ Parameters.modulus parameter := by
    exact_mod_cast (show parameter ^ 40 ≤ Parameters.modulus parameter by simpa only [Parameters.security_eq parameter hp] using (Parameters.modulus_bounds parameter).1)
  have hsafe : 2 * (Parameters.safeMargin parameter : ℤ) < Parameters.modulus parameter := by
    have hq' := (Parameters.modulus_prime parameter).pos
    omega
  have hbody := TrimmedSlice.blurredSafeLaw_palette_l1_le (Parameters.modulus parameter) (Parameters.safeMargin parameter)
    (bodyShift cutoffScale parameter) (bodyBlur cutoffScale parameter).weight (by positivity)
    (bodyBlur cutoffScale parameter).sum_one (bodyBlur cutoffScale parameter).nonneg hsafe
    (fun sample => (bodyShift_abs_le cutoffScale parameter sample).trans (by exact_mod_cast hscales.1))
  have hwidth : Parameters.anchorWidth parameter ≠ 0 := by
    unfold Parameters.anchorWidth
    exact ne_of_gt (pow_pos (lt_of_lt_of_le (by decide : 0 < 2) (Parameters.security_ge_two parameter)) 32)
  have hclear' : 2 * boundaryHalf cutoffScale parameter + 3 * (Parameters.anchorWidth parameter : ℤ) + legCutoff cutoffScale parameter < Parameters.modulus parameter := by
    have hq' := (Parameters.modulus_prime parameter).pos
    omega
  have hslice := TrimmedSlice.fairMixedLaw_palette_l1_le (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter)
    (3 * (Parameters.anchorWidth parameter : ℤ)) (legCutoff cutoffScale parameter) (Parameters.anchorWidth parameter) hwidth
    (startsPlus cutoffScale parameter) (startsMinus cutoffScale parameter) (pairSourceShift cutoffScale parameter)
    (pairSourceLaw cutoffScale parameter).weight (pairSourceLaw cutoffScale parameter).nonneg (pairSourceLaw cutoffScale parameter).sum_one
    hphysical.1.1.1 hphysical.1.2.1 hphysical.1.2.2.1 hphysical.1.2.2.2 hclear'
  have hslice0 := TrimmedSlice.fairMixedLaw_palette_l1_le (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter)
    (3 * (Parameters.anchorWidth parameter : ℤ)) (legCutoff cutoffScale parameter) (Parameters.anchorWidth parameter) hwidth
    (startsPlus cutoffScale parameter) (startsMinus cutoffScale parameter) (fun _ => 0)
    (pairSourceLaw cutoffScale parameter).weight (pairSourceLaw cutoffScale parameter).nonneg (pairSourceLaw cutoffScale parameter).sum_one
    hphysical.1.1.1 hphysical.1.2.1 hphysical.1.2.2.1 (by intro; simp) hclear'
  have hminor : (legCutoff cutoffScale parameter : ℤ) + 2 * boundaryHalf cutoffScale parameter ≤ Parameters.anchorWidth parameter := by
    have h41 : 41 ≤ parameter ^ 30 := by have hh := Nat.pow_le_pow_left hp 30; omega
    have hh := Nat.mul_le_mul_right (parameter ^ 2) h41
    have hh' : 41 * parameter ^ 2 ≤ Parameters.anchorWidth parameter := by
      simpa only [Parameters.anchorWidth, Parameters.security_eq parameter hp, ← pow_add] using hh
    have hh'' : Parameters.safeMargin parameter = 20 * parameter ^ 2 := by simp only [Parameters.safeMargin, Parameters.security_eq parameter hp]
    omega
  have hsliceBound : 2 * (((3 * (Parameters.anchorWidth parameter : ℤ) : ℤ) : ℝ) +
      (legCutoff cutoffScale parameter : ℝ) + 2 * (boundaryHalf cutoffScale parameter : ℝ)) / Parameters.modulus parameter ≤
      8 / (parameter : ℝ) ^ 8 := by
    have hminor' : (legCutoff cutoffScale parameter : ℝ) + 2 * boundaryHalf cutoffScale parameter ≤ Parameters.anchorWidth parameter := by exact_mod_cast hminor
    simp only [Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
    calc
      _ ≤ (8 * (Parameters.anchorWidth parameter : ℝ)) / Parameters.modulus parameter := by
        apply div_le_div_of_nonneg_right _ hq.le
        linarith
      _ ≤ (8 * (parameter : ℝ) ^ 32) / (parameter : ℝ) ^ 40 := by rw [hanchor]; exact div_le_div_of_nonneg_left (by positivity) (by positivity) hqpow
      _ = _ := by field_simp
  have hh := basePrimaryProfile_uniform_l1_le (Parameters.bodies parameter) (Parameters.legs parameter)
    (v7Activation cutoffScale parameter) (fun _ : Fin (Parameters.modulus parameter) => 1 / (Parameters.modulus parameter : ℝ))
    (fun color => TrimmedSlice.blurredSafeLaw (Parameters.modulus parameter) (Parameters.safeMargin parameter)
      (bodyShift cutoffScale parameter) (bodyBlur cutoffScale parameter).weight color.val)
    (fun color => TrimmedSlice.fairMixedLaw (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter)
      (startsPlus cutoffScale parameter) (startsMinus cutoffScale parameter) (pairSourceShift cutoffScale parameter) (pairSourceLaw cutoffScale parameter).weight (Parameters.anchorWidth parameter) color.val)
    (fun color => TrimmedSlice.fairMixedLaw (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter)
      (startsPlus cutoffScale parameter) (startsMinus cutoffScale parameter) (fun _ => 0) (pairSourceLaw cutoffScale parameter).weight (Parameters.anchorWidth parameter) color.val)
    (4 * (Parameters.safeMargin parameter : ℝ) / Parameters.modulus parameter) (8 / (parameter : ℝ) ^ 8)
    (by positivity) hm ha ha1 (by simpa only [one_div, Int.cast_natCast] using hbody)
    (by simpa only [one_div] using hslice.trans hsliceBound) (by simpa only [one_div] using hslice0.trans hsliceBound)
  change (∑ color, |actualBasePrimary cutoffScale parameter color - 1 / (Parameters.modulus parameter : ℝ)|) ≤ _ at hh
  apply hh.trans
  rw [hpop, hdim, hlegs, hmargin]
  field_simp
  norm_num

/-- The complete beta repair remains close to uniform, with the actual
activation retained and the reference fringe bounded separately. -/
theorem actual_primary_uniform_l1_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
      (∑ color, |actualPrimary cutoffScale parameter (beta parameter) color - 1 / (Parameters.modulus parameter : ℝ)|) ≤
        192 / (v7Activation cutoffScale parameter * (parameter : ℝ) ^ 8) ∧
      (∑ color, |actualReferenceMean cutoffScale parameter (beta parameter) color - 1 / (Parameters.modulus parameter : ℝ)|) ≤
        80 / (parameter : ℝ) ^ 38 := by
  have hphysical := (actual_physical_supports_eventually cutoffScale hscale).mono fun _ h => h.1
  filter_upwards [actual_base_primary_l1_eventually cutoffScale hscale, hbeta,
    body_support_scales_eventually cutoffScale hscale,
    v7_primaryCalibration_clearance_eventually cutoffScale hscale (boundaryHalf cutoffScale) (hphysical.mono fun _ h => h.1),
    eventually_ge_atTop 2] with parameter hbase hb hs hclear hp
  have hx : (0 : ℝ) < parameter := by exact_mod_cast (by omega : 0 < parameter)
  have hq : (0 : ℝ) < Parameters.modulus parameter := by exact_mod_cast (Parameters.modulus_prime parameter).pos
  have hm : (0 : ℝ) < Parameters.legs parameter := by
    simp only [Parameters.legs, Parameters.security_eq parameter hp, Nat.cast_pow]; positivity
  have hn : (0 : ℝ) < Parameters.dimension parameter := by
    simp only [Parameters.dimension, Nat.cast_mul, Parameters.meanDensity, Parameters.security_eq parameter hp, Nat.cast_pow]; positivity
  have ha : 0 < v7Activation cutoffScale parameter := activation_positive _ _ _ _
    (legFeatureCount_positive cutoffScale parameter hscale (by omega))
  have hcard : ((boundaryPalette (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter)).card : ℝ) ≤
      40 * (parameter : ℝ) ^ 2 := by
    have heq := boundaryPalette_card (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter) hs.2.2.1
      (by have hh := hs.2.2.2; omega)
    have heq' : ((boundaryPalette (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter)).card : ℝ) =
        2 * boundaryHalf cutoffScale parameter := by exact_mod_cast heq
    rw [heq']
    have hh : (boundaryHalf cutoffScale parameter : ℝ) ≤ Parameters.safeMargin parameter := by exact_mod_cast hs.2.2.2
    have he : (Parameters.safeMargin parameter : ℝ) = 20 * (parameter : ℝ) ^ 2 := by
      simp only [Parameters.safeMargin, Parameters.security_eq parameter hp, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
    linarith
  have hmass := beta_boundary_mass_bounds (Parameters.dimension parameter) (Parameters.legs parameter)
    (v7Activation cutoffScale parameter)
    ((boundaryPalette (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter)).card / (Parameters.modulus parameter : ℝ))
    (beta parameter) hn hm ha (by positivity) hb.1 hb.2
  have heq : (Parameters.dimension parameter : ℝ) *
      ((boundaryPalette (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter)).card / (Parameters.modulus parameter : ℝ)) /
      (Parameters.legs parameter * v7Activation cutoffScale parameter) =
      v7BaseBoundaryMass cutoffScale parameter (boundaryHalf cutoffScale parameter) := by unfold v7BaseBoundaryMass; ring
  rw [heq] at hmass
  change v7BaseBoundaryMass cutoffScale parameter (boundaryHalf cutoffScale parameter) / 2 ≤
      repairedBoundaryMass parameter cutoffScale (beta parameter) (boundaryHalf cutoffScale parameter) ∧
    repairedBoundaryMass parameter cutoffScale (beta parameter) (boundaryHalf cutoffScale parameter) ≤
      2 * v7BaseBoundaryMass cutoffScale parameter (boundaryHalf cutoffScale parameter) at hmass
  have hchange : |repairedBoundaryMass parameter cutoffScale (beta parameter) (boundaryHalf cutoffScale parameter) -
      v7BaseBoundaryMass cutoffScale parameter (boundaryHalf cutoffScale parameter)| ≤
      v7BaseBoundaryMass cutoffScale parameter (boundaryHalf cutoffScale parameter) := by
    have hb0 : 0 ≤ v7BaseBoundaryMass cutoffScale parameter (boundaryHalf cutoffScale parameter) := by unfold v7BaseBoundaryMass; positivity
    exact abs_le.mpr ⟨by linarith [hmass.1], by linarith [hmass.2]⟩
  have hbaseMass : v7BaseBoundaryMass cutoffScale parameter (boundaryHalf cutoffScale parameter) ≤
      40 / (v7Activation cutoffScale parameter * (parameter : ℝ) ^ 8) := by
    unfold v7BaseBoundaryMass
    calc
      _ ≤ (Parameters.dimension parameter : ℝ) * (40 * (parameter : ℝ) ^ 2) /
          ((Parameters.modulus parameter : ℝ) * Parameters.legs parameter * v7Activation cutoffScale parameter) := by gcongr
      _ = _ := by
        simp only [Parameters.dimension, Parameters.meanDensity, Parameters.legs,
          Parameters.security_eq parameter hp, Nat.cast_mul, Nat.cast_pow]
        field_simp
  have hrepair : (∑ color, |actualPrimary cutoffScale parameter (beta parameter) color - actualBasePrimary cutoffScale parameter color|) ≤
      80 / (v7Activation cutoffScale parameter * (parameter : ℝ) ^ 8) := by
    simp only [actualPrimary, actualBasePrimary, primary, calibratedPrimaryProfile, Pi.add_apply,
      Pi.smul_apply, Pi.sub_apply, smul_eq_mul, add_sub_cancel_left, abs_mul]
    rw [← Finset.mul_sum]
    calc
      _ ≤ v7BaseBoundaryMass cutoffScale parameter (boundaryHalf cutoffScale parameter) * 2 :=
        mul_le_mul hchange (uniformFiniteProfile_difference_l1_le_two _ _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
          (by unfold v7BaseBoundaryMass; positivity)
      _ ≤ _ := by have hh := mul_le_mul_of_nonneg_right hbaseMass (by norm_num : (0 : ℝ) ≤ 2); convert hh using 1; ring
  refine ⟨?_, ?_⟩
  · calc
      _ ≤ ∑ color, (|actualPrimary cutoffScale parameter (beta parameter) color - actualBasePrimary cutoffScale parameter color| +
          |actualBasePrimary cutoffScale parameter color - 1 / (Parameters.modulus parameter : ℝ)|) :=
        Finset.sum_le_sum fun _ _ => abs_sub_le _ _ _
      _ ≤ _ := by rw [Finset.sum_add_distrib]; exact (add_le_add hrepair hbase).trans_eq (by ring)
  · have hr := referenceMean_l1_le parameter cutoffScale (beta parameter) (boundaryHalf cutoffScale parameter)
      hscale (by omega) hb.1 hb.2
    have hqpow : (parameter : ℝ) ^ 40 ≤ Parameters.modulus parameter := by
      exact_mod_cast (show parameter ^ 40 ≤ Parameters.modulus parameter by simpa only [Parameters.security_eq parameter hp] using (Parameters.modulus_bounds parameter).1)
    apply hr.trans
    calc
      _ ≤ (2 * (40 * (parameter : ℝ) ^ 2)) / (parameter : ℝ) ^ 40 := by
        apply div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hcard (by norm_num)) (by positivity) hqpow
      _ = _ := by field_simp; norm_num

/-- The Section 9 exponent for the true primary-reference total variation. -/
theorem actual_primary_reference_l1_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
      (∑ color, |actualPrimary cutoffScale parameter (beta parameter) color - actualReferenceMean cutoffScale parameter (beta parameter) color|) ≤
        (192 * activationConstant cutoffScale + 80) / (parameter : ℝ) ^ (15 / 4 : ℝ) := by
  filter_upwards [actual_primary_uniform_l1_eventually cutoffScale hscale beta hbeta, eventually_ge_atTop 2]
    with parameter hL1 hp
  have hx : (0 : ℝ) < parameter := by exact_mod_cast (by omega : 0 < parameter)
  have hx1 : (1 : ℝ) ≤ parameter := by exact_mod_cast (by omega : 1 ≤ parameter)
  have heq : (parameter : ℝ) ^ (17 / 4 : ℝ) * (parameter : ℝ) ^ (15 / 4 : ℝ) = (parameter : ℝ) ^ 8 := by
    rw [← Real.rpow_add hx]; norm_num
    exact Real.rpow_natCast _ 8
  have hmain : 192 / (v7Activation cutoffScale parameter * (parameter : ℝ) ^ 8) ≤
      (192 * activationConstant cutoffScale) / (parameter : ℝ) ^ (15 / 4 : ℝ) := by
    have hi := v7Activation_inverse_upper cutoffScale parameter hscale (by omega)
    calc
      _ = (192 / (parameter : ℝ) ^ 8) * (v7Activation cutoffScale parameter)⁻¹ := by ring
      _ ≤ (192 / (parameter : ℝ) ^ 8) * (activationConstant cutoffScale * (parameter : ℝ) ^ (17 / 4 : ℝ)) := by gcongr
      _ = _ := by rw [← heq]; field_simp
  have href : 80 / (parameter : ℝ) ^ 38 ≤ 80 / (parameter : ℝ) ^ (15 / 4 : ℝ) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (15 / 4 : ℝ) ≤ (38 : ℕ))
  calc
    _ ≤ ∑ color, (|actualPrimary cutoffScale parameter (beta parameter) color - 1 / (Parameters.modulus parameter : ℝ)| +
        |actualReferenceMean cutoffScale parameter (beta parameter) color - 1 / (Parameters.modulus parameter : ℝ)|) := by
      apply Finset.sum_le_sum
      intro color _
      simpa only [abs_sub_comm (1 / (Parameters.modulus parameter : ℝ)) _] using
        abs_sub_le (actualPrimary cutoffScale parameter (beta parameter) color) (1 / (Parameters.modulus parameter : ℝ))
          (actualReferenceMean cutoffScale parameter (beta parameter) color)
    _ ≤ _ := by
      rw [Finset.sum_add_distrib]
      exact (add_le_add (hL1.1.trans hmain) (hL1.2.trans href)).trans_eq (by ring)

end V7Calibration
end
end AFT
