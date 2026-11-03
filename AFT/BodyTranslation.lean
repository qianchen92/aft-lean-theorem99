import AFT.BodyFringeBounds

/-! # True interval translation variation of the calibrated body center -/

namespace AFT.V7Calibration

open Filter GaussianSource
open scoped BigOperators Classical Topology

noncomputable section

theorem publicAnchorKernel_translation_l1 (parameter : ℕ) (color : Fin (Parameters.modulus parameter)) (shift : ℤ) :
    (∑ output : Fin (Parameters.modulus parameter),
      |publicAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color ((output.val : ℤ) - shift) -
        publicAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color output.val|) ≤
      2 * (shift.natAbs : ℝ) / Parameters.anchorWidth parameter := by
  have hpoint (output : Fin (Parameters.modulus parameter)) :
      |publicAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color ((output.val : ℤ) - shift) -
        publicAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color output.val| ≤
      (|intervalAnchorLaw (publicAnchorStart (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color true)
          (Parameters.anchorWidth parameter) ((output.val : ℤ) - shift) -
        intervalAnchorLaw (publicAnchorStart (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color true)
          (Parameters.anchorWidth parameter) output.val| +
      |intervalAnchorLaw (publicAnchorStart (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color false)
          (Parameters.anchorWidth parameter) ((output.val : ℤ) - shift) -
        intervalAnchorLaw (publicAnchorStart (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color false)
          (Parameters.anchorWidth parameter) output.val|) / 2 := by
    unfold publicAnchorKernel
    have hh := abs_add_le
      (intervalAnchorLaw (publicAnchorStart (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color true)
          (Parameters.anchorWidth parameter) ((output.val : ℤ) - shift) -
        intervalAnchorLaw (publicAnchorStart (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color true)
          (Parameters.anchorWidth parameter) output.val)
      (intervalAnchorLaw (publicAnchorStart (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color false)
          (Parameters.anchorWidth parameter) ((output.val : ℤ) - shift) -
        intervalAnchorLaw (publicAnchorStart (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color false)
          (Parameters.anchorWidth parameter) output.val)
    have heq (a b c d : ℝ) : (a + b) / 2 - (c + d) / 2 = ((a - c) + (b - d)) / 2 := by ring
    rw [heq, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right hh (by norm_num)
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun output _ => hpoint output)
  simp only [← Finset.sum_div, Finset.sum_add_distrib] at hh
  have h1 := interval_palette_translation_l1_le parameter
    (publicAnchorStart (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color true) shift (Parameters.anchorWidth parameter)
  have h2 := interval_palette_translation_l1_le parameter
    (publicAnchorStart (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color false) shift (Parameters.anchorWidth parameter)
  linarith

theorem anchorMean_translation_l1 (parameter : ℕ) (primary : Fin (Parameters.modulus parameter) → ℝ)
    (hn : ∀ color, 0 ≤ primary color) (hm : ∑ color, primary color = 1) (shift : ℤ) :
    (∑ output : Fin (Parameters.modulus parameter),
      |anchorMean (Parameters.modulus parameter) (Parameters.anchorWidth parameter) primary ((output.val : ℤ) - shift) -
        anchorMean (Parameters.modulus parameter) (Parameters.anchorWidth parameter) primary output.val|) ≤
      2 * (shift.natAbs : ℝ) / Parameters.anchorWidth parameter := by
  have hpoint (output : Fin (Parameters.modulus parameter)) :
      |anchorMean (Parameters.modulus parameter) (Parameters.anchorWidth parameter) primary ((output.val : ℤ) - shift) -
        anchorMean (Parameters.modulus parameter) (Parameters.anchorWidth parameter) primary output.val| ≤
      ∑ color, primary color *
        |publicAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color ((output.val : ℤ) - shift) -
          publicAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color output.val| := by
    unfold anchorMean
    rw [← Finset.sum_sub_distrib]
    simp_rw [← mul_sub]
    exact (Finset.abs_sum_le_sum_abs _ _).trans_eq (by simp only [abs_mul, abs_of_nonneg (hn _)])
  calc
    _ ≤ ∑ output : Fin (Parameters.modulus parameter), ∑ color, primary color *
        |publicAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color ((output.val : ℤ) - shift) -
          publicAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color output.val| :=
      Finset.sum_le_sum fun output _ => hpoint output
    _ = ∑ color, primary color * ∑ output : Fin (Parameters.modulus parameter),
        |publicAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color ((output.val : ℤ) - shift) -
          publicAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color output.val| := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ ∑ color, primary color * (2 * (shift.natAbs : ℝ) / Parameters.anchorWidth parameter) := by
      exact Finset.sum_le_sum fun color _ => mul_le_mul_of_nonneg_left (publicAnchorKernel_translation_l1 parameter color shift) (hn color)
    _ = _ := by rw [← Finset.sum_mul, hm, one_mul]

theorem publicAnchorKernel_integer_support (parameter : ℕ) (color : Fin (Parameters.modulus parameter))
    (output : ℤ) (hout : output < 0 ∨ (Parameters.modulus parameter : ℤ) ≤ output) :
    publicAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color output = 0 := by
  have hw : Parameters.anchorWidth parameter ≠ 0 := by
    unfold Parameters.anchorWidth
    exact pow_ne_zero _ (by have := Parameters.security_ge_two parameter; omega)
  have hh := publicAnchorKernel_safe_mass (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
    0 0 hw (Parameters.anchor_clearance parameter) (by norm_num) (by simp) color
  have hz := hh.2 output (by simpa using hout)
  convert hz using 1
  simp

def actualBodyIntegerProfile (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) (output : ℤ) : ℝ :=
  (1 + bodyCompensation parameter cutoffScale) * coreIntegerProfile parameter output -
    bodyCompensation parameter cutoffScale * anchorMean (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
      (actualPrimary cutoffScale parameter beta) output

theorem actualBodyIntegerProfile_on_palette (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (output : Fin (Parameters.modulus parameter)) :
    actualBodyIntegerProfile cutoffScale parameter beta output.val = actualBodyCenter cutoffScale parameter beta output := by
  simp only [actualBodyIntegerProfile, coreIntegerProfile_on_palette, actualBodyCenter, calibratedBodyProfile, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

theorem actualBodyIntegerProfile_support (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (output : ℤ) (hout : output < 0 ∨ (Parameters.modulus parameter : ℤ) ≤ output) :
    actualBodyIntegerProfile cutoffScale parameter beta output = 0 := by
  simp only [actualBodyIntegerProfile, coreIntegerProfile_support parameter output hout,
    anchorMean, publicAnchorKernel_integer_support parameter _ output hout, mul_zero, Finset.sum_const_zero, sub_zero]

/-- The actual calibrated profile variation is an interval-edge variation;
no Gaussian or body translation regularity is assumed. -/
theorem actualBodyCenter_translation_l1 (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (hn : ∀ color, 0 ≤ actualPrimary cutoffScale parameter beta color)
    (hm : ∑ color, actualPrimary cutoffScale parameter beta color = 1)
    (hdelta : 0 ≤ bodyCompensation parameter cutoffScale) (shift : ℤ) :
    (∑ output, |integerShiftProfile parameter (actualBodyCenter cutoffScale parameter beta) shift output -
      actualBodyCenter cutoffScale parameter beta output|) ≤
      (1 + bodyCompensation parameter cutoffScale) * (2 * (shift.natAbs : ℝ) / Parameters.safeSize parameter) +
        bodyCompensation parameter cutoffScale * (2 * (shift.natAbs : ℝ) / Parameters.anchorWidth parameter) := by
  have heq : actualBodyCenter cutoffScale parameter beta =
      fun color => actualBodyIntegerProfile cutoffScale parameter beta color.val :=
    funext fun color => (actualBodyIntegerProfile_on_palette cutoffScale parameter beta color).symm
  have hpoint (output : Fin (Parameters.modulus parameter)) :
      |integerShiftProfile parameter (actualBodyCenter cutoffScale parameter beta) shift output -
        actualBodyCenter cutoffScale parameter beta output| ≤
      (1 + bodyCompensation parameter cutoffScale) *
        |coreIntegerProfile parameter ((output.val : ℤ) - shift) - coreIntegerProfile parameter output.val| +
      bodyCompensation parameter cutoffScale *
        |anchorMean (Parameters.modulus parameter) (Parameters.anchorWidth parameter) (actualPrimary cutoffScale parameter beta) ((output.val : ℤ) - shift) -
          anchorMean (Parameters.modulus parameter) (Parameters.anchorWidth parameter) (actualPrimary cutoffScale parameter beta) output.val| := by
    rw [heq, integerShiftProfile_function parameter _ (actualBodyIntegerProfile_support cutoffScale parameter beta)]
    dsimp only [actualBodyIntegerProfile]
    have hid (a b c d e : ℝ) : (1 + e) * a - e * b - ((1 + e) * c - e * d) =
        (1 + e) * (a - c) - e * (b - d) := by ring
    rw [hid]
    exact (abs_sub _ _).trans_eq (by rw [abs_mul, abs_mul, abs_of_nonneg hdelta, abs_of_nonneg (by linarith : 0 ≤ 1 + bodyCompensation parameter cutoffScale)])
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun output _ => hpoint output)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hh
  have hc := interval_palette_translation_l1_le parameter (Parameters.safeMargin parameter) shift (Parameters.safeSize parameter)
  have ha := anchorMean_translation_l1 parameter (actualPrimary cutoffScale parameter beta) hn hm shift
  exact hh.trans (add_le_add (mul_le_mul_of_nonneg_left hc (by linarith)) (mul_le_mul_of_nonneg_left ha hdelta))

end
end AFT.V7Calibration
