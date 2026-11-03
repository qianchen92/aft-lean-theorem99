import AFT.PrimaryL1
import AFT.V7PrimaryInverse

/-! # Exact public anchor means and their calibrated supremum bound -/

namespace AFT

open Filter
open scoped BigOperators Classical Topology

noncomputable section

/-- An interval law summed over an injective palette has mass at most one. -/
theorem intervalAnchorLaw_palette_mass_le_one (modulus width : ℕ) (start : ℤ) :
    (∑ color : Fin modulus, intervalAnchorLaw start width color.val) ≤ 1 := by
  let support : Finset (Fin modulus) := Finset.univ.filter fun c => (c.val : ℤ) ∈ anchorInterval start width
  have hc : support.card ≤ width := by
    have hh := Finset.card_le_card_of_injOn (s := support) (t := anchorInterval start width)
      (fun c : Fin modulus => (c.val : ℤ))
      (by intro c hc; change (c.val : ℤ) ∈ anchorInterval start width; exact (Finset.mem_filter.mp (show c ∈ support from hc)).2)
      (by intro a _ b _ h; change (a.val : ℤ) = b.val at h; apply Fin.ext; exact_mod_cast h)
    simpa only [anchorInterval_card] using hh
  have he : (∑ color : Fin modulus, intervalAnchorLaw start width color.val) = (support.card : ℝ) * (width : ℝ)⁻¹ := by
    simp only [intervalAnchorLaw, ← Finset.sum_filter]
    simp [support]
  rw [he]
  by_cases hw : width = 0
  · simp [hw]
  · calc
      _ ≤ (width : ℝ) * (width : ℝ)⁻¹ := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (by positivity)
      _ = 1 := mul_inv_cancel₀ (by exact_mod_cast hw)

theorem intervalAnchorLaw_reflected_start (offset color output : ℤ) (width : ℕ) :
    intervalAnchorLaw (offset - color) width output = intervalAnchorLaw (offset - output) width color := by
  have hh : output ∈ anchorInterval (offset - color) width ↔ color ∈ anchorInterval (offset - output) width := by
    simp only [anchorInterval, Finset.mem_Ico]
    omega
  simp only [intervalAnchorLaw, hh]

namespace V7Calibration

/-- The true fair midpoint anchor kernel, with both non-midpoint directions. -/
def publicAnchorKernel (modulus width : ℕ) (color : Fin modulus) (output : ℤ) : ℝ :=
  (intervalAnchorLaw (publicAnchorStart modulus width color true) width output +
    intervalAnchorLaw (publicAnchorStart modulus width color false) width output) / 2

def anchorMean (modulus width : ℕ) (profile : Fin modulus → ℝ) (output : ℤ) : ℝ :=
  ∑ color, profile color * publicAnchorKernel modulus width color output

theorem publicAnchorKernel_nonneg (modulus width : ℕ) (color : Fin modulus) (output : ℤ) :
    0 ≤ publicAnchorKernel modulus width color output := by
  unfold publicAnchorKernel
  exact div_nonneg (add_nonneg (intervalAnchorLaw_nonneg _ _ _) (intervalAnchorLaw_nonneg _ _ _)) (by norm_num)

theorem publicAnchorKernel_le (modulus width : ℕ) (color : Fin modulus) (output : ℤ) :
    publicAnchorKernel modulus width color output ≤ (width : ℝ)⁻¹ := by
  unfold publicAnchorKernel
  linarith [intervalAnchorLaw_bound (publicAnchorStart modulus width color true) output width,
    intervalAnchorLaw_bound (publicAnchorStart modulus width color false) output width]

theorem publicAnchorKernel_column_bound (modulus width : ℕ) (output : ℤ) :
    (∑ color, publicAnchorKernel modulus width color output) ≤ 2 := by
  have hpoint (color : Fin modulus) : publicAnchorKernel modulus width color output ≤
      intervalAnchorLaw ((modulus : ℤ) - 2 * width - output) width color.val +
        intervalAnchorLaw ((modulus : ℤ) - 1 + width - output) width color.val := by
    have hplus : intervalAnchorLaw ((modulus : ℤ) - color.val - 2 * width) width output =
        intervalAnchorLaw ((modulus : ℤ) - 2 * width - output) width color.val := by
      rw [show (modulus : ℤ) - color.val - 2 * width = (modulus : ℤ) - 2 * width - color.val by ring]
      exact intervalAnchorLaw_reflected_start _ _ _ _
    have hminus : intervalAnchorLaw ((modulus : ℤ) - 1 - color.val + width) width output =
        intervalAnchorLaw ((modulus : ℤ) - 1 + width - output) width color.val := by
      rw [show (modulus : ℤ) - 1 - color.val + width = (modulus : ℤ) - 1 + width - color.val by ring]
      exact intervalAnchorLaw_reflected_start _ _ _ _
    unfold publicAnchorKernel publicAnchorStart
    split_ifs <;> simp only [hplus, hminus] <;>
      linarith [intervalAnchorLaw_nonneg ((modulus : ℤ) - 2 * width - output) color.val width,
        intervalAnchorLaw_nonneg ((modulus : ℤ) - 1 + width - output) color.val width]
  calc
    _ ≤ ∑ color : Fin modulus, (intervalAnchorLaw ((modulus : ℤ) - 2 * width - output) width color.val +
        intervalAnchorLaw ((modulus : ℤ) - 1 + width - output) width color.val) := Finset.sum_le_sum fun c _ => hpoint c
    _ ≤ 2 := by rw [Finset.sum_add_distrib]; linarith [intervalAnchorLaw_palette_mass_le_one modulus width ((modulus : ℤ) - 2 * width - output),
      intervalAnchorLaw_palette_mass_le_one modulus width ((modulus : ℤ) - 1 + width - output)]

theorem anchorMean_uniform_bound (modulus width : ℕ) (output : ℤ) :
    anchorMean modulus width (fun _ => 1 / (modulus : ℝ)) output ≤ 2 / modulus := by
  unfold anchorMean
  rw [← Finset.mul_sum]
  have hh := mul_le_mul_of_nonneg_left (publicAnchorKernel_column_bound modulus width output)
    (by positivity : 0 ≤ 1 / (modulus : ℝ))
  convert hh using 1; ring

theorem anchorMean_difference_bound (modulus width : ℕ) (first second : Fin modulus → ℝ) (output : ℤ) :
    |anchorMean modulus width first output - anchorMean modulus width second output| ≤
      (∑ color, |first color - second color|) / width := by
  unfold anchorMean
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ color, |(first color - second color) * publicAnchorKernel modulus width color output| := by
      simpa only [sub_mul] using Finset.abs_sum_le_sum_abs
        (fun color => (first color - second color) * publicAnchorKernel modulus width color output) Finset.univ
    _ ≤ ∑ color, |first color - second color| * (width : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro color _
      rw [abs_mul, abs_of_nonneg (publicAnchorKernel_nonneg _ _ _ _)]
      exact mul_le_mul_of_nonneg_left (publicAnchorKernel_le _ _ _ _) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; rfl

/-- The true calibrated anchor mean satisfies the needed uniform bound,
including every color, both signs, and the midpoint coin. -/
theorem actual_primary_anchor_bound_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ output : ℤ,
      GaussianSource.v7Activation cutoffScale parameter * anchorMean (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
        (actualPrimary cutoffScale parameter (beta parameter)) output ≤ 386 / Parameters.modulus parameter := by
  filter_upwards [actual_primary_uniform_l1_eventually cutoffScale hscale beta hbeta, eventually_ge_atTop 2]
    with parameter hL1 hp output
  have hx : (0 : ℝ) < parameter := by exact_mod_cast (by omega : 0 < parameter)
  have hq : (0 : ℝ) < Parameters.modulus parameter := by exact_mod_cast (Parameters.modulus_prime parameter).pos
  have ha : 0 < GaussianSource.v7Activation cutoffScale parameter := GaussianSource.activation_positive _ _ _ _
    (GaussianSource.legFeatureCount_positive cutoffScale parameter hscale (by omega))
  have ha1 : GaussianSource.v7Activation cutoffScale parameter ≤ 1 :=
    (GaussianSource.activation_le_one_hundredth _ _ _ _).trans (by norm_num)
  have hA : (Parameters.anchorWidth parameter : ℝ) = (parameter : ℝ) ^ 32 := by
    simp only [Parameters.anchorWidth, Parameters.security_eq parameter hp, Nat.cast_pow]
  have hq2 : (Parameters.modulus parameter : ℝ) ≤ 2 * (parameter : ℝ) ^ 40 := by
    exact_mod_cast (show Parameters.modulus parameter ≤ 2 * parameter ^ 40 by
      simpa only [Parameters.security_eq parameter hp] using (Parameters.modulus_bounds parameter).2)
  have hh := (le_abs_self _).trans (anchorMean_difference_bound (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
    (actualPrimary cutoffScale parameter (beta parameter)) (fun _ => 1 / (Parameters.modulus parameter : ℝ)) output)
  have hfirst := anchorMean_uniform_bound (Parameters.modulus parameter) (Parameters.anchorWidth parameter) output
  have hL1' := div_le_div_of_nonneg_right hL1.1 (Nat.cast_nonneg (Parameters.anchorWidth parameter))
  have hsum : anchorMean (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
      (actualPrimary cutoffScale parameter (beta parameter)) output ≤
      2 / Parameters.modulus parameter + 192 / (GaussianSource.v7Activation cutoffScale parameter * (parameter : ℝ) ^ 8) /
        Parameters.anchorWidth parameter := by linarith
  calc
    _ ≤ GaussianSource.v7Activation cutoffScale parameter *
        (2 / Parameters.modulus parameter + 192 / (GaussianSource.v7Activation cutoffScale parameter * (parameter : ℝ) ^ 8) /
          Parameters.anchorWidth parameter) := mul_le_mul_of_nonneg_left hsum ha.le
    _ = GaussianSource.v7Activation cutoffScale parameter * (2 / Parameters.modulus parameter) + 192 / (parameter : ℝ) ^ 40 := by
      rw [hA]; field_simp
    _ ≤ 2 / Parameters.modulus parameter + 384 / Parameters.modulus parameter := by
      apply add_le_add
      · simpa only [one_mul] using mul_le_mul_of_nonneg_right ha1 (by positivity : 0 ≤ 2 / (Parameters.modulus parameter : ℝ))
      · exact (div_le_div_iff₀ (by positivity) hq).mpr (by nlinarith)
    _ = _ := by ring

end V7Calibration
end
end AFT
