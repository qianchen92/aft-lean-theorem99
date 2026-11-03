import AFT.FixedPairedDensity
import AFT.PrimaryLawLower

/-! # Sharp raw numerator density on the actual calibrated primary palette -/

namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance fixedPrimaryDensityFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
attribute [local instance] actualModulusNeZero

/-- The marked first coordinate keeps its calibrated primary probability.
Consequently it cancels against that output reference, giving only q/W. -/
theorem pairedHeight_primary_comparison (q width activation : ℝ) (p : Fin 4 → ℝ)
    (hq : 0 < q) (hw : 0 < width) (ha0 : 0 ≤ activation) (ha1 : activation ≤ 1)
    (hp : ∀ slot, 1 / (4 * q) ≤ p slot) :
    (4 / q) ^ 2 * (4 / (q * width) + activation * p 0 / width) ≤
      (17408 * q / width) * ∏ slot, p slot := by
  have hp0 (slot) : 0 ≤ p slot := (by positivity : (0 : ℝ) ≤ 1 / (4 * q)).trans (hp slot)
  have hp00 := hp0 0
  have hp01 := hp0 1
  have hp02 := hp0 2
  have hp03 := hp0 3
  have hfirst : 4 / (q * width) ≤ (64 * q / width) * (p 0 * p 1) := by
    have hh := mul_le_mul (hp 0) (hp 1) (by positivity : (0 : ℝ) ≤ 1 / (4 * q)) (hp0 0)
    have ht := mul_le_mul_of_nonneg_left hh (show 0 ≤ 64 * q / width by positivity)
    apply le_trans _ ht
    apply le_of_eq
    field_simp
    ring
  have hmark : activation * p 0 / width ≤ (4 * q / width) * (p 0 * p 1) := by
    calc
      _ ≤ p 0 / width := div_le_div_of_nonneg_right
        ((mul_le_mul_of_nonneg_right ha1 (hp0 0)).trans_eq (one_mul _)) hw.le
      _ ≤ (4 * q / width) * (p 0 * p 1) := by
        have hh := mul_le_mul_of_nonneg_left (hp 1) (show 0 ≤ (4 * q / width) * p 0 by positivity)
        apply le_trans _ (hh.trans_eq (by ring))
        apply le_of_eq
        field_simp
  have hpair : 4 / (q * width) + activation * p 0 / width ≤ (68 * q / width) * (p 0 * p 1) :=
    (add_le_add hfirst hmark).trans_eq (by ring)
  have hbody : (4 / q) ^ 2 ≤ 256 * (p 2 * p 3) := by
    have hh := mul_le_mul (hp 2) (hp 3) (by positivity : (0 : ℝ) ≤ 1 / (4 * q)) (hp0 2)
    have ht := mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 256)
    apply le_trans _ ht
    apply le_of_eq
    field_simp
    ring
  have hh := mul_le_mul hbody hpair (by positivity : 0 ≤ 4 / (q * width) + activation * p 0 / width) (by positivity : 0 ≤ 256 * (p 2 * p 3))
  apply hh.trans_eq
  rw [Fin.prod_univ_four]
  ring

/-- The actual conditional kernel has sharp polynomial density against
four copies of the calibrated primary law, uniformly in its roots. -/
theorem fixedPairedKernel_primary_density_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark,
    (∀ mark first second, publicChartRaw cutoffScale parameter mark (charts mark) (fun _ => 1) first second =
      conditionalJointOutput cutoffScale parameter mark (fun _ => 1) first second) →
    ∀ attachedRoot compensatorRoot queue : ℤ,
      |attachedRoot| ≤ (v7RootCutoff parameter : ℤ) → |queue| ≤ (queueCutoff parameter : ℤ) →
    ∀ word : Fin 4 → Fin (Parameters.modulus parameter),
    (∑ input, ((actualPrimaryLaw cutoffScale parameter (beta parameter)).prod (actualBodyLaw cutoffScale parameter (beta parameter))).weight input *
      fixedPairedKernel cutoffScale parameter (beta parameter) charts attachedRoot compensatorRoot queue input word) ≤
    (34816 * (parameter : ℝ) ^ 8) *
      ∏ slot : Fin 4, (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight (word slot) := by
  filter_upwards [fixedPairedKernel_height_eventually cutoffScale hscale beta hbeta,
    actual_primary_law_quarter_lower_eventually cutoffScale hscale beta hbeta, eventually_ge_atTop 2]
    with parameter hh hp hparameter charts hc ar cr queue har hqueue word
  have hq : (0 : ℝ) < Parameters.modulus parameter := Nat.cast_pos.mpr (Parameters.modulus_prime parameter).pos
  have hx : (0 : ℝ) < parameter := by exact_mod_cast (by omega : 0 < parameter)
  have hA : (Parameters.anchorWidth parameter : ℝ) = (parameter : ℝ) ^ 32 := by
    simp only [Parameters.anchorWidth, Parameters.security_eq parameter hparameter, Nat.cast_pow]
  have hqbound : (Parameters.modulus parameter : ℝ) ≤ 2 * (parameter : ℝ) ^ 40 := by
    exact_mod_cast (show Parameters.modulus parameter ≤ 2 * parameter ^ 40 by
      simpa only [Parameters.security_eq parameter hparameter] using (Parameters.modulus_bounds parameter).2)
  have ha0 : 0 ≤ v7Activation cutoffScale parameter := by
    unfold v7Activation GaussianSource.activation
    exact mul_nonneg (by positivity) (FiniteDist.nonneg _ _)
  have hcompare := pairedHeight_primary_comparison (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
    (v7Activation cutoffScale parameter) (fun slot => (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight (word slot))
    hq (by rw [hA]; positivity) ha0 (activation_le_one _ _ _ _) (fun slot => hp (word slot))
  have hnumeric : 17408 * (Parameters.modulus parameter : ℝ) / Parameters.anchorWidth parameter ≤ 34816 * (parameter : ℝ) ^ 8 := by
    rw [hA]
    calc
      _ ≤ 17408 * (2 * (parameter : ℝ) ^ 40) / (parameter : ℝ) ^ 32 := by gcongr
      _ = _ := by field_simp; ring
  exact ((hh charts hc ar cr queue har hqueue word).trans hcompare).trans
    (mul_le_mul_of_nonneg_right hnumeric (Finset.prod_nonneg fun slot _ => FiniteDist.nonneg _ _))

end
end AFT.V7Calibration
