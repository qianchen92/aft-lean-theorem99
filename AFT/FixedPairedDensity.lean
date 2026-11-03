import AFT.FixedPairedKernel
import AFT.ActualPairedLift
import AFT.PrimarySup
import AFT.V7ReferenceLower

/-! # A genuine density ceiling for the physical paired four-output kernel -/

namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance fixedDensityFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
attribute [local instance] actualModulusNeZero

theorem fixedPairedKernel_average_factor (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark)
    (attachedRoot compensatorRoot queue : ℤ) (word : Fin 4 → Fin (Parameters.modulus parameter)) :
    (∑ input, ((actualPrimaryLaw cutoffScale parameter beta).prod (actualBodyLaw cutoffScale parameter beta)).weight input *
      fixedPairedKernel cutoffScale parameter beta charts attachedRoot compensatorRoot queue input word) =
    (∑ mark, (actualPrimaryLaw cutoffScale parameter beta).weight mark *
      publicChartRaw cutoffScale parameter mark (charts mark)
        (fun source => (actualShiftedBodyLaw cutoffScale parameter beta (attachedRoot + source + queue)).weight (word 2)) (word 0) (word 1)) *
      integerShiftProfile parameter (actualBodyLaw cutoffScale parameter beta).weight compensatorRoot (word 3) := by
  simp only [Fintype.sum_prod_type, FiniteDist.prod_weight, fixedPairedKernel, integerShiftProfile]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro mark _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro center _
  split_ifs <;> ring

/-- The primary-dependent chart sign remains inside its exact law. The
ceiling uses the real calibrated primary mass, not a fictitious fair sign. -/
theorem fixedPairedKernel_height_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
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
    (4 / (Parameters.modulus parameter : ℝ)) ^ 2 *
      (4 / ((Parameters.modulus parameter : ℝ) * Parameters.anchorWidth parameter) +
        v7Activation cutoffScale parameter * (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight (word 0) / Parameters.anchorWidth parameter) := by
  filter_upwards [actual_shifted_body_law_eventually cutoffScale hscale beta hbeta,
    actual_inactive_pair_bounds_eventually cutoffScale hscale,
    actual_body_center_probability_eventually cutoffScale hscale beta hbeta,
    actual_reference_laws_eventually cutoffScale hscale beta hbeta] with parameter hs hi hb hl charts hc ar cr queue hr hq word
  have hmod : (0 : ℝ) < Parameters.modulus parameter := Nat.cast_pos.mpr (Parameters.modulus_prime parameter).pos
  have hbody (color) : (actualBodyLaw cutoffScale parameter (beta parameter)).weight color ≤ 4 / (Parameters.modulus parameter : ℝ) := by
    rw [hl.2.1]
    exact (hb.2.1 color).2.trans ((mul_le_mul_of_nonneg_left ((actualCoreLaw_bounds parameter).1 color) (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring))
  have hcomp := integerShiftProfile_bound parameter (actualBodyLaw cutoffScale parameter (beta parameter)).weight
    (4 / (Parameters.modulus parameter : ℝ)) (by positivity) hbody cr (word 3)
  have hheight := publicChartRaw_primary_height cutoffScale parameter
    (actualPrimaryLaw cutoffScale parameter (beta parameter)) charts hc (fun source => (hi source).2.2) (word 0) (word 1)
  have hfirst : (∑ mark, (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight mark *
      publicChartRaw cutoffScale parameter mark (charts mark)
        (fun source => (actualShiftedBodyLaw cutoffScale parameter (beta parameter) (ar + source + queue)).weight (word 2)) (word 0) (word 1)) ≤
      (4 / (Parameters.modulus parameter : ℝ)) *
        (4 / ((Parameters.modulus parameter : ℝ) * Parameters.anchorWidth parameter) +
          v7Activation cutoffScale parameter * (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight (word 0) / Parameters.anchorWidth parameter) := by
    calc
      _ ≤ ∑ mark, (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight mark *
        ((4 / (Parameters.modulus parameter : ℝ)) * publicChartRaw cutoffScale parameter mark (charts mark) (fun _ => 1) (word 0) (word 1)) := by
        apply Finset.sum_le_sum
        intro mark _
        apply mul_le_mul_of_nonneg_left _ (FiniteDist.nonneg _ _)
        exact publicChartRaw_attached_le _ _ _ _ _ _ (fun source =>
          (hs _ (actualBodyBranch_shift_bound cutoffScale parameter ar queue hr hq (.inr source))).2 (word 2)) _ _
      _ = (4 / (Parameters.modulus parameter : ℝ)) * ∑ mark,
          (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight mark *
            publicChartRaw cutoffScale parameter mark (charts mark) (fun _ => 1) (word 0) (word 1) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro mark _
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hheight (by positivity)
  rw [fixedPairedKernel_average_factor]
  have hn := integerShiftProfile_nonneg parameter (actualBodyLaw cutoffScale parameter (beta parameter)).weight
    (actualBodyLaw cutoffScale parameter (beta parameter)).nonneg cr (word 3)
  have hact : 0 ≤ v7Activation cutoffScale parameter := by
    unfold v7Activation GaussianSource.activation
    exact mul_nonneg (by positivity) (FiniteDist.nonneg _ _)
  have hp := (actualPrimaryLaw cutoffScale parameter (beta parameter)).nonneg (word 0)
  exact (mul_le_mul hfirst hcomp hn (by positivity)).trans_eq (by ring)

/-- Every actual conditional four-output average has a polynomial density
ceiling against the true output reference. All palette powers cancel here. -/
theorem fixedPairedKernel_density_power_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
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
    (5120 * (parameter : ℝ) ^ 38) *
      ∏ slot : Fin 4, (actualReferenceLaw cutoffScale parameter (beta parameter)).weight (word slot) := by
  filter_upwards [fixedPairedKernel_height_eventually cutoffScale hscale beta hbeta,
    actual_primary_upper_eventually cutoffScale hscale beta hbeta,
    actual_reference_lower_eventually cutoffScale hscale beta hbeta,
    actual_reference_laws_eventually cutoffScale hscale beta hbeta, eventually_ge_atTop 2]
    with parameter hh hp hr hl hparameter charts hc ar cr queue har hqueue word
  let x : ℝ := parameter
  let q : ℝ := Parameters.modulus parameter
  let A : ℝ := Parameters.anchorWidth parameter
  let a := v7Activation cutoffScale parameter
  have hx : 0 < x := by dsimp [x]; exact_mod_cast (by omega : 0 < parameter)
  have hx1 : 1 ≤ x := by dsimp [x]; exact_mod_cast (by omega : 1 ≤ parameter)
  have hq : 0 < q := Nat.cast_pos.mpr (Parameters.modulus_prime parameter).pos
  have hA : A = x ^ 32 := by simp only [A, x, Parameters.anchorWidth, Parameters.security_eq parameter hparameter, Nat.cast_pow]
  have ha : 0 < a := activation_positive _ _ _ _ (legFeatureCount_positive cutoffScale parameter hscale (by omega))
  have hqbound : q ≤ 2 * x ^ 40 := by
    dsimp [q, x]
    exact_mod_cast (show Parameters.modulus parameter ≤ 2 * parameter ^ 40 by
      simpa only [Parameters.security_eq parameter hparameter] using (Parameters.modulus_bounds parameter).2)
  have hap : a * (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight (word 0) ≤ 3 / x ^ 10 := by
    rw [hl.1]
    have ht := mul_le_mul_of_nonneg_left (hp (word 0)) ha.le
    exact ht.trans_eq (by change a * (3 / (a * x ^ 10)) = 3 / x ^ 10; field_simp)
  have hraw := hh charts hc ar cr queue har hqueue word
  have hsmall : (4 / q) ^ 2 * (4 / (q * A) + a * (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight (word 0) / A) ≤
      (4 / q) ^ 2 * (4 / (q * A) + 3 / (x ^ 10 * A)) := by
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    apply add_le_add le_rfl
    exact (div_le_div_of_nonneg_right hap (by rw [hA]; positivity)).trans_eq (by ring)
  have hratio1 : q / A ≤ 2 * x ^ 8 := by
    rw [hA]
    calc
      _ ≤ (2 * x ^ 40) / x ^ 32 := div_le_div_of_nonneg_right hqbound (by positivity)
      _ = _ := by field_simp
  have hratio2 : q ^ 2 / (x ^ 10 * A) ≤ 4 * x ^ 38 := by
    rw [hA]
    calc
      _ ≤ (2 * x ^ 40) ^ 2 / (x ^ 10 * x ^ 32) := by gcongr
      _ = _ := by field_simp; ring
  have hpow : x ^ 8 ≤ x ^ 38 := pow_le_pow_right₀ hx1 (by norm_num)
  have hnumeric : (4 / q) ^ 2 * (4 / (q * A) + 3 / (x ^ 10 * A)) ≤
      (5120 * x ^ 38) * (1 / (2 * q)) ^ 4 := by
    have ht : 1024 * (q / A) + 768 * (q ^ 2 / (x ^ 10 * A)) ≤ 5120 * x ^ 38 := by nlinarith
    have hm := mul_le_mul_of_nonneg_right ht (show 0 ≤ (1 / (2 * q)) ^ 4 by positivity)
    apply le_trans _ hm
    apply le_of_eq
    rw [hA]
    field_simp
    ring
  have href : (1 / (2 * q)) ^ 4 ≤ ∏ slot : Fin 4,
      (actualReferenceLaw cutoffScale parameter (beta parameter)).weight (word slot) := by
    calc
      _ = ∏ _slot : Fin 4, (1 / (2 * q)) := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => by positivity) (fun slot _ => by rw [hl.2.2]; exact hr (word slot))
  exact ((hraw.trans hsmall).trans hnumeric).trans
    (mul_le_mul_of_nonneg_left href (by positivity))

end
end AFT.V7Calibration
