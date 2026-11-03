import AFT.ActualPairedLift
import AFT.PrimaryLawLower

/-! # Constant Hilbert cost of the actual compensated primary lift -/

namespace AFT.V7Calibration
open GaussianSource Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The calibrated anchor mean removes the apparent width-dependent loss
in the paired score. This estimate uses the actual primary and safe body. -/
theorem actual_paired_lift_square_sharp_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
      ∀ profile : Fin (Parameters.modulus parameter) → ℝ, (∑ color, profile color) = 0 →
      (∑ color, ∑ center,
        (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight color *
        (actualBodyLaw cutoffScale parameter (beta parameter)).weight center *
        pairedLift (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight
          (actualBodyLaw cutoffScale parameter (beta parameter)).weight
          (fun color position => publicAnchorKernel (Parameters.modulus parameter)
            (Parameters.anchorWidth parameter) color position.val)
          (v7Activation cutoffScale parameter) profile color center ^ 2) ≤
      773 * profileSquareNorm (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight profile := by
  filter_upwards [actual_reference_laws_eventually cutoffScale hscale beta hbeta,
    actual_primary_probability_eventually cutoffScale hscale beta hbeta,
    actual_body_center_probability_eventually cutoffScale hscale beta hbeta,
    actual_primary_anchor_bound_eventually cutoffScale hscale beta hbeta, eventually_ge_atTop 2]
    with parameter hl hp hb hmean hparameter profile hcanonical
  let anchor := fun color position : Fin (Parameters.modulus parameter) =>
    publicAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color position.val
  let primary := actualPrimaryLaw cutoffScale parameter (beta parameter)
  let body := actualBodyLaw cutoffScale parameter (beta parameter)
  let a := v7Activation cutoffScale parameter
  have ha : 0 < a := activation_positive _ _ _ _ (legFeatureCount_positive cutoffScale parameter hscale (by omega))
  have ha1 : a ≤ 1 := activation_le_one _ _ _ _
  have hq : (0 : ℝ) < Parameters.modulus parameter := Nat.cast_pos.mpr (Parameters.modulus_prime parameter).pos
  have hp0 (color) : 0 < primary.weight color := by rw [show primary.weight = _ from hl.1]; exact hp.1 color
  have hcompare (center : Fin (Parameters.modulus parameter)) :
      applyAnchor anchor primary.weight center ≤ (772 / a) * body.weight center := by
    by_cases hc : center ∈ safePalette parameter
    · have hbody : 1 / (2 * (Parameters.modulus parameter : ℝ)) ≤ body.weight center := by
        change _ ≤ (actualBodyLaw cutoffScale parameter (beta parameter)).weight center
        rw [hl.2.1]
        have hh := (div_le_div_of_nonneg_right ((actualCoreLaw_bounds parameter).2 center hc) (by norm_num : (0 : ℝ) ≤ 2)).trans (hb.2.1 center).1
        convert hh using 1
        ring
      have hanchor : a * applyAnchor anchor primary.weight center ≤ 386 / Parameters.modulus parameter := by
        change a * applyAnchor anchor (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight center ≤ _
        rw [hl.1]
        simpa only [a, anchor, applyAnchor, anchorMean, mul_comm] using hmean center.val
      have hh : a * applyAnchor anchor primary.weight center ≤ 772 * body.weight center :=
        hanchor.trans ((mul_le_mul_of_nonneg_left hbody (by norm_num : (0 : ℝ) ≤ 772)).trans' (by ring_nf; exact le_rfl))
      have ht : applyAnchor anchor primary.weight center ≤ (772 * body.weight center) / a :=
        (le_div_iff₀ ha).mpr (by simpa only [mul_comm] using hh)
      exact ht.trans_eq (by ring)
    · have hh : applyAnchor anchor primary.weight center = 0 := by
        unfold applyAnchor
        apply Finset.sum_eq_zero
        intro color _
        change publicAnchorKernel _ _ color center.val * _ = 0
        rw [(actual_anchor_safe_mass parameter color).2 center hc, zero_mul]
      rw [hh]
      exact mul_nonneg (by positivity) (body.nonneg center)
  have he := applyAnchor_profileSquareNorm_le_supported primary.weight body.weight anchor profile
    (772 / a) (by positivity) hp0 body.nonneg
    (fun color position => publicAnchorKernel_nonneg _ _ _ _) (fun color => (actual_anchor_safe_mass parameter color).1) hcompare
  rw [pairedLift_square _ _ _ _ _ (fun color => (hp0 color).ne') primary.sum_one body.sum_one hcanonical]
  change profileSquareNorm primary.weight profile + a ^ 2 * profileSquareNorm body.weight (applyAnchor anchor profile) ≤ _
  have hn := profileSquareNorm_nonneg primary.weight profile primary.nonneg
  calc
    _ ≤ profileSquareNorm primary.weight profile + a ^ 2 * ((772 / a) * profileSquareNorm primary.weight profile) := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left he (sq_nonneg a))
    _ = (1 + 772 * a) * profileSquareNorm primary.weight profile := by field_simp
    _ ≤ 773 * profileSquareNorm primary.weight profile := mul_le_mul_of_nonneg_right (by linarith) hn

end
end AFT.V7Calibration
