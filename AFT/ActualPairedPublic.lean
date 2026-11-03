import AFT.PairedPublicSchur
import AFT.ActualPairedLiftSharp

/-! # Mixed public-score bounds for the actual calibrated primary and body laws -/
namespace AFT.V7Calibration
open GaussianSource Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The actual calibrated anchor/body comparison includes all zero body
atoms, and its constant is independent of lambda and the alphabet. -/
theorem actual_public_anchor_comparison_eventually (C : ℝ) (hC : 1 ≤ C)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,
      (Parameters.legs n : ℝ) / (2 * Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2 * (Parameters.legs n : ℝ) / Parameters.dimension n) :
    ∀ᶠ n in atTop, ∀ center : Fin (Parameters.modulus n),
      v7Activation C n * applyAnchor
        (fun color position => publicAnchorKernel (Parameters.modulus n) (Parameters.anchorWidth n) color position.val)
        (actualPrimaryLaw C n (beta n)).weight center ≤ 772 * (actualBodyLaw C n (beta n)).weight center := by
  filter_upwards [actual_reference_laws_eventually C hC beta hbeta,
    actual_body_center_probability_eventually C hC beta hbeta,
    actual_primary_anchor_bound_eventually C hC beta hbeta]
    with n hl hb hmean center
  by_cases hc : center ∈ safePalette n
  · have hbody : 1 / (2 * (Parameters.modulus n : ℝ)) ≤ (actualBodyLaw C n (beta n)).weight center := by
      rw [hl.2.1]
      have hh := (div_le_div_of_nonneg_right ((actualCoreLaw_bounds n).2 center hc)
        (by norm_num : (0 : ℝ) ≤ 2)).trans (hb.2.1 center).1
      convert hh using 1
      ring
    have hanchor : v7Activation C n * applyAnchor
        (fun color position => publicAnchorKernel (Parameters.modulus n) (Parameters.anchorWidth n) color position.val)
        (actualPrimaryLaw C n (beta n)).weight center ≤ 386 / Parameters.modulus n := by
      rw [hl.1]
      simpa only [applyAnchor, anchorMean, mul_comm] using hmean center.val
    exact hanchor.trans ((mul_le_mul_of_nonneg_left hbody (by norm_num : (0 : ℝ) ≤ 772)).trans_eq' (by ring))
  · have hz : applyAnchor
        (fun color position => publicAnchorKernel (Parameters.modulus n) (Parameters.anchorWidth n) color position.val)
        (actualPrimaryLaw C n (beta n)).weight center = 0 := by
      unfold applyAnchor
      apply Finset.sum_eq_zero
      intro color _
      dsimp only
      rw [(actual_anchor_safe_mass n color).2 center hc, zero_mul]
    rw [hz, mul_zero]
    exact mul_nonneg (by norm_num) ((actualBodyLaw C n (beta n)).nonneg center)

/-- Every actual joint primary score is transferred to the real paired
public variables with a fixed-order constant, retaining every mixed fiber. -/
theorem actual_paired_public_activity_eventually (C : ℝ) (hC : 1 ≤ C)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,
      (Parameters.legs n : ℝ) / (2 * Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2 * (Parameters.legs n : ℝ) / Parameters.dimension n) :
    ∀ᶠ n in atTop, ∀ count : ℕ,
      ∀ rates : Fin count → ℝ, (∀ slot, 0 ≤ rates slot) →
      ∀ kernel : (Fin count → Fin (Parameters.modulus n)) → ℝ,
      MixedKernel.activity rates
        (fun _ => (actualPrimaryLaw C n (beta n)).prod (actualBodyLaw C n (beta n)))
        (TensorChannel.applyLinear count (fun _ => pairedPublicDensity
          (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
          (fun color position => publicAnchorKernel (Parameters.modulus n) (Parameters.anchorWidth n) color position.val)
          (v7Activation C n)) kernel) ≤
        (774 : ℝ)^(2 * count) * MixedKernel.activity rates (fun _ => actualPrimaryLaw C n (beta n)) kernel := by
  filter_upwards [actual_public_anchor_comparison_eventually C hC beta hbeta, eventually_ge_atTop 2]
    with n hcompare hn count rates hrates kernel
  have ha : 0 < v7Activation C n :=
    activation_positive _ _ _ _ (legFeatureCount_positive C n hC (by omega))
  simpa only [show (772 : ℝ) + 2 = 774 by norm_num] using
    pairedPublicDensity_joint_activity_le count (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
      (fun color position => publicAnchorKernel (Parameters.modulus n) (Parameters.anchorWidth n) color position.val)
      (v7Activation C n) 772 ha.le (activation_le_one _ _ _ _) (by norm_num)
      (fun color position => publicAnchorKernel_nonneg _ _ _ _)
      (fun color => (actual_anchor_safe_mass n color).1) hcompare rates hrates kernel
end
end AFT.V7Calibration
