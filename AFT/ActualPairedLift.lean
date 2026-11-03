import AFT.PairedScoreOutput
import AFT.AnchorSeedBounds

/-! # The real paired input lift on its safe probability support -/

namespace AFT

open scoped BigOperators Classical
noncomputable section

/-- Anchor contraction remains valid when the body law is zero outside
its actual safe support. -/
theorem applyAnchor_profileSquareNorm_le_supported {ι κ : Type*} [Fintype ι] [Fintype κ]
    (primary : ι → ℝ) (body : κ → ℝ) (anchor : ι → κ → ℝ)
    (profile : ι → ℝ) (comparison : ℝ) (hcomp : 0 ≤ comparison)
    (hp : ∀ color, 0 < primary color) (hb : ∀ center, 0 ≤ body center)
    (ha : ∀ color center, 0 ≤ anchor color center)
    (hamass : ∀ color, ∑ center, anchor color center = 1)
    (hcompare : ∀ center, applyAnchor anchor primary center ≤ comparison * body center) :
    profileSquareNorm body (applyAnchor anchor profile) ≤ comparison * profileSquareNorm primary profile := by
  calc
    _ ≤ ∑ center, comparison * ∑ color, anchor color center * (profile color ^ 2 / primary color) := by
      apply Finset.sum_le_sum
      intro center _
      have hn : 0 ≤ ∑ color, anchor color center * (profile color ^ 2 / primary color) :=
        Finset.sum_nonneg fun color _ => mul_nonneg (ha color center) (div_nonneg (sq_nonneg _) (hp color).le)
      by_cases hz : body center = 0
      · simp only [hz, div_zero]
        exact mul_nonneg hcomp hn
      · apply (div_le_iff₀ (lt_of_le_of_ne (hb center) (Ne.symm hz))).mpr
        have hh := (applyAnchor_square_le primary anchor profile hp ha center).trans
          (mul_le_mul_of_nonneg_right (hcompare center) hn)
        exact hh.trans_eq (by ring)
    _ = _ := by
      simp only [← Finset.mul_sum]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul, hamass, one_mul]
      rfl

namespace V7Calibration

open GaussianSource Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Concrete paired lift bound for the genuine calibrated p and safe body
law. The explicit factor is at most a fixed polynomial of degree eight. -/
theorem actual_paired_lift_square_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
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
      (1 + v7Activation cutoffScale parameter ^ 2 *
        (2 * Parameters.modulus parameter / (Parameters.anchorWidth parameter : ℝ))) *
        profileSquareNorm (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight profile := by
  filter_upwards [actual_reference_laws_eventually cutoffScale hscale beta hbeta,
    actual_primary_probability_eventually cutoffScale hscale beta hbeta,
    actual_body_center_probability_eventually cutoffScale hscale beta hbeta] with parameter hl hp hb profile hcanonical
  have hp0 (color) : 0 < (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight color := by
    rw [hl.1]; exact hp.1 color
  let anchor := fun color position : Fin (Parameters.modulus parameter) =>
    publicAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color position.val
  have hA : (0 : ℝ) < Parameters.anchorWidth parameter := by
    unfold Parameters.anchorWidth
    have := Parameters.security_ge_two parameter
    positivity
  have hq : (0 : ℝ) < Parameters.modulus parameter := Nat.cast_pos.mpr (Parameters.modulus_prime parameter).pos
  have hcompare (center : Fin (Parameters.modulus parameter)) :
      applyAnchor anchor (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight center ≤
        (2 * Parameters.modulus parameter / (Parameters.anchorWidth parameter : ℝ)) *
          (actualBodyLaw cutoffScale parameter (beta parameter)).weight center := by
    by_cases hc : center ∈ safePalette parameter
    · have hbody : 1 / (2 * (Parameters.modulus parameter : ℝ)) ≤
          (actualBodyLaw cutoffScale parameter (beta parameter)).weight center := by
        rw [hl.2.1]
        have hh := (div_le_div_of_nonneg_right ((actualCoreLaw_bounds parameter).2 center hc) (by norm_num : (0 : ℝ) ≤ 2)).trans (hb.2.1 center).1
        convert hh using 1
        ring
      have ha := applyAnchor_primary_upper (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight anchor
        (1 / (Parameters.anchorWidth parameter : ℝ)) (actualPrimaryLaw cutoffScale parameter (beta parameter)).nonneg
        (actualPrimaryLaw cutoffScale parameter (beta parameter)).sum_one
        (fun color position => by simpa only [anchor, one_div] using publicAnchorKernel_le (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color position.val) center
      apply ha.trans
      have hh := mul_le_mul_of_nonneg_left hbody (by positivity : 0 ≤ 2 * (Parameters.modulus parameter : ℝ) / Parameters.anchorWidth parameter)
      convert hh using 1
      field_simp
    · have ha : applyAnchor anchor (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight center = 0 := by
        unfold applyAnchor
        apply Finset.sum_eq_zero
        intro color _
        change publicAnchorKernel _ _ color center.val * _ = 0
        rw [(actual_anchor_safe_mass parameter color).2 center hc, zero_mul]
      rw [ha]
      exact mul_nonneg (by positivity) ((actualBodyLaw cutoffScale parameter (beta parameter)).nonneg center)
  have hanchor := applyAnchor_profileSquareNorm_le_supported
    (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight
    (actualBodyLaw cutoffScale parameter (beta parameter)).weight anchor profile
    (2 * Parameters.modulus parameter / (Parameters.anchorWidth parameter : ℝ)) (by positivity) hp0
    (actualBodyLaw cutoffScale parameter (beta parameter)).nonneg
    (fun color position => publicAnchorKernel_nonneg _ _ _ _) (fun color => (actual_anchor_safe_mass parameter color).1) hcompare
  rw [pairedLift_square _ _ _ _ _ (fun color => (hp0 color).ne')
    (actualPrimaryLaw cutoffScale parameter (beta parameter)).sum_one
    (actualBodyLaw cutoffScale parameter (beta parameter)).sum_one hcanonical]
  change _ ≤ (1 + _ * _) * _
  have hh := mul_le_mul_of_nonneg_left hanchor (sq_nonneg (v7Activation cutoffScale parameter))
  nlinarith only [hh]

end V7Calibration
end
end AFT
