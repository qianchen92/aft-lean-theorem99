import AFT.AnchorSeedBounds

/-! # Positivity and uniform comparison of the actual reference mean -/

namespace AFT

open Filter
open scoped BigOperators Classical Topology

noncomputable section

theorem uniform_boundary_perturbation_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    (boundary : Finset ι) (change : ℝ)
    (hq : 0 < (Fintype.card ι : ℝ))
    (hsmall : 2 * (boundary.card : ℝ) ≤ Fintype.card ι)
    (hchange : |change| ≤ (boundary.card : ℝ) / Fintype.card ι) :
    (∀ color, 0 ≤ (Fintype.card ι : ℝ)⁻¹ + change *
      (uniformFiniteProfile boundary color - uniformFiniteProfile boundaryᶜ color) ∧
      (Fintype.card ι : ℝ)⁻¹ + change *
      (uniformFiniteProfile boundary color - uniformFiniteProfile boundaryᶜ color) ≤ 2 / Fintype.card ι) ∧
    (∑ color, ((Fintype.card ι : ℝ)⁻¹ + change *
      (uniformFiniteProfile boundary color - uniformFiniteProfile boundaryᶜ color))) = 1 := by
  have hc : (boundary.card : ℝ) + boundaryᶜ.card = Fintype.card ι := by exact_mod_cast boundary.card_add_card_compl
  have hi : (0 : ℝ) < boundaryᶜ.card := by linarith [show (0 : ℝ) ≤ boundary.card from Nat.cast_nonneg _]
  have hchange' := abs_le.mp hchange
  have hdelta (color) : |change * (uniformFiniteProfile boundary color - uniformFiniteProfile boundaryᶜ color)| ≤
      (Fintype.card ι : ℝ)⁻¹ := by
    by_cases hcolor : color ∈ boundary
    · have hb : (0 : ℝ) < boundary.card := by exact_mod_cast Finset.card_pos.mpr ⟨color, hcolor⟩
      simp only [uniformFiniteProfile, Finset.mem_compl, hcolor, not_true_eq_false, if_true, if_false, sub_zero, abs_mul,
        abs_of_nonneg (inv_nonneg.mpr hb.le)]
      have hh := mul_le_mul_of_nonneg_right hchange (inv_nonneg.mpr hb.le)
      exact hh.trans_eq (by field_simp)
    · simp only [uniformFiniteProfile, Finset.mem_compl, hcolor, not_false_eq_true, if_false, if_true, zero_sub,
        abs_mul, abs_neg, abs_of_nonneg (inv_nonneg.mpr hi.le)]
      have hh := mul_le_mul_of_nonneg_right hchange (inv_nonneg.mpr hi.le)
      apply hh.trans
      have hbi : (boundary.card : ℝ) ≤ boundaryᶜ.card := by linarith
      calc
        _ ≤ ((boundaryᶜ.card : ℝ) / Fintype.card ι) * (boundaryᶜ.card : ℝ)⁻¹ := by gcongr
        _ = _ := by field_simp
  refine ⟨?_, ?_⟩
  · intro color
    have hd := abs_le.mp (hdelta color)
    rw [div_eq_mul_inv]
    constructor <;> linarith [hd.1, hd.2]
  · by_cases hb : boundary.Nonempty
    · have hb' : boundaryᶜ.Nonempty := Finset.card_pos.mp (by exact_mod_cast hi)
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
        uniformFiniteProfile_mass boundary hb, uniformFiniteProfile_mass boundaryᶜ hb', sub_self, mul_zero, add_zero,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact mul_inv_cancel₀ (ne_of_gt hq)
    · have hb' := Finset.not_nonempty_iff_eq_empty.mp hb
      have hzero : change = 0 := abs_eq_zero.mp (le_antisymm (by simpa only [hb', Finset.card_empty, Nat.cast_zero, zero_div] using hchange) (abs_nonneg _))
      simp only [hzero, zero_mul, add_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact mul_inv_cancel₀ (ne_of_gt hq)

namespace V7Calibration
open GaussianSource

/-- Typical beta gives a true reference probability bounded by twice
palette uniform; the estimate is for the literal calibrated formula. -/
theorem actual_reference_probability_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
      (∀ color, 0 ≤ actualReferenceMean cutoffScale parameter (beta parameter) color ∧
        actualReferenceMean cutoffScale parameter (beta parameter) color ≤ 2 / (Parameters.modulus parameter : ℝ)) ∧
      (∑ color, actualReferenceMean cutoffScale parameter (beta parameter) color) = 1 := by
  filter_upwards [hbeta, body_support_scales_eventually cutoffScale hscale, eventually_ge_atTop 2]
    with parameter hb hs hp
  have hq : (0 : ℝ) < Parameters.modulus parameter := by exact_mod_cast (Parameters.modulus_prime parameter).pos
  have hm : (0 : ℝ) < Parameters.legs parameter := by
    simp only [Parameters.legs, Parameters.security_eq parameter hp, Nat.cast_pow]; positivity
  have hn : (0 : ℝ) < Parameters.dimension parameter := by
    simp only [Parameters.dimension, Parameters.meanDensity, Parameters.security_eq parameter hp, Nat.cast_mul, Nat.cast_pow]; positivity
  have ha : 0 < v7Activation cutoffScale parameter := activation_positive _ _ _ _
    (legFeatureCount_positive cutoffScale parameter hscale (by omega))
  let boundary := boundaryPalette (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter)
  let scale := (Parameters.legs parameter : ℝ) * v7Activation cutoffScale parameter / Parameters.dimension parameter
  let change := repairedBoundaryMass parameter cutoffScale (beta parameter) (boundaryHalf cutoffScale parameter) -
    v7BaseBoundaryMass cutoffScale parameter (boundaryHalf cutoffScale parameter)
  have hsmall : 2 * (boundary.card : ℝ) ≤ Parameters.modulus parameter := by
    have hmargin := safeMargin_quarter parameter
    have hcard := boundaryPalette_card (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter) hs.2.2.1 (by have hh := hs.2.2.2; omega)
    have hcard' : (boundary.card : ℝ) ≤ 2 * Parameters.safeMargin parameter := by
      have hh : (boundary.card : ℝ) = 2 * boundaryHalf cutoffScale parameter := by exact_mod_cast hcard
      rw [hh]
      exact_mod_cast (show 2 * boundaryHalf cutoffScale parameter ≤ 2 * (Parameters.safeMargin parameter : ℤ) by linarith [hs.2.2.2])
    have hh : (4 : ℝ) * Parameters.safeMargin parameter ≤ Parameters.modulus parameter := by exact_mod_cast hmargin
    linarith
  have hmass := beta_boundary_mass_bounds (Parameters.dimension parameter) (Parameters.legs parameter) (v7Activation cutoffScale parameter)
    (boundary.card / (Parameters.modulus parameter : ℝ)) (beta parameter) hn hm ha (by positivity) hb.1 hb.2
  have hbase : (Parameters.dimension parameter : ℝ) * (boundary.card / (Parameters.modulus parameter : ℝ)) /
      (Parameters.legs parameter * v7Activation cutoffScale parameter) =
      v7BaseBoundaryMass cutoffScale parameter (boundaryHalf cutoffScale parameter) := by unfold v7BaseBoundaryMass; dsimp only [boundary]; ring
  rw [hbase] at hmass
  change v7BaseBoundaryMass cutoffScale parameter (boundaryHalf cutoffScale parameter) / 2 ≤
      repairedBoundaryMass parameter cutoffScale (beta parameter) (boundaryHalf cutoffScale parameter) ∧
    repairedBoundaryMass parameter cutoffScale (beta parameter) (boundaryHalf cutoffScale parameter) ≤
      2 * v7BaseBoundaryMass cutoffScale parameter (boundaryHalf cutoffScale parameter) at hmass
  have hchange : |change| ≤ v7BaseBoundaryMass cutoffScale parameter (boundaryHalf cutoffScale parameter) := by
    have hb0 : 0 ≤ v7BaseBoundaryMass cutoffScale parameter (boundaryHalf cutoffScale parameter) := by unfold v7BaseBoundaryMass; positivity
    dsimp only [change]
    exact abs_le.mpr ⟨by linarith [hmass.1], by linarith [hmass.2]⟩
  have hscale0 : 0 ≤ scale := by dsimp only [scale]; positivity
  have hcoefficient : |scale * change| ≤ boundary.card / (Parameters.modulus parameter : ℝ) := by
    rw [abs_mul, abs_of_nonneg hscale0]
    apply (mul_le_mul_of_nonneg_left hchange hscale0).trans_eq
    dsimp only [scale, v7BaseBoundaryMass, boundary]
    field_simp
  have hh := uniform_boundary_perturbation_bounds boundary (scale * change)
    (by simpa only [Fintype.card_fin] using hq) (by simpa only [Fintype.card_fin] using hsmall)
    (by simpa only [Fintype.card_fin] using hcoefficient)
  have heq (color) : actualReferenceMean cutoffScale parameter (beta parameter) color =
      (Parameters.modulus parameter : ℝ)⁻¹ + (scale * change) *
        (uniformFiniteProfile boundary color - uniformFiniteProfile boundaryᶜ color) := by
    simp only [actualReferenceMean, referenceMean, calibratedReferenceMean, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
      scale, change, boundary, one_div]
    ring
  simpa only [Fintype.card_fin, ← heq] using hh

end V7Calibration
end
end AFT
