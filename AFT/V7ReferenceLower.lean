import AFT.V7ReferenceLaws

/-! # A strict uniform lower bound for the actual V7 reference -/

namespace AFT

open Filter
open scoped BigOperators Classical Topology

noncomputable section

theorem uniform_boundary_perturbation_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (boundary : Finset ι) (change : ℝ) (hq : 0 < (Fintype.card ι : ℝ))
    (hsmall : 3 * (boundary.card : ℝ) ≤ Fintype.card ι)
    (hlower : -(boundary.card : ℝ) / (2 * Fintype.card ι) ≤ change)
    (hupper : change ≤ (boundary.card : ℝ) / Fintype.card ι) (color : ι) :
    1 / (2 * Fintype.card ι) ≤ (Fintype.card ι : ℝ)⁻¹ + change *
      (uniformFiniteProfile boundary color - uniformFiniteProfile boundaryᶜ color) := by
  have hc : (boundary.card : ℝ) + boundaryᶜ.card = Fintype.card ι :=
    by exact_mod_cast boundary.card_add_card_compl
  have hi : (0 : ℝ) < boundaryᶜ.card := by
    linarith [show (0 : ℝ) ≤ boundary.card from Nat.cast_nonneg _]
  by_cases hcolor : color ∈ boundary
  · have hb : (0 : ℝ) < boundary.card := by exact_mod_cast Finset.card_pos.mpr ⟨color, hcolor⟩
    simp only [uniformFiniteProfile, hcolor, Finset.mem_compl, not_true_eq_false,
      if_true, if_false, sub_zero]
    have hh := mul_le_mul_of_nonneg_right hlower (inv_nonneg.mpr hb.le)
    have heq : (-(boundary.card : ℝ) / (2 * Fintype.card ι)) * (boundary.card : ℝ)⁻¹ =
        -(1 / (2 * Fintype.card ι)) := by field_simp
    rw [heq] at hh
    have hqeq : (Fintype.card ι : ℝ)⁻¹ = 2 * (1 / (2 * Fintype.card ι)) := by field_simp
    linarith
  · simp only [uniformFiniteProfile, hcolor, Finset.mem_compl, not_false_eq_true,
      if_false, if_true, zero_sub, mul_neg]
    have hh := mul_le_mul_of_nonneg_right hupper (inv_nonneg.mpr hi.le)
    have hb : (boundary.card : ℝ) ≤ (boundaryᶜ.card : ℝ) / 2 := by linarith
    have hh' : ((boundary.card : ℝ) / Fintype.card ι) * (boundaryᶜ.card : ℝ)⁻¹ ≤
        1 / (2 * Fintype.card ι) := by
      apply (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hb hq.le) (inv_nonneg.mpr hi.le)).trans_eq
      field_simp
    have hqeq : (Fintype.card ι : ℝ)⁻¹ = 2 * (1 / (2 * Fintype.card ι)) := by field_simp
    linarith

namespace V7Calibration
open GaussianSource

theorem safeMargin_sixth (parameter : ℕ) : 6 * Parameters.safeMargin parameter ≤ Parameters.modulus parameter := by
  have hh : 120 ≤ Parameters.security parameter ^ 38 := by
    have hh := Nat.pow_le_pow_left (Parameters.security_ge_two parameter) 38
    omega
  have hmul := Nat.mul_le_mul_right (Parameters.security parameter ^ 2) hh
  have hm : 6 * Parameters.safeMargin parameter ≤ Parameters.security parameter ^ 40 := by
    convert hmul using 1 <;> simp [Parameters.safeMargin, ← pow_add, ← Nat.mul_assoc]
  exact hm.trans (Parameters.modulus_bounds parameter).1

theorem actual_reference_lower_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ color,
      1 / (2 * (Parameters.modulus parameter : ℝ)) ≤ actualReferenceMean cutoffScale parameter (beta parameter) color := by
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
  have hsmall : 3 * (boundary.card : ℝ) ≤ Parameters.modulus parameter := by
    have hmargin := safeMargin_sixth parameter
    have hcard := boundaryPalette_card (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter) hs.2.2.1 (by have hh := hs.2.2.2; omega)
    have hcard' : (boundary.card : ℝ) ≤ 2 * Parameters.safeMargin parameter := by
      have hh : (boundary.card : ℝ) = 2 * boundaryHalf cutoffScale parameter := by exact_mod_cast hcard
      rw [hh]
      exact_mod_cast (show 2 * boundaryHalf cutoffScale parameter ≤ 2 * (Parameters.safeMargin parameter : ℤ) by linarith [hs.2.2.2])
    have hh : (6 : ℝ) * Parameters.safeMargin parameter ≤ Parameters.modulus parameter := by exact_mod_cast hmargin
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
  have hscale0 : 0 ≤ scale := by dsimp only [scale]; positivity
  have hidentity : scale * v7BaseBoundaryMass cutoffScale parameter (boundaryHalf cutoffScale parameter) =
      (boundary.card : ℝ) / Parameters.modulus parameter := by
    dsimp only [scale, v7BaseBoundaryMass, boundary]
    field_simp
  have hl : -(boundary.card : ℝ) / (2 * Parameters.modulus parameter) ≤ scale * change := by
    have hh := mul_le_mul_of_nonneg_left hmass.1 hscale0
    dsimp only [change]
    rw [mul_sub]
    rw [← mul_div_assoc, hidentity] at hh
    rw [hidentity]
    have heq : -(boundary.card : ℝ) / (2 * Parameters.modulus parameter) =
        -((boundary.card : ℝ) / Parameters.modulus parameter) / 2 := by ring
    rw [heq]
    linarith
  have hu : scale * change ≤ (boundary.card : ℝ) / Parameters.modulus parameter := by
    have hh := mul_le_mul_of_nonneg_left hmass.2 hscale0
    have heq : scale * (2 * v7BaseBoundaryMass cutoffScale parameter (boundaryHalf cutoffScale parameter)) =
        2 * ((boundary.card : ℝ) / Parameters.modulus parameter) := by rw [← hidentity]; ring
    rw [heq] at hh
    dsimp only [change]
    rw [mul_sub, hidentity]
    linarith
  intro color
  have hh := uniform_boundary_perturbation_lower boundary (scale * change)
    (by simpa only [Fintype.card_fin] using hq) (by simpa only [Fintype.card_fin] using hsmall)
    (by simpa only [Fintype.card_fin] using hl) (by simpa only [Fintype.card_fin] using hu) color
  have heq : actualReferenceMean cutoffScale parameter (beta parameter) color =
      (Parameters.modulus parameter : ℝ)⁻¹ + (scale * change) *
        (uniformFiniteProfile boundary color - uniformFiniteProfile boundaryᶜ color) := by
    simp only [actualReferenceMean, referenceMean, calibratedReferenceMean, Pi.add_apply,
      Pi.smul_apply, Pi.sub_apply, smul_eq_mul, scale, change, boundary, one_div]
    ring
  simpa only [Fintype.card_fin, ← heq] using hh

end V7Calibration
end
end AFT
