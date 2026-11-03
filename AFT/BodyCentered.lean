import AFT.BodyPhysicalSupport

/-! # Canonical input and primary fringe for each actual body type -/

namespace AFT.V7Calibration

open Filter GaussianSource
open scoped BigOperators Classical Topology

noncomputable section

def bodyCenteredOutside (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) (shift : ℤ) :
    Fin (Parameters.modulus parameter) → ℝ :=
  rootProfileOperator parameter (bodyOutside parameter (actualBodyCenter cutoffScale parameter beta) shift) -
    bodyOutsideMass parameter (actualBodyCenter cutoffScale parameter beta) shift • actualReferenceMean cutoffScale parameter beta

def bodyCanonicalInput (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) (shift : ℤ) :
    Fin (Parameters.modulus parameter) → ℝ :=
  bodyInside parameter (actualBodyCenter cutoffScale parameter beta) shift +
    (1 - bodyOutsideMass parameter (actualBodyCenter cutoffScale parameter beta) shift) •
      (actualBodyCenter cutoffScale parameter beta - (actualCoreLaw parameter).weight)

/-- The complete centered physical body type, retaining the mass-balancing
subtraction and the root-only reference fringe exactly. -/
theorem body_type_centered_decomposition (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) (shift : ℤ) :
    rootProfileOperator parameter (integerShiftProfile parameter (actualBodyCenter cutoffScale parameter beta) shift) -
      actualReferenceMean cutoffScale parameter beta =
    rootProfileOperator parameter (bodyCanonicalInput cutoffScale parameter beta shift) +
      bodyCenteredOutside cutoffScale parameter beta shift +
      (1 - bodyOutsideMass parameter (actualBodyCenter cutoffScale parameter beta) shift) •
        (actualRootBodyMean parameter - actualReferenceMean cutoffScale parameter beta) := by
  let P := actualBodyCenter cutoffScale parameter beta
  let mu := bodyOutsideMass parameter P shift
  have hid : integerShiftProfile parameter P shift =
      bodyInside parameter P shift + bodyOutside parameter P shift + (1 - mu) • P := by
    funext color
    have hh := body_shift_split parameter P shift color
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    dsimp only [mu]
    linarith
  change rootProfileOperator parameter (integerShiftProfile parameter P shift) - _ = _
  rw [hid]
  simp only [bodyCanonicalInput, bodyCenteredOutside, map_add, map_smul, map_sub,
    rootProfileOperator_core]
  funext color
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  change rootProfileOperator parameter (bodyInside parameter P shift) color +
      rootProfileOperator parameter (bodyOutside parameter P shift) color +
      (1 - mu) * rootProfileOperator parameter P color - actualReferenceMean cutoffScale parameter beta color = _
  dsimp only [P, mu]
  ring

theorem bodyCanonicalInput_mass (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) (shift : ℤ)
    (hm : ∑ color, actualBodyCenter cutoffScale parameter beta color = 1)
    (hs : ∀ color, color ∉ safePalette parameter → actualBodyCenter cutoffScale parameter beta color = 0)
    (hshift : |shift| ≤ (Parameters.safeMargin parameter : ℤ)) :
    (∑ color, bodyCanonicalInput cutoffScale parameter beta shift color) = 0 := by
  simp only [bodyCanonicalInput, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
    bodyInside_mass parameter _ hm hs shift hshift, hm, (actualCoreLaw parameter).sum_one, sub_self, mul_zero, add_zero]

theorem bodyCanonicalInput_support (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) (shift : ℤ)
    (hs : ∀ color, color ∉ safePalette parameter → actualBodyCenter cutoffScale parameter beta color = 0)
    (color : Fin (Parameters.modulus parameter)) (hout : color ∉ safePalette parameter) :
    bodyCanonicalInput cutoffScale parameter beta shift color = 0 := by
  simp only [bodyCanonicalInput, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    bodyInside_support parameter _ hs shift color hout, hs color hout,
    actualCoreLaw_outside_value parameter color hout, sub_self, mul_zero, add_zero]

theorem bodyCenteredOutside_mass (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) (shift : ℤ)
    (hs : ∀ color, color ∉ safePalette parameter → actualBodyCenter cutoffScale parameter beta color = 0)
    (hr : ∑ color, actualReferenceMean cutoffScale parameter beta color = 1)
    (hshift : |shift| + v7RootCutoff parameter ≤ (Parameters.safeMargin parameter : ℤ)) :
    (∑ color, bodyCenteredOutside cutoffScale parameter beta shift color) = 0 := by
  simp only [bodyCenteredOutside, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_sub_distrib, ← Finset.mul_sum, bodyOutside_root_mass parameter _ hs shift hshift,
    hr, mul_one, sub_self]

/-- Centering the genuine outside profile costs only its actual fringe
energy plus its squared (small) mass. -/
theorem actual_centered_body_fringe_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ shift : ℤ,
      let mu := bodyOutsideMass parameter (actualBodyCenter cutoffScale parameter (beta parameter)) shift
      (∀ color, |bodyCenteredOutside cutoffScale parameter (beta parameter) shift color| ≤
        8 * (bodyCompensation parameter cutoffScale + mu) * actualPrimary cutoffScale parameter (beta parameter) color) ∧
      profileSquareNorm (actualPrimary cutoffScale parameter (beta parameter))
        (bodyCenteredOutside cutoffScale parameter (beta parameter) shift) ≤
        192 * bodyCompensation parameter cutoffScale * (shift.natAbs : ℝ) / Parameters.modulus parameter + 16 * mu ^ 2 := by
  filter_upwards [actual_body_fringe_bounds_eventually cutoffScale hscale beta hbeta,
    actual_body_center_probability_eventually cutoffScale hscale beta hbeta,
    actual_primary_probability_eventually cutoffScale hscale beta hbeta,
    actual_reference_probability_eventually cutoffScale hscale beta hbeta,
    actual_reference_le_primary_eventually cutoffScale hscale beta hbeta]
    with parameter hf hb hp hr hrp shift
  dsimp only
  let P := actualBodyCenter cutoffScale parameter (beta parameter)
  let p := actualPrimary cutoffScale parameter (beta parameter)
  let r := actualReferenceMean cutoffScale parameter (beta parameter)
  let mu := bodyOutsideMass parameter P shift
  let out := rootProfileOperator parameter (bodyOutside parameter P shift)
  have hP (color) : 0 ≤ P color := (div_nonneg ((actualCoreLaw parameter).nonneg color) (by norm_num)).trans (hb.2.1 color).1
  have hmu := bodyOutsideMass_bounds parameter P hP hb.1 shift
  have hpoint (color) : |out color - mu * r color| ≤
      8 * (bodyCompensation parameter cutoffScale + mu) * p color := by
    have ho := (hf shift).2.2.2.1 color
    have hrr := hrp color
    have hrn := (hr.1 color).1
    have hm := mul_le_mul_of_nonneg_left hrr hmu.1
    exact (abs_sub _ _).trans (by rw [abs_of_nonneg ho.1, abs_of_nonneg (mul_nonneg hmu.1 hrn)]; dsimp only [out, mu, r, p] at *; nlinarith)
  refine ⟨hpoint, ?_⟩
  have hbalance : profileSquareNorm p (mu • r) ≤ 8 * mu ^ 2 := by
    have hterm (color) : (mu * r color)^2 / p color ≤ 8 * mu ^ 2 * r color := by
      apply (div_le_iff₀ (hp.1 color)).mpr
      have hh := mul_le_mul_of_nonneg_left (hrp color) (mul_nonneg (sq_nonneg mu) ((hr.1 color).1))
      dsimp only [p, r]
      nlinarith
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun color _ => hterm color)
    have hrm : (∑ color, r color) = 1 := hr.2
    rw [← Finset.mul_sum, hrm, mul_one] at hh
    exact hh
  have hs := profileSquareNorm_sub_le_two p out (mu • r) (fun color => (hp.1 color).le)
  have hbound := (hf shift).2.2.2.2
  change profileSquareNorm p (out - mu • r) ≤ _
  change profileSquareNorm p out ≤ _ at hbound
  change profileSquareNorm p (out - mu • r) ≤
    192 * bodyCompensation parameter cutoffScale * (shift.natAbs : ℝ) / Parameters.modulus parameter + 16 * mu ^ 2
  simp only [div_eq_mul_inv] at hbound ⊢
  nlinarith

end
end AFT.V7Calibration
