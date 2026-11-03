import AFT.BodyShiftFringe

/-! # Preserving the physical fringe mass under the true root operator -/

namespace AFT.V7Calibration

open Filter GaussianSource
open scoped BigOperators Classical Topology

noncomputable section

theorem actualCoreLaw_safe_value (parameter : ℕ) (color : Fin (Parameters.modulus parameter))
    (hc : color ∈ safePalette parameter) :
    (actualCoreLaw parameter).weight color = 1 / (Parameters.safeSize parameter : ℝ) := by
  rw [actualCoreLaw_weight]
  simp only [uniformFiniteProfile, if_pos hc, safePalette_card, one_div]

theorem actualCoreLaw_outside_value (parameter : ℕ) (color : Fin (Parameters.modulus parameter))
    (hc : color ∉ safePalette parameter) : (actualCoreLaw parameter).weight color = 0 := by
  rw [actualCoreLaw_weight]
  simp only [uniformFiniteProfile, if_neg hc]

theorem actualCoreLaw_upper (parameter : ℕ) (color : Fin (Parameters.modulus parameter)) :
    (actualCoreLaw parameter).weight color ≤ 1 / (Parameters.safeSize parameter : ℝ) := by
  by_cases hc : color ∈ safePalette parameter
  · rw [actualCoreLaw_safe_value parameter color hc]
  · rw [actualCoreLaw_outside_value parameter color hc]
    positivity

theorem bodyOutsideMass_le_variation (parameter : ℕ) (profile : Fin (Parameters.modulus parameter) → ℝ)
    (hn : ∀ color, 0 ≤ profile color)
    (hs : ∀ color, color ∉ safePalette parameter → profile color = 0) (shift : ℤ) :
    bodyOutsideMass parameter profile shift ≤
      ∑ color, |integerShiftProfile parameter profile shift color - profile color| := by
  apply Finset.sum_le_sum
  intro color _
  unfold bodyOutside
  split_ifs with hc
  · exact abs_nonneg _
  · rw [hs color hc, sub_zero, abs_of_nonneg (integerShiftProfile_nonneg parameter profile hn shift color)]

theorem bodyInside_l1_le_variation (parameter : ℕ) (profile : Fin (Parameters.modulus parameter) → ℝ)
    (hn : ∀ color, 0 ≤ profile color) (hm : ∑ color, profile color = 1)
    (hs : ∀ color, color ∉ safePalette parameter → profile color = 0) (shift : ℤ) :
    (∑ color, |bodyInside parameter profile shift color|) ≤
      2 * ∑ color, |integerShiftProfile parameter profile shift color - profile color| := by
  have hout := bodyOutsideMass_bounds parameter profile hn hm shift
  have hpoint (color) : |bodyInside parameter profile shift color| ≤
      |integerShiftProfile parameter profile shift color - profile color| +
        bodyOutsideMass parameter profile shift * profile color := by
    by_cases hc : color ∈ safePalette parameter
    · have heq : bodyInside parameter profile shift color =
          (integerShiftProfile parameter profile shift color - profile color) + bodyOutsideMass parameter profile shift * profile color := by
        simp only [bodyInside, if_pos hc]
        ring
      rw [heq]
      exact (abs_add_le _ _).trans_eq (by rw [abs_of_nonneg (mul_nonneg hout.1 (hn color))])
    · rw [bodyInside_support parameter profile hs shift color hc]
      simp only [abs_zero]
      exact add_nonneg (abs_nonneg _) (mul_nonneg hout.1 (hn color))
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun color _ => hpoint color)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hm, mul_one] at hh
  have hmass := bodyOutsideMass_le_variation parameter profile hn hs shift
  linarith

theorem bodyInside_relative (parameter : ℕ) (profile : Fin (Parameters.modulus parameter) → ℝ)
    (hm : ∑ color, profile color = 1)
    (hcompare : ∀ color, (actualCoreLaw parameter).weight color / 2 ≤ profile color ∧
      profile color ≤ 2 * (actualCoreLaw parameter).weight color)
    (shift : ℤ) (output : Fin (Parameters.modulus parameter)) :
    |bodyInside parameter profile shift output| ≤ 4 * profile output := by
  have hn (color) : 0 ≤ profile color := le_trans (div_nonneg ((actualCoreLaw parameter).nonneg color) (by norm_num)) (hcompare color).1
  have hs (color) (hc : color ∉ safePalette parameter) : profile color = 0 := by
    have hh := hcompare color
    rw [actualCoreLaw_outside_value parameter color hc] at hh
    simp only [zero_div, mul_zero] at hh
    exact le_antisymm hh.2 hh.1
  have hmu := bodyOutsideMass_bounds parameter profile hn hm shift
  by_cases hc : output ∈ safePalette parameter
  · have hbound : integerShiftProfile parameter profile shift output ≤ 2 / (Parameters.safeSize parameter : ℝ) :=
      integerShiftProfile_bound parameter profile _ (by positivity)
        (fun color => (hcompare color).2.trans (by have hh := actualCoreLaw_upper parameter color; simp only [div_eq_mul_inv] at *; linarith)) shift output
    have hlower := (hcompare output).1
    rw [actualCoreLaw_safe_value parameter output hc] at hlower
    have hshift := integerShiftProfile_nonneg parameter profile hn shift output
    simp only [div_eq_mul_inv] at hbound hlower
    simp only [bodyInside, if_pos hc]
    apply abs_le.mpr
    constructor <;> nlinarith [mul_nonneg hmu.1 (hn output), mul_nonneg (sub_nonneg.mpr hmu.2) (hn output)]
  · rw [bodyInside_support parameter profile hs shift output hc, hs output hc]
    norm_num

theorem bodyInside_square_le_variation (parameter : ℕ) (profile : Fin (Parameters.modulus parameter) → ℝ)
    (hm : ∑ color, profile color = 1)
    (hcompare : ∀ color, (actualCoreLaw parameter).weight color / 2 ≤ profile color ∧
      profile color ≤ 2 * (actualCoreLaw parameter).weight color)
    (shift : ℤ) :
    profileSquareNorm profile (bodyInside parameter profile shift) ≤
      8 * ∑ color, |integerShiftProfile parameter profile shift color - profile color| := by
  have hn (color) : 0 ≤ profile color := le_trans (div_nonneg ((actualCoreLaw parameter).nonneg color) (by norm_num)) (hcompare color).1
  have hs (color) (hc : color ∉ safePalette parameter) : profile color = 0 := by
    have hh := hcompare color
    rw [actualCoreLaw_outside_value parameter color hc] at hh
    simp only [zero_div, mul_zero] at hh
    exact le_antisymm hh.2 hh.1
  have hpoint (color) : (bodyInside parameter profile shift color)^2 / profile color ≤
      4 * |bodyInside parameter profile shift color| := by
    by_cases hc : color ∈ safePalette parameter
    · have hsize : (0 : ℝ) < Parameters.safeSize parameter := by exact_mod_cast Parameters.safeSize_positive parameter
      have hp : 0 < profile color := lt_of_lt_of_le (by rw [actualCoreLaw_safe_value parameter color hc]; positivity) (hcompare color).1
      apply (div_le_iff₀ hp).mpr
      have hh := mul_le_mul_of_nonneg_left (bodyInside_relative parameter profile hm hcompare shift color)
        (abs_nonneg (bodyInside parameter profile shift color))
      nlinarith [sq_abs (bodyInside parameter profile shift color)]
    · rw [bodyInside_support parameter profile hs shift color hc]
      simp only [zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_div, abs_zero, mul_zero, le_refl]
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun color _ => hpoint color)
  rw [← Finset.mul_sum] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_left (bodyInside_l1_le_variation parameter profile hn hm hs shift) (by norm_num)).trans_eq (by ring))

theorem rootProfileOperator_nonneg (parameter : ℕ) (profile : Fin (Parameters.modulus parameter) → ℝ)
    (hn : ∀ color, 0 ≤ profile color) (output : Fin (Parameters.modulus parameter)) :
    0 ≤ rootProfileOperator parameter profile output := by
  change 0 ≤ ∑ root : Window (v7RootCutoff parameter), _ * _
  apply Finset.sum_nonneg
  intro root _
  exact mul_nonneg (FiniteDist.nonneg _ _) (integerShiftProfile_nonneg parameter profile hn root output)

theorem rootProfileOperator_mass_le (parameter : ℕ) (profile : Fin (Parameters.modulus parameter) → ℝ)
    (hn : ∀ color, 0 ≤ profile color) :
    (∑ output, rootProfileOperator parameter profile output) ≤ ∑ color, profile color := by
  change (∑ output, ∑ root : Window (v7RootCutoff parameter), _ * _) ≤ _
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  calc
    _ ≤ ∑ root : Window (v7RootCutoff parameter),
        (rootMarginal (v7RootWidth parameter) (v7RootCutoff parameter) (Parameters.bodies parameter)
          (Parameters.bodies_positive parameter)).weight root * (∑ color, profile color) := by
      apply Finset.sum_le_sum
      intro root _
      exact mul_le_mul_of_nonneg_left (integerShiftProfile_mass_le parameter profile hn root) (FiniteDist.nonneg _ _)
    _ = _ := by rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]

theorem rootProfileOperator_bound (parameter : ℕ) (profile : Fin (Parameters.modulus parameter) → ℝ)
    (bound : ℝ) (hb : 0 ≤ bound) (h : ∀ color, profile color ≤ bound)
    (output : Fin (Parameters.modulus parameter)) :
    rootProfileOperator parameter profile output ≤ bound := by
  change (∑ root : Window (v7RootCutoff parameter), _ * _) ≤ _
  calc
    _ ≤ ∑ root : Window (v7RootCutoff parameter),
        (rootMarginal (v7RootWidth parameter) (v7RootCutoff parameter) (Parameters.bodies parameter)
          (Parameters.bodies_positive parameter)).weight root * bound := by
      apply Finset.sum_le_sum
      intro root _
      exact mul_le_mul_of_nonneg_left (integerShiftProfile_bound parameter profile bound hb h root output) (FiniteDist.nonneg _ _)
    _ = _ := by rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]

/-- The true root image of the outside piece is controlled by the actual
root-uniform deficit, even for a fixed shift larger than a typical root. -/
theorem bodyOutside_root_deficit (parameter : ℕ) (profile : Fin (Parameters.modulus parameter) → ℝ)
    (hcompare : ∀ color, profile color ≤ 2 * (actualCoreLaw parameter).weight color)
    (shift : ℤ) (output : Fin (Parameters.modulus parameter)) :
    rootProfileOperator parameter (bodyOutside parameter profile shift) output ≤
      2 * (1 / (Parameters.safeSize parameter : ℝ) - actualRootBodyMean parameter output) := by
  have hbound (color) : bodyOutside parameter profile shift color + 2 * (actualCoreLaw parameter).weight color ≤
      2 / (Parameters.safeSize parameter : ℝ) := by
    by_cases hc : color ∈ safePalette parameter
    · simp only [bodyOutside, if_pos hc, actualCoreLaw_safe_value parameter color hc, zero_add]
      ring_nf
      exact le_rfl
    · rw [bodyOutside, if_neg hc, actualCoreLaw_outside_value parameter color hc, mul_zero, add_zero]
      exact integerShiftProfile_bound parameter profile _ (by positivity)
        (fun color => (hcompare color).trans (by have hh := actualCoreLaw_upper parameter color; simp only [div_eq_mul_inv] at *; linarith)) shift color
  have hh := rootProfileOperator_bound parameter
    (bodyOutside parameter profile shift + (2 : ℝ) • (actualCoreLaw parameter).weight)
    (2 / (Parameters.safeSize parameter : ℝ)) (by positivity) hbound output
  rw [map_add, map_smul, rootProfileOperator_core] at hh
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hh
  simp only [div_eq_mul_inv] at *
  linarith

end
end AFT.V7Calibration
