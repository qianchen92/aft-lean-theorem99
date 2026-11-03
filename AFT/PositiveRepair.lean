import Mathlib

/-!
# Conditional positive repair

V7 Lemma 9.19 clips a signed weight separately at each retained skeleton.
Here `weight` is the signed mass function at any one fixed skeleton. The
identity below is exact and does not require that its entries be positive.
The separate task of bounding the physical moments is not assumed proved.
-/

namespace AFT

open scoped BigOperators

variable {α : Type*} [Fintype α]

noncomputable def positiveMass (weight : α → ℝ) : ℝ := ∑ a, max (weight a) 0
noncomputable def negativeMass (weight : α → ℝ) : ℝ := ∑ a, max (-weight a) 0
noncomputable def signedMass (weight : α → ℝ) : ℝ := ∑ a, weight a

theorem negativeMass_nonneg (weight : α → ℝ) : 0 ≤ negativeMass weight :=
  Finset.sum_nonneg (fun _ _ => le_max_right _ _)

theorem positiveMass_eq (weight : α → ℝ) :
    positiveMass weight = signedMass weight + negativeMass weight := by
  rw [positiveMass, signedMass, negativeMass, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : 0 ≤ weight a
  · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), add_zero]
  · have hn : weight a ≤ 0 := le_of_not_ge h
    rw [max_eq_right hn, max_eq_left (neg_nonneg.mpr hn)]
    ring

theorem positiveMass_pos (weight : α → ℝ) (hmean : 0 < signedMass weight) :
    0 < positiveMass weight := by
  rw [positiveMass_eq]
  exact add_pos_of_pos_of_nonneg hmean (negativeMass_nonneg weight)

/-- The pointwise Jordan-decomposition identity underlying positive repair. -/
theorem repair_pointwise (weight mean normalizer : ℝ)
    (hmean : 0 < mean) (horder : mean ≤ normalizer) :
    |max weight 0 / normalizer - weight / mean| =
      max weight 0 * (1 / mean - 1 / normalizer) + max (-weight) 0 / mean := by
  by_cases hw : 0 ≤ weight
  · rw [max_eq_left hw, max_eq_right (neg_nonpos.mpr hw)]
    have hdiv : weight / normalizer ≤ weight / mean :=
      div_le_div_of_nonneg_left hw hmean horder
    rw [abs_of_nonpos (sub_nonpos.mpr hdiv)]
    ring
  · have hw' : weight ≤ 0 := le_of_not_ge hw
    rw [max_eq_right hw', max_eq_left (neg_nonneg.mpr hw')]
    have hdiv : weight / mean ≤ 0 := div_nonpos_of_nonpos_of_nonneg hw' hmean.le
    rw [zero_div, zero_sub, abs_of_nonneg (neg_nonneg.mpr hdiv)]
    ring

/-- Exact `L¹` cost of clipping and normalizing a finite signed measure.
Dividing this expression by two gives the signed total-variation cost.
This is V7's displayed positive-repair identity, with all normalizers explicit. -/
theorem positive_repair_l1 (weight : α → ℝ) (hmean : 0 < signedMass weight) :
    (∑ a, |max (weight a) 0 / positiveMass weight - weight a / signedMass weight|) =
      2 * negativeMass weight / signedMass weight := by
  have hpos := positiveMass_pos weight hmean
  have horder : signedMass weight ≤ positiveMass weight := by
    rw [positiveMass_eq]
    exact le_add_of_nonneg_right (negativeMass_nonneg weight)
  simp_rw [repair_pointwise _ _ _ hmean horder]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_div]
  change positiveMass weight * (1 / signedMass weight - 1 / positiveMass weight) +
      negativeMass weight / signedMass weight = _
  field_simp
  nlinarith [positiveMass_eq weight]

/-- The normalized positive part is a probability mass function. -/
theorem positive_repair_normalized (weight : α → ℝ) (hmean : 0 < signedMass weight) :
    (∀ a, 0 ≤ max (weight a) 0 / positiveMass weight) ∧
      (∑ a, max (weight a) 0 / positiveMass weight) = 1 := by
  have hpos := positiveMass_pos weight hmean
  constructor
  · intro a
    exact div_nonneg (le_max_right _ _) hpos.le
  · rw [← Finset.sum_div]
    exact div_self (ne_of_gt hpos)

/-- A negative weight is controlled by any positive even centered moment. -/
theorem negative_part_le_even_moment (weight : ℝ) (moment : ℕ) (hmoment : 0 < moment) :
    max (-weight) 0 ≤ |weight - 1| ^ (2 * moment) := by
  by_cases hw : 0 ≤ weight
  · rw [max_eq_right (neg_nonpos.mpr hw)]
    positivity
  · have hw' : weight < 0 := lt_of_not_ge hw
    have habs : |weight - 1| = 1 - weight := by
      rw [abs_of_neg (by linarith)]
      ring
    rw [max_eq_left (by linarith), habs]
    have hbase : 1 ≤ 1 - weight := by linarith
    have hp := le_self_pow₀ hbase (show 2 * moment ≠ 0 by omega)
    linarith

/-- Finite expectation version, usable at each conditional skeleton. -/
theorem weighted_negative_part_le_even_moment (base weight : α → ℝ)
    (hbase : ∀ a, 0 ≤ base a) (moment : ℕ) (hmoment : 0 < moment) :
    (∑ a, base a * max (-weight a) 0) ≤
      ∑ a, base a * |weight a - 1| ^ (2 * moment) := by
  apply Finset.sum_le_sum
  intro a _
  exact mul_le_mul_of_nonneg_left
    (negative_part_le_even_moment (weight a) moment hmoment) (hbase a)

end AFT
