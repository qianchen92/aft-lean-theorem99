import Mathlib

/-!
# Bounded clipping for the current affine transport construction

This file formalizes the clipping map used in
`cor:calibration-bounded-clipping` and the finite-reference high-moment
implication used in `lem:df-positive-repair` in the current manuscript.
The high-moment estimate for the actual calibrated public weight is a
separate construction-specific obligation, not a premise hidden in a
definition here.
-/

namespace CurrentAFT

/-- Clip a real public weight to the interval `[0, 2]`. -/
def clip (weight : ℝ) : ℝ := min 2 (max 0 weight)

theorem clip_nonneg (weight : ℝ) : 0 ≤ clip weight := by
  exact le_min (by norm_num) (le_max_left 0 weight)

theorem clip_le_two (weight : ℝ) : clip weight ≤ 2 :=
  min_le_left _ _

theorem clip_mem_Icc (weight : ℝ) : clip weight ∈ Set.Icc (0 : ℝ) 2 :=
  ⟨clip_nonneg weight, clip_le_two weight⟩

theorem clip_of_nonpos {weight : ℝ} (hweight : weight ≤ 0) : clip weight = 0 := by
  simp [clip, max_eq_left hweight]

theorem clip_of_two_le {weight : ℝ} (hweight : 2 ≤ weight) : clip weight = 2 := by
  have hnonneg : 0 ≤ weight := by linarith
  simp [clip, max_eq_right hnonneg, min_eq_left hweight]

theorem clip_of_mem_Icc {weight : ℝ} (hweight : weight ∈ Set.Icc (0 : ℝ) 2) :
    clip weight = weight := by
  simp [clip, max_eq_right hweight.1, min_eq_right hweight.2]

private theorem clip_ordered_difference {left right : ℝ} (horder : left ≤ right) :
    0 ≤ clip right - clip left ∧ clip right - clip left ≤ right - left := by
  rcases le_total left 0 with hleft | hleft
  · rcases le_total right 0 with hright | hright
    · rw [clip_of_nonpos hleft, clip_of_nonpos hright]
      constructor <;> linarith
    · rcases le_total right 2 with hright2 | hright2
      · rw [clip_of_nonpos hleft, clip_of_mem_Icc ⟨hright, hright2⟩]
        constructor <;> linarith
      · rw [clip_of_nonpos hleft, clip_of_two_le hright2]
        constructor <;> linarith
  · rcases le_total 2 left with hleft2 | hleft2
    · have hright2 : 2 ≤ right := hleft2.trans horder
      rw [clip_of_two_le hleft2, clip_of_two_le hright2]
      constructor <;> linarith
    · have hright : 0 ≤ right := hleft.trans horder
      rcases le_total right 2 with hright2 | hright2
      · rw [clip_of_mem_Icc ⟨hleft, hleft2⟩,
          clip_of_mem_Icc ⟨hright, hright2⟩]
        constructor <;> linarith
      · rw [clip_of_mem_Icc ⟨hleft, hleft2⟩, clip_of_two_le hright2]
        constructor <;> linarith

/-- Bounded clipping is nonexpansive in the absolute-value metric. -/
theorem clip_abs_sub_le (left right : ℝ) :
    |clip left - clip right| ≤ |left - right| := by
  rcases le_total left right with horder | horder
  · obtain ⟨hnonneg, hbound⟩ := clip_ordered_difference horder
    rw [abs_of_nonpos (by linarith : clip left - clip right ≤ 0),
      abs_of_nonpos (by linarith : left - right ≤ 0)]
    linarith
  · obtain ⟨hnonneg, hbound⟩ := clip_ordered_difference horder
    rw [abs_of_nonneg (by linarith : 0 ≤ clip left - clip right),
      abs_of_nonneg (by linarith : 0 ≤ left - right)]
    exact hbound

/-- The clipping operator has Lipschitz constant one. -/
theorem clip_lipschitz : LipschitzWith 1 clip := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro left right
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using clip_abs_sub_le left right

/-- Any positive even moment of the deviation from one bounds clipping loss
pointwise. In the interval `[0, 2]` the loss is zero; outside it the deviation
from one has absolute value at least one. -/
theorem abs_sub_clip_le_even_power (weight : ℝ) (moment : ℕ) (hmoment : 1 ≤ moment) :
    |weight - clip weight| ≤ |weight - 1| ^ (2 * moment) := by
  rcases le_total weight 0 with hlow | hlow
  · rw [clip_of_nonpos hlow]
    have hbase : 1 ≤ |weight - 1| := by
      rw [abs_of_nonpos (by linarith : weight - 1 ≤ 0)]
      linarith
    calc
      |weight - 0| ≤ |weight - 1| := by
        rw [sub_zero, abs_of_nonpos hlow,
          abs_of_nonpos (by linarith : weight - 1 ≤ 0)]
        linarith
      _ = |weight - 1| ^ 1 := by simp
      _ ≤ |weight - 1| ^ (2 * moment) := pow_le_pow_right₀ hbase (by omega)
  · rcases le_total weight 2 with hhigh | hhigh
    · rw [clip_of_mem_Icc ⟨hlow, hhigh⟩, sub_self, abs_zero]
      positivity
    · rw [clip_of_two_le hhigh]
      have hbase : 1 ≤ |weight - 1| := by
        rw [abs_of_nonneg (by linarith : 0 ≤ weight - 1)]
        linarith
      calc
        |weight - 2| ≤ |weight - 1| := by
          rw [abs_of_nonneg (by linarith : 0 ≤ weight - 2),
            abs_of_nonneg (by linarith : 0 ≤ weight - 1)]
          linarith
        _ = |weight - 1| ^ 1 := by simp
        _ ≤ |weight - 1| ^ (2 * moment) := pow_le_pow_right₀ hbase (by omega)

open scoped BigOperators

/-- The reference weights need only be nonnegative. Thus the estimate applies
both to probability laws and to their unnormalized restrictions. -/
theorem clipping_loss_le_even_moment {Index : Type*} [Fintype Index]
    (reference weight : Index → ℝ) (hreference : ∀ index, 0 ≤ reference index)
    (moment : ℕ) (hmoment : 1 ≤ moment) :
    (∑ index, reference index * |weight index - clip (weight index)|) ≤
      ∑ index, reference index * |weight index - 1| ^ (2 * moment) := by
  apply Finset.sum_le_sum
  intro index _
  exact mul_le_mul_of_nonneg_left
    (abs_sub_clip_le_even_power (weight index) moment hmoment) (hreference index)

/-- An established high-moment budget transfers to the same weight's clipping
loss without changing that weight or the reference experiment. -/
theorem clipping_loss_le_of_even_moment {Index : Type*} [Fintype Index]
    (reference weight : Index → ℝ) (hreference : ∀ index, 0 ≤ reference index)
    (moment : ℕ) (hmoment : 1 ≤ moment) (budget : ℝ)
    (hbudget : (∑ index, reference index * |weight index - 1| ^ (2 * moment)) ≤ budget) :
    (∑ index, reference index * |weight index - clip (weight index)|) ≤ budget :=
  (clipping_loss_le_even_moment reference weight hreference moment hmoment).trans hbudget

end CurrentAFT
