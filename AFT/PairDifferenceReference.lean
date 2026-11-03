import AFT.PairSourceMarginal

/-! # Complete density fibers from true pair source-difference bounds -/

namespace AFT.TrimmedSlice

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- A fixed-endpoint counting bound controls both the full density energy
and the one-fixed density fiber without a further palette supremum. -/
theorem pairDifference_density_bounds (difference : ι → ι → ℝ) (reference : ι → ℝ)
    (lower rowBound : ℝ) (hl : 0 < lower) (href : ∀ color, lower ≤ reference color)
    (hrow : ∀ first, (∑ second, difference first second ^ 2) ≤ rowBound) :
    (∑ first, ∑ second, difference first second ^ 2 / (reference first * reference second)) ≤
      (Fintype.card ι : ℝ) * rowBound / lower ^ 2 ∧
    ∀ first, (∑ second, reference second * (difference first second / (reference first * reference second)) ^ 2) ≤
      rowBound / lower ^ 3 := by
  have hp (color : ι) : 0 < reference color := hl.trans_le (href color)
  constructor
  · calc
      _ ≤ ∑ first, ∑ second, difference first second ^ 2 / lower ^ 2 := by
        apply Finset.sum_le_sum
        intro first _
        apply Finset.sum_le_sum
        intro second _
        apply div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos hl)
        nlinarith [mul_le_mul (href first) (href second) hl.le (hp first).le]
      _ = (∑ first, ∑ second, difference first second ^ 2) / lower ^ 2 := by simp only [Finset.sum_div]
      _ ≤ (∑ _first : ι, rowBound) / lower ^ 2 := div_le_div_of_nonneg_right (Finset.sum_le_sum fun first _ => hrow first) (sq_nonneg _)
      _ = _ := by simp
  · intro first
    calc
      _ = ∑ second, difference first second ^ 2 / (reference first ^ 2 * reference second) := by
        apply Finset.sum_congr rfl
        intro second _
        field_simp
      _ ≤ ∑ second, difference first second ^ 2 / lower ^ 3 := by
        apply Finset.sum_le_sum
        intro second _
        apply div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos hl 3)
        have hfirst := pow_le_pow_left₀ hl.le (href first) 2
        have hh := mul_le_mul hfirst (href second) hl.le (sq_nonneg (reference first))
        simpa only [pow_succ] using hh
      _ = (∑ second, difference first second ^ 2) / lower ^ 3 := by rw [Finset.sum_div]
      _ ≤ _ := div_le_div_of_nonneg_right (hrow first) (pow_nonneg hl.le 3)

/-- The true row L1 source difference bounds its signed marginal directly. -/
theorem pairDifference_marginal_bounds (difference : ι → ι → ℝ) (reference : ι → ℝ)
    (lower rowL1 : ℝ) (hl : 0 < lower) (hrowL1 : 0 ≤ rowL1) (href : ∀ color, lower ≤ reference color)
    (hrow : ∀ first, (∑ second, |difference first second|) ≤ rowL1) :
    (∀ first, |(∑ second, difference first second) / reference first| ≤ rowL1 / lower) ∧
    (∑ first, (∑ second, difference first second) ^ 2 / reference first) ≤
      (Fintype.card ι : ℝ) * rowL1 ^ 2 / lower := by
  have hp (color : ι) : 0 < reference color := hl.trans_le (href color)
  have hab (first : ι) : |∑ second, difference first second| ≤ rowL1 :=
    (Finset.abs_sum_le_sum_abs _ _).trans (hrow first)
  constructor
  · intro first
    rw [abs_div, abs_of_pos (hp first)]
    exact (div_le_div_of_nonneg_right (hab first) (hp first).le).trans
      (div_le_div_of_nonneg_left hrowL1 hl (href first))
  · calc
      _ ≤ ∑ _first : ι, rowL1 ^ 2 / lower := by
        apply Finset.sum_le_sum
        intro first _
        have hsq := pow_le_pow_left₀ (abs_nonneg (∑ second, difference first second)) (hab first) 2
        rw [sq_abs] at hsq
        exact (div_le_div_of_nonneg_right hsq (hp first).le).trans
          (div_le_div_of_nonneg_left (sq_nonneg _) hl (href first))
      _ = _ := by simp; ring

omit [Fintype ι] in
theorem pairDifference_density_sup (difference : ι → ι → ℝ) (reference : ι → ℝ)
    (lower upper : ℝ) (hl : 0 < lower) (hu : 0 ≤ upper)
    (href : ∀ color, lower ≤ reference color) (hdiff : ∀ first second, |difference first second| ≤ upper)
    (first second : ι) : |difference first second / (reference first * reference second)| ≤ upper / lower ^ 2 := by
  have hp (color : ι) : 0 < reference color := hl.trans_le (href color)
  rw [abs_div, abs_of_pos (mul_pos (hp first) (hp second))]
  exact (div_le_div_of_nonneg_right (hdiff first second) (mul_nonneg (hp first).le (hp second).le)).trans
    (div_le_div_of_nonneg_left hu (sq_pos_of_pos hl) (by nlinarith [mul_le_mul (href first) (href second) hl.le (hp first).le]))

end AFT.TrimmedSlice
