import AFT.SignedChannelEnergy

/-! # Joint source/input extension of actual signed finite channels -/

namespace AFT
open scoped BigOperators Classical
noncomputable section

/-- Averaging a family of signed profiles is contractive in every fixed
weighted profile Hilbert space. Source probabilities remain inside the sum. -/
theorem profileSquareNorm_average_le {Source Output : Type*} [Fintype Source] [Fintype Output]
    (source : FiniteDist Source) (reference : Output → ℝ) (href : ∀ output, 0 ≤ reference output)
    (profile : Source → Output → ℝ) :
    profileSquareNorm reference (fun output => ∑ point, source.weight point * profile point output) ≤
      ∑ point, source.weight point * profileSquareNorm reference (profile point) := by
  calc
    _ ≤ ∑ output, (∑ point, source.weight point * profile point output ^ 2) / reference output := by
      apply Finset.sum_le_sum
      intro output _
      apply div_le_div_of_nonneg_right _ (href output)
      have hh : (∑ point, source.weight point * profile point output) ^ 2 ≤
          (∑ point, source.weight point) * (∑ point, source.weight point * profile point output ^ 2) := by
        apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
        · intro point _; exact source.nonneg point
        · intro point _; exact mul_nonneg (source.nonneg point) (sq_nonneg _)
        · intro point _; ring
      simpa only [source.sum_one, one_mul] using hh
    _ = _ := by
      simp only [Finset.sum_div, profileSquareNorm, Finset.mul_sum, mul_div_assoc]
      exact Finset.sum_comm

/-- Turning a density into its actual signed mass preserves its Hilbert
square exactly, including zero-probability input atoms. -/
theorem profileSquareNorm_weight_mul {Input : Type*} [Fintype Input]
    (input : FiniteDist Input) (density : Input → ℝ) :
    profileSquareNorm input.weight (fun color => input.weight color * density color) = input.l2Sq density := by
  apply Finset.sum_congr rfl
  intro color _
  change (input.weight color * density color) ^ 2 / input.weight color = input.weight color * density color ^ 2
  by_cases hz : input.weight color = 0
  · simp only [hz, zero_mul, zero_pow (by norm_num : (2 : ℕ) ≠ 0), div_zero]
  · field_simp

end
end AFT
