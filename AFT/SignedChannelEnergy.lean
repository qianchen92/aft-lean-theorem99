import AFT.FiniteConcentration
import AFT.LocalResponse

/-! # Signed finite substochastic channels with an actual output density ceiling -/

namespace AFT

open scoped BigOperators Classical
noncomputable section

/-- Weighted Cauchy--Schwarz transfers an arbitrary signed score through a
positive finite channel. Only its genuine average output density enters. -/
theorem signedChannel_profile_energy_le {Input Output : Type*} [Fintype Input] [Fintype Output]
    (input : FiniteDist Input) (reference : Output → ℝ)
    (kernel : Input → Output → ℝ) (densityBound : ℝ)
    (href : ∀ output, 0 < reference output) (hbound : 0 ≤ densityBound)
    (hkernel : ∀ point output, 0 ≤ kernel point output)
    (hmass : ∀ point, (∑ output, kernel point output) ≤ 1)
    (hdensity : ∀ output, (∑ point, input.weight point * kernel point output) ≤ densityBound * reference output)
    (score : Input → ℝ) :
    profileSquareNorm reference (fun output => ∑ point, input.weight point * score point * kernel point output) ≤
      densityBound * input.l2Sq score := by
  have hpoint (output : Output) :
      (∑ point, input.weight point * score point * kernel point output) ^ 2 / reference output ≤
        densityBound * ∑ point, input.weight point * score point ^ 2 * kernel point output := by
    have hc : (∑ point, input.weight point * score point * kernel point output) ^ 2 ≤
        (∑ point, input.weight point * kernel point output) *
          ∑ point, input.weight point * score point ^ 2 * kernel point output := by
      apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
      · intro point _; exact mul_nonneg (input.nonneg point) (hkernel point output)
      · intro point _; exact mul_nonneg (mul_nonneg (input.nonneg point) (sq_nonneg _)) (hkernel point output)
      · intro point _; ring
    have hn : 0 ≤ ∑ point, input.weight point * score point ^ 2 * kernel point output := by
      exact Finset.sum_nonneg fun point _ => mul_nonneg (mul_nonneg (input.nonneg point) (sq_nonneg _)) (hkernel point output)
    apply (div_le_iff₀ (href output)).mpr
    exact hc.trans ((mul_le_mul_of_nonneg_right (hdensity output) hn).trans_eq (by ring))
  calc
    _ ≤ ∑ output, densityBound * ∑ point, input.weight point * score point ^ 2 * kernel point output :=
      Finset.sum_le_sum fun output _ => hpoint output
    _ = densityBound * ∑ point, input.weight point * score point ^ 2 * ∑ output, kernel point output := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp only [← Finset.mul_sum]
    _ ≤ densityBound * ∑ point, input.weight point * score point ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hbound
      apply Finset.sum_le_sum
      intro point _
      exact (mul_le_mul_of_nonneg_left (hmass point) (mul_nonneg (input.nonneg point) (sq_nonneg _))).trans_eq (mul_one _)
    _ = _ := rfl

end
end AFT
