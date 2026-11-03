import CurrentAFT.WeightedSubsetSum

/-! # Fixed-order summation of all genuine root subsets -/
namespace CurrentAFT.RootSubsetNormSum
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000

theorem power_decay (base constant : ℝ) (hbase : 1 ≤ base) (hconstant : 1 ≤ constant)
    (order degree : ℕ) (hlower : 2 ≤ degree) (hupper : degree ≤ order) :
    (constant / base ^ 13) ^ degree ≤ constant ^ order / base ^ 26 := by
  have hb : 0 < base := lt_of_lt_of_le zero_lt_one hbase
  rw [div_pow, ← pow_mul]
  apply (div_le_div_of_nonneg_left (pow_nonneg (zero_le_one.trans hconstant) _)
    (pow_pos hb _) (pow_le_pow_right₀ hbase (by omega : 26 ≤ 13 * degree))).trans
  exact div_le_div_of_nonneg_right (pow_le_pow_right₀ hconstant hupper) (pow_nonneg hb.le _)

theorem subset_sum_decay {Index : Type*} [DecidableEq Index]
    (pool : Finset Index) (activity : Index → ℝ) (hnonneg : ∀ index ∈ pool, 0 ≤ activity index)
    (base constant : ℝ) (hbase : 1 ≤ base) (hconstant : 1 ≤ constant)
    (hsum : (∑ index ∈ pool, activity index) ≤ constant / base ^ 13) (order : ℕ) :
    (∑ selected ∈ pool.powerset.filter (fun selected => 2 ≤ selected.card ∧ selected.card ≤ order),
      ∏ index ∈ selected, activity index) ≤ ((order + 1 : ℕ) : ℝ) * constant ^ order / base ^ 26 := by
  have h := WeightedSubsetSum.sum_card_range_le pool activity hnonneg (fun _ => 1)
    (fun _ => zero_le_one) order
  simp only [one_mul] at h
  apply h.trans
  calc
    _ ≤ ∑ _degree ∈ Finset.range (order + 1), constant ^ order / base ^ 26 := by
      apply Finset.sum_le_sum
      intro degree hdegree
      split_ifs with hlower
      · exact (pow_le_pow_left₀ (Finset.sum_nonneg hnonneg) hsum degree).trans
          (power_decay base constant hbase hconstant order degree hlower
            (by have := Finset.mem_range.mp hdegree; omega))
      · exact div_nonneg (pow_nonneg (zero_le_one.trans hconstant) _) (pow_nonneg (zero_le_one.trans hbase) _)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

end
end CurrentAFT.RootSubsetNormSum
