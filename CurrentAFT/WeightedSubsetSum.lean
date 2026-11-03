import Mathlib

/-! # Nonnegative weighted subset sums without a population factor -/
namespace CurrentAFT.WeightedSubsetSum
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {Index : Type*} [DecidableEq Index]

theorem insert_recursion (pool : Finset Index) (point : Index) (hpoint : point ∉ pool)
    (activity : Index → ℝ) (degree : ℕ) :
    (∑ selected ∈ (insert point pool).powersetCard (degree + 1), ∏ index ∈ selected, activity index) =
      (∑ selected ∈ pool.powersetCard (degree + 1), ∏ index ∈ selected, activity index) +
        activity point * (∑ selected ∈ pool.powersetCard degree, ∏ index ∈ selected, activity index) := by
  have hnot (selected : Finset Index) (hselected : selected ⊆ pool) : point ∉ selected :=
    fun hmember => hpoint (hselected hmember)
  have hdisjoint : Disjoint (pool.powersetCard (degree + 1)) ((pool.powersetCard degree).image (insert point)) := by
    apply Finset.disjoint_left.mpr
    intro selected hselected himage
    obtain ⟨other, _, hequal⟩ := Finset.mem_image.mp himage
    apply hnot selected (Finset.mem_powersetCard.mp hselected).1
    rw [← hequal]
    exact Finset.mem_insert_self _ _
  rw [Finset.powersetCard_succ_insert hpoint, Finset.sum_union hdisjoint]
  congr 1
  rw [Finset.sum_image]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro selected hselected
    exact Finset.prod_insert (hnot selected (Finset.mem_powersetCard.mp hselected).1)
  · intro first hfirst second hsecond hequal
    have h := congrArg (fun selected => selected.erase point) hequal
    simpa only [Finset.erase_insert (hnot first (Finset.mem_powersetCard.mp hfirst).1),
      Finset.erase_insert (hnot second (Finset.mem_powersetCard.mp hsecond).1)] using h

/-- Every unordered distinct subset is bounded by the complete ordered
power expansion. No number of vertices or choice of enumeration is lost. -/
theorem sum_le_power (pool : Finset Index) (activity : Index → ℝ)
    (hnonneg : ∀ index ∈ pool, 0 ≤ activity index) (degree : ℕ) :
    (∑ selected ∈ pool.powersetCard degree, ∏ index ∈ selected, activity index) ≤
      (∑ index ∈ pool, activity index) ^ degree := by
  induction pool using Finset.induction_on generalizing degree with
  | empty =>
    cases degree with
    | zero => simp
    | succ degree =>
      rw [Finset.powersetCard_eq_empty.mpr (by simp)]
      simp
  | @insert point pool hpoint ih =>
    have hp : 0 ≤ activity point := hnonneg point (Finset.mem_insert_self _ _)
    have hpool : ∀ index ∈ pool, 0 ≤ activity index :=
      fun index hindex => hnonneg index (Finset.mem_insert_of_mem hindex)
    have hsum : 0 ≤ ∑ index ∈ pool, activity index := Finset.sum_nonneg (fun index hindex => hpool index hindex)
    cases degree with
    | zero => simp
    | succ degree =>
      rw [insert_recursion pool point hpoint activity degree, Finset.sum_insert hpoint]
      calc
        _ ≤ (∑ index ∈ pool, activity index) ^ (degree + 1) +
            activity point * (∑ index ∈ pool, activity index) ^ degree :=
          add_le_add (ih hpool _) (mul_le_mul_of_nonneg_left (ih hpool _) hp)
        _ = (activity point + ∑ index ∈ pool, activity index) *
            (∑ index ∈ pool, activity index) ^ degree := by rw [pow_succ]; ring
        _ ≤ (activity point + ∑ index ∈ pool, activity index) *
            (activity point + ∑ index ∈ pool, activity index) ^ degree :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ hsum (le_add_of_nonneg_left hp) degree) (add_nonneg hp hsum)
        _ = _ := by rw [pow_succ]; ring

theorem finite_sum_le_power [Fintype Index] (activity : Index → ℝ)
    (hnonneg : ∀ index, 0 ≤ activity index) (degree : ℕ) :
    (∑ selected ∈ Finset.univ.powersetCard degree, ∏ index ∈ selected, activity index) ≤
      (∑ index, activity index) ^ degree :=
  sum_le_power Finset.univ activity (fun index _ => hnonneg index) degree

theorem tagged_sum_le_power (pool : Finset Index) (activity : Index → ℝ)
    (hnonneg : ∀ index ∈ pool, 0 ≤ activity index) (tag : ℝ) (htag : 0 ≤ tag) (degree : ℕ) :
    (∑ selected ∈ pool.powersetCard degree, (∏ index ∈ selected, activity index) * tag ^ degree) ≤
      ((∑ index ∈ pool, activity index) * tag) ^ degree := by
  have h := sum_le_power pool (fun index => activity index * tag)
    (fun index hindex => mul_nonneg (hnonneg index hindex) htag) degree
  have hequal : (∑ selected ∈ pool.powersetCard degree,
      ∏ index ∈ selected, activity index * tag) =
      ∑ selected ∈ pool.powersetCard degree, (∏ index ∈ selected, activity index) * tag ^ degree := by
    apply Finset.sum_congr rfl
    intro selected hselected
    rw [Finset.prod_mul_distrib, Finset.prod_const, (Finset.mem_powersetCard.mp hselected).2]
  rw [hequal] at h
  simpa only [Finset.sum_mul] using h

/-- Grouping every retained subset by its exact cardinality gives the
fixed-order bound used by the complete root defect. -/
theorem sum_card_range_le (pool : Finset Index) (activity : Index → ℝ)
    (hnonneg : ∀ index ∈ pool, 0 ≤ activity index) (bound : ℕ → ℝ)
    (hbound : ∀ degree, 0 ≤ bound degree) (maximum : ℕ) :
    (∑ selected ∈ pool.powerset.filter (fun selected => 2 ≤ selected.card ∧ selected.card ≤ maximum),
      bound selected.card * ∏ index ∈ selected, activity index) ≤
      ∑ degree ∈ Finset.range (maximum + 1),
        if 2 ≤ degree then bound degree * (∑ index ∈ pool, activity index) ^ degree else 0 := by
  have hfiber (degree : ℕ) :
      (∑ selected ∈ pool.powersetCard degree,
        if 2 ≤ selected.card ∧ selected.card ≤ maximum then bound selected.card *
          (∏ index ∈ selected, activity index) else 0) =
      if 2 ≤ degree ∧ degree ≤ maximum then bound degree *
        (∑ selected ∈ pool.powersetCard degree, ∏ index ∈ selected, activity index) else 0 := by
    calc
      _ = ∑ selected ∈ pool.powersetCard degree,
          if 2 ≤ degree ∧ degree ≤ maximum then bound degree * (∏ index ∈ selected, activity index) else 0 := by
        apply Finset.sum_congr rfl
        intro selected hselected
        rw [(Finset.mem_powersetCard.mp hselected).2]
      _ = _ := by
        by_cases hcondition : 2 ≤ degree ∧ degree ≤ maximum
        · simp only [if_pos hcondition, Finset.mul_sum]
        · simp only [if_neg hcondition, Finset.sum_const_zero]
  rw [Finset.sum_filter, Finset.sum_powerset]
  simp_rw [hfiber]
  calc
    _ ≤ ∑ degree ∈ Finset.range (pool.card + 1),
        if 2 ≤ degree ∧ degree ≤ maximum then bound degree *
          (∑ index ∈ pool, activity index) ^ degree else 0 := by
      apply Finset.sum_le_sum
      intro degree _
      split_ifs
      · exact mul_le_mul_of_nonneg_left (sum_le_power pool activity hnonneg degree) (hbound degree)
      · exact le_rfl
    _ = ∑ degree ∈ (Finset.range (pool.card + 1)).filter (fun degree => degree ≤ maximum),
        if 2 ≤ degree then bound degree * (∑ index ∈ pool, activity index) ^ degree else 0 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro degree _
      split_ifs <;> simp_all
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (by
      intro degree hdegree
      have h := (Finset.mem_filter.mp hdegree).2
      exact Finset.mem_range.mpr (by omega)) (fun degree _ _ => by
        split_ifs
        · exact mul_nonneg (hbound degree) (pow_nonneg (Finset.sum_nonneg hnonneg) _)
        · exact le_rfl)

end
end CurrentAFT.WeightedSubsetSum
