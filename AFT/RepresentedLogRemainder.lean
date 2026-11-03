import AFT.RepresentedBackground

/-! # Finite logarithms with the global linear cancellation retained -/

namespace AFT.RepresentedPolynomial

open scoped BigOperators Classical

noncomputable section

variable {Seed : Type*}

def logarithmRemainder (table : Table Seed) (cutoff : ℕ) : Table Seed :=
  ∑ index ∈ Finset.range cutoff,
    MvPolynomial.C ((-1 : ℝ) ^ (index + 1) / (index + 2)) * table ^ (index + 2)

theorem logarithm_succ (table : Table Seed) (cutoff : ℕ) :
    logarithm table (cutoff + 1) = table + logarithmRemainder table cutoff := by
  unfold logarithm logarithmRemainder
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_add, Nat.cast_one, zero_add, pow_zero,
    Nat.cast_zero, div_one, map_one, pow_one, one_mul]
  conv_lhs => rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro index _
  congr 2
  ring

/-- The remainder begins in degree two, so the bound is quadratic in the
local activity. It is uniform in the finite truncation order. -/
theorem activity_logarithmRemainder_le (weight : Seed → ℝ) (hweight : ∀ seed, 0 ≤ weight seed)
    (table : Table Seed) (cutoff : ℕ) (hsmall : activity weight table ≤ 1 / 2) :
    activity weight (logarithmRemainder table cutoff) ≤ 2 * activity weight table ^ 2 := by
  have ha := activity_nonneg weight hweight table
  apply (activity_sum_le weight hweight _ _).trans
  calc
    _ ≤ ∑ index ∈ Finset.range cutoff, (1 / 2 : ℝ) ^ index * activity weight table ^ 2 := by
      apply Finset.sum_le_sum
      intro index _
      have hc : |(-1 : ℝ) ^ (index + 1) / (index + 2)| ≤ 1 := by
        rw [abs_div, abs_pow, abs_neg, abs_one, one_pow,
          abs_of_nonneg (by positivity : 0 ≤ (index : ℝ) + 2)]
        exact (div_le_one (by positivity)).mpr (by have := Nat.cast_nonneg (α := ℝ) index; linarith)
      have hh := (activity_mul_le weight hweight
        (MvPolynomial.C ((-1 : ℝ) ^ (index + 1) / (index + 2))) (table ^ (index + 2))).trans
        (mul_le_mul (by simpa only [activity_C] using hc)
          (activity_pow_le weight hweight table (index + 2))
          (activity_nonneg weight hweight _) (by norm_num))
      simp only [one_mul] at hh
      apply hh.trans
      rw [pow_add]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha hsmall index) (sq_nonneg _)
    _ = (∑ index ∈ Finset.range cutoff, (1 / 2 : ℝ) ^ index) * activity weight table ^ 2 :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ 2 * activity weight table ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      calc
        _ ≤ ∑' index : ℕ, (1 / 2 : ℝ) ^ index :=
          (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
            (by norm_num : (1 / 2 : ℝ) < 1)).sum_le_tsum _ (fun _ _ => by positivity)
        _ = 2 := by
          rw [tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
            (by norm_num : (1 / 2 : ℝ) < 1)]
          norm_num

/-- Subtract the specified linear part before taking any activity norm. -/
theorem activity_logarithm_sub_linear_le (weight : Seed → ℝ) (hweight : ∀ seed, 0 ≤ weight seed)
    (linear higher : Table Seed) (cutoff : ℕ) (hcutoff : 1 ≤ cutoff)
    (hsmall : activity weight (linear + higher) ≤ 1 / 2) :
    activity weight (logarithm (linear + higher) cutoff - linear) ≤
      activity weight higher + 2 * activity weight (linear + higher) ^ 2 := by
  obtain ⟨depth, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : cutoff ≠ 0)
  rw [Nat.succ_eq_add_one, logarithm_succ]
  have heq : linear + higher + logarithmRemainder (linear + higher) depth - linear =
      higher + logarithmRemainder (linear + higher) depth := by ring
  rw [heq]
  exact (activity_add_le weight hweight _ _).trans
    (add_le_add le_rfl (activity_logarithmRemainder_le weight hweight _ _ hsmall))

/-- The exact finite background logarithm is estimated after summing its
linear terms. This preserves the actual global mean cancellation. -/
theorem activity_backgroundLogarithm_linear_le {Block : Type*} [Fintype Block]
    (weight : Seed → ℝ) (hweight : ∀ seed, 0 ≤ weight seed)
    (linear higher : Block → Table Seed) (cutoff : ℕ) (hcutoff : 1 ≤ cutoff)
    (hsmall : ∀ block, activity weight (linear block + higher block) ≤ 1 / 2) :
    activity weight (backgroundLogarithm (fun block => linear block + higher block) Finset.univ cutoff) ≤
      activity weight (∑ block, linear block) + ∑ block, activity weight (higher block) +
        2 * ∑ block, activity weight (linear block + higher block) ^ 2 := by
  have heq : backgroundLogarithm (fun block => linear block + higher block) Finset.univ cutoff =
      (∑ block, linear block) + ∑ block, (logarithm (linear block + higher block) cutoff - linear block) := by
    unfold backgroundLogarithm
    simp only [Finset.sum_sub_distrib]
    ring
  rw [heq]
  apply (activity_add_le weight hweight _ _).trans
  have hh := (activity_sum_le weight hweight _ _).trans
    (Finset.sum_le_sum fun block (_ : block ∈ Finset.univ) =>
      activity_logarithm_sub_linear_le weight hweight (linear block) (higher block) cutoff hcutoff (hsmall block))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hh
  linarith only [hh]

end
end AFT.RepresentedPolynomial
