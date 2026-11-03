import AFT.NilpotentLogarithm

/-! # Finite logarithm certificates in the literal input representation -/

namespace AFT.RepresentedPolynomial

open scoped BigOperators Classical

noncomputable section

variable {Seed : Type*}

def logarithm (table : Table Seed) (cutoff : ℕ) : Table Seed :=
  ∑ index ∈ Finset.range cutoff,
    MvPolynomial.C ((-1 : ℝ) ^ index / (index + 1)) * table ^ (index + 1)

theorem hasOrder_logarithm (order : Seed → ℕ) (cutoff : ℕ) (table : Table Seed)
    (h : HasOrder order 1 table) : HasOrder order 1 (logarithm table cutoff) := by
  apply hasOrder_sum
  intro index _
  have hp := hasOrder_pow order 1 table h (index + 1)
  simp only [mul_one] at hp
  exact hasOrder_mul order 0 1 _ _ (hasOrder_zero order _)
    (hasOrder_mono order 1 (index + 1) _ hp (by omega))

theorem quotient_logarithm (order : Seed → ℕ) (cutoff : ℕ) (table : Table Seed) :
    quotientMap order cutoff (logarithm table cutoff) =
      FormalLogarithm.finiteLogarithm (quotientMap order cutoff table) cutoff := by
  simp only [logarithm, FormalLogarithm.finiteLogarithm, map_sum, map_mul, map_pow,
    quotient_C, Algebra.smul_def]
  apply Finset.sum_congr rfl
  intro index _
  congr 1
  rw [IsScalarTower.algebraMap_apply ℚ ℝ (CutoffRing order cutoff)]
  simp

/-- The actual finite log certificate exponentiates to the prescribed local
law through the input cutoff. No output-image identification is used. -/
theorem truncate_exponential_logarithm (order : Seed → ℕ) (cutoff : ℕ)
    (table : Table Seed) (h : HasOrder order 1 table) :
    truncate order cutoff (exponential (logarithm table cutoff) cutoff) =
      truncate order cutoff (1 + table) := by
  apply (quotient_eq_iff_truncate order cutoff _ _).mp
  rw [quotient_exponential order cutoff _ (hasOrder_logarithm order cutoff table h),
    quotient_logarithm, FormalLogarithm.exp_finiteLogarithm _ _
      (quotient_pow_zero order cutoff table h), map_add, map_one]
  rfl

theorem activity_logarithm_le (weight : Seed → ℝ) (hweight : ∀ seed, 0 ≤ weight seed)
    (table : Table Seed) (cutoff : ℕ) (hsmall : activity weight table ≤ 1 / 2) :
    activity weight (logarithm table cutoff) ≤ 2 * activity weight table := by
  have ha := activity_nonneg weight hweight table
  apply (activity_sum_le weight hweight _ _).trans
  calc
    _ ≤ ∑ index ∈ Finset.range cutoff, (1 / 2 : ℝ) ^ index * activity weight table := by
      apply Finset.sum_le_sum
      intro index _
      have hc : |(-1 : ℝ) ^ index / (index + 1)| ≤ 1 := by
        rw [abs_div, abs_pow, abs_neg, abs_one, one_pow,
          abs_of_nonneg (by positivity : 0 ≤ (index : ℝ) + 1)]
        exact (div_le_one (by positivity)).mpr (by have := Nat.cast_nonneg (α := ℝ) index; linarith)
      have hh := (activity_mul_le weight hweight
        (MvPolynomial.C ((-1 : ℝ) ^ index / (index + 1))) (table ^ (index + 1))).trans
        (mul_le_mul (by simpa only [activity_C] using hc)
          (activity_pow_le weight hweight table (index + 1))
          (activity_nonneg weight hweight _) (by norm_num))
      simp only [one_mul] at hh
      apply hh.trans
      rw [pow_succ]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha hsmall index) ha
    _ = (∑ index ∈ Finset.range cutoff, (1 / 2 : ℝ) ^ index) * activity weight table :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ 2 * activity weight table := by
      apply mul_le_mul_of_nonneg_right _ ha
      calc
        _ ≤ ∑' index : ℕ, (1 / 2 : ℝ) ^ index :=
          (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
            (by norm_num : (1 / 2 : ℝ) < 1)).sum_le_tsum _ (fun _ _ => by positivity)
        _ = 2 := by
          rw [tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
            (by norm_num : (1 / 2 : ℝ) < 1)]
          norm_num

end

end AFT.RepresentedPolynomial
