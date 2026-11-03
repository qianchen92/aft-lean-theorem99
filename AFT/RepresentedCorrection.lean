import AFT.RepresentedSubstitution

/-! # Finite correction in the actual weighted seed representation -/

namespace AFT.RepresentedPolynomial

open scoped BigOperators Classical

noncomputable section

variable {Seed : Type*}

theorem activity_operator_pow_le (weight : Seed → ℝ)
    (operator : Module.End ℝ (Table Seed)) (bound : ℝ) (hbound : 0 ≤ bound)
    (hoperator : ∀ table, activity weight (operator table) ≤ bound * activity weight table)
    (power : ℕ) (table : Table Seed) :
    activity weight ((operator ^ power) table) ≤ bound ^ power * activity weight table := by
  induction power with
  | zero => simp
  | succ power ih =>
    rw [pow_succ', Module.End.mul_apply, pow_succ']
    simpa only [mul_assoc] using (hoperator _).trans (mul_le_mul_of_nonneg_left ih hbound)

/-- The finite inverse is bounded in literal activity even when zero seed
weights prevent using an ordinary normed-ring instance. -/
theorem activity_operator_correction_le_two (weight : Seed → ℝ) (hweight : ∀ seed, 0 ≤ weight seed)
    (error : Module.End ℝ (Table Seed))
    (herror : ∀ table, activity weight (error table) ≤ (1 / 2) * activity weight table)
    (depth : ℕ) (table : Table Seed) :
    activity weight (finiteCorrection error depth table) ≤ 2 * activity weight table := by
  have hneg (input : Table Seed) : activity weight ((-error) input) ≤ (1 / 2) * activity weight input := by
    simpa only [LinearMap.neg_apply, activity_neg] using herror input
  simp only [finiteCorrection, LinearMap.sum_apply]
  apply (activity_sum_le weight hweight _ _).trans
  calc
    _ ≤ ∑ power ∈ Finset.range (depth + 1), (1 / 2 : ℝ)^power * activity weight table :=
      Finset.sum_le_sum fun power _ => activity_operator_pow_le weight (-error) (1 / 2)
        (by norm_num) hneg power table
    _ = (∑ power ∈ Finset.range (depth + 1), (1 / 2 : ℝ)^power) * activity weight table :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ 2 * activity weight table := by
      apply mul_le_mul_of_nonneg_right _ (activity_nonneg weight hweight table)
      calc
        _ ≤ ∑' power : ℕ, (1 / 2 : ℝ)^power :=
          (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
            (by norm_num : (1 / 2 : ℝ) < 1)).sum_le_tsum _ (fun _ _ => by positivity)
        _ = 2 := by
          rw [tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
            (by norm_num : (1 / 2 : ℝ) < 1)]
          norm_num

/-- The next-power residual retains the genuine contraction exponent. -/
theorem activity_operator_correction_residual (weight : Seed → ℝ)
    (error : Module.End ℝ (Table Seed))
    (bound : ℝ) (hbound : 0 ≤ bound)
    (herror : ∀ table, activity weight (error table) ≤ bound * activity weight table)
    (depth : ℕ) (table : Table Seed) :
    activity weight ((1 + error) (finiteCorrection error depth table) - table) ≤
      bound ^ (depth + 1) * activity weight table := by
  rw [finiteCorrection_apply]
  have heq : table - ((-error) ^ (depth + 1)) table - table =
      -(((-error) ^ (depth + 1)) table) := by abel
  rw [heq, activity_neg]
  exact activity_operator_pow_le weight (-error) bound hbound
    (fun input => by simpa only [LinearMap.neg_apply, activity_neg] using herror input) _ table

end

end AFT.RepresentedPolynomial
