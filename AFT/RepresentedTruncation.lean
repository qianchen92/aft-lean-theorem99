import AFT.RepresentedPolynomial

/-!
# Weighted truncation of literal input seed polynomials

The cutoff acts on the sum of the primary and body input orders.  Formal
seed labels remain distinct.  Finite Neumann inversion is exact after this
cutoff, with its activity controlled before and after truncation.
-/

namespace AFT.RepresentedPolynomial

open scoped BigOperators Classical

noncomputable section

variable {Seed : Type*}

def weightedOrder (order : Seed → ℕ) (powers : Seed →₀ ℕ) : ℕ :=
  powers.sum fun seed power => power * order seed

@[simp] theorem weightedOrder_zero (order : Seed → ℕ) : weightedOrder order 0 = 0 := by
  simp [weightedOrder]

theorem weightedOrder_add (order : Seed → ℕ) (first second : Seed →₀ ℕ) :
    weightedOrder order (first + second) = weightedOrder order first + weightedOrder order second :=
  Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

def truncate (order : Seed → ℕ) (cutoff : ℕ) (table : Table Seed) : Table Seed :=
  Finsupp.filter (fun powers => weightedOrder order powers ≤ cutoff) table

@[simp] theorem coeff_truncate (order : Seed → ℕ) (cutoff : ℕ) (table : Table Seed)
    (powers : Seed →₀ ℕ) :
    MvPolynomial.coeff powers (truncate order cutoff table) =
      if weightedOrder order powers ≤ cutoff then MvPolynomial.coeff powers table else 0 := rfl

@[simp] theorem truncate_zero (order : Seed → ℕ) (cutoff : ℕ) :
    truncate order cutoff (0 : Table Seed) = 0 := by
  ext powers
  simp

@[simp] theorem truncate_one (order : Seed → ℕ) (cutoff : ℕ) :
    truncate order cutoff (1 : Table Seed) = 1 := by
  ext powers
  by_cases h : powers = 0
  · subst powers; simp
  · simp [MvPolynomial.coeff_one, Ne.symm h]

theorem truncate_add (order : Seed → ℕ) (cutoff : ℕ) (first second : Table Seed) :
    truncate order cutoff (first + second) = truncate order cutoff first + truncate order cutoff second := by
  ext powers
  simp only [coeff_truncate, MvPolynomial.coeff_add]
  split_ifs <;> simp

theorem truncate_neg (order : Seed → ℕ) (cutoff : ℕ) (table : Table Seed) :
    truncate order cutoff (-table) = -truncate order cutoff table := by
  ext powers
  simp only [coeff_truncate, MvPolynomial.coeff_neg]
  split_ifs <;> simp

theorem truncate_sub (order : Seed → ℕ) (cutoff : ℕ) (first second : Table Seed) :
    truncate order cutoff (first - second) = truncate order cutoff first - truncate order cutoff second := by
  simp only [sub_eq_add_neg, truncate_add, truncate_neg]

@[simp] theorem truncate_idempotent (order : Seed → ℕ) (cutoff : ℕ) (table : Table Seed) :
    truncate order cutoff (truncate order cutoff table) = truncate order cutoff table := by
  ext powers
  simp only [coeff_truncate]
  split_ifs <;> rfl

theorem truncate_mul (order : Seed → ℕ) (cutoff : ℕ) (first second : Table Seed) :
    truncate order cutoff (first * second) =
      truncate order cutoff (truncate order cutoff first * truncate order cutoff second) := by
  ext powers
  simp only [coeff_truncate]
  split_ifs with h
  · simp only [MvPolynomial.coeff_mul]
    apply Finset.sum_congr rfl
    intro pair hpair
    have heq := Finset.mem_antidiagonal.mp hpair
    have hsum : weightedOrder order pair.1 + weightedOrder order pair.2 ≤ cutoff := by
      rw [← weightedOrder_add, heq]
      exact h
    rw [coeff_truncate, coeff_truncate, if_pos (by omega), if_pos (by omega)]
  · rfl

theorem activity_truncate_le (weight : Seed → ℝ) (hweight : ∀ seed, 0 ≤ weight seed)
    (order : Seed → ℕ) (cutoff : ℕ) (table : Table Seed) :
    activity weight (truncate order cutoff table) ≤ activity weight table := by
  change (∑ powers ∈ (Finsupp.filter (fun powers => weightedOrder order powers ≤ cutoff) table).support,
      |MvPolynomial.coeff powers (truncate order cutoff table)| * monomialWeight weight powers) ≤ _
  rw [Finsupp.support_filter]
  calc
    _ = ∑ powers ∈ table.support.filter (fun powers => weightedOrder order powers ≤ cutoff),
        |MvPolynomial.coeff powers table| * monomialWeight weight powers := by
      apply Finset.sum_congr rfl
      intro powers hp
      rw [coeff_truncate, if_pos (Finset.mem_filter.mp hp).2]
    _ ≤ activity weight table := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro powers _ _
      exact mul_nonneg (abs_nonneg _) (monomialWeight_nonneg weight hweight powers)

/-- Every coefficient strictly below the specified weighted order vanishes. -/
def HasOrder (order : Seed → ℕ) (minimum : ℕ) (table : Table Seed) : Prop :=
  ∀ powers, weightedOrder order powers < minimum → MvPolynomial.coeff powers table = 0

theorem hasOrder_zero (order : Seed → ℕ) (table : Table Seed) : HasOrder order 0 table := by
  intro powers h
  omega

theorem hasOrder_neg (order : Seed → ℕ) (minimum : ℕ) (table : Table Seed)
    (h : HasOrder order minimum table) : HasOrder order minimum (-table) := by
  intro powers hp
  simp [h powers hp]

theorem hasOrder_mul (order : Seed → ℕ) (firstOrder secondOrder : ℕ)
    (first second : Table Seed) (hfirst : HasOrder order firstOrder first)
    (hsecond : HasOrder order secondOrder second) :
    HasOrder order (firstOrder + secondOrder) (first * second) := by
  intro powers hp
  rw [MvPolynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro pair hpair
  have heq := Finset.mem_antidiagonal.mp hpair
  have hsum : weightedOrder order pair.1 + weightedOrder order pair.2 < firstOrder + secondOrder := by
    rw [← weightedOrder_add, heq]
    exact hp
  by_cases h : weightedOrder order pair.1 < firstOrder
  · rw [hfirst _ h, zero_mul]
  · rw [hsecond _ (by omega), mul_zero]

theorem hasOrder_pow (order : Seed → ℕ) (minimum : ℕ) (table : Table Seed)
    (h : HasOrder order minimum table) (power : ℕ) :
    HasOrder order (power * minimum) (table ^ power) := by
  induction power with
  | zero => simpa only [zero_mul] using hasOrder_zero order (table ^ 0)
  | succ power ih =>
    rw [pow_succ, Nat.succ_mul]
    exact hasOrder_mul order _ _ _ _ ih h

theorem truncate_of_hasOrder (order : Seed → ℕ) (cutoff : ℕ) (table : Table Seed)
    (h : HasOrder order (cutoff + 1) table) : truncate order cutoff table = 0 := by
  ext powers
  simp only [coeff_truncate, MvPolynomial.coeff_zero]
  split_ifs with hp
  · exact h powers (by omega)
  · rfl

/-- The explicit finite correction is an exact inverse in the truncated
input algebra.  The only hypothesis is absence of order-zero error terms. -/
theorem truncate_finiteCorrection_residual (order : Seed → ℕ) (cutoff : ℕ)
    (error : Table Seed) (herror : HasOrder order 1 error) :
    truncate order cutoff ((1 + error) * finiteCorrection error cutoff) = 1 := by
  rw [finiteCorrection_residual, truncate_sub, truncate_one]
  have hp := hasOrder_pow order 1 (-error) (hasOrder_neg order 1 error herror) (cutoff + 1)
  simp only [mul_one] at hp
  rw [truncate_of_hasOrder order cutoff _ hp, sub_zero]

theorem truncated_inverse_activity (weight : Seed → ℝ) (hweight : ∀ seed, 0 ≤ weight seed)
    (order : Seed → ℕ) (cutoff : ℕ) (error : Table Seed)
    (hsmall : activity weight error ≤ 1 / 2) :
    activity weight (truncate order cutoff (finiteCorrection error cutoff)) ≤ 2 :=
  (activity_truncate_le weight hweight order cutoff _).trans
    (activity_finiteCorrection_le_two weight hweight error cutoff hsmall)

end

end AFT.RepresentedPolynomial
