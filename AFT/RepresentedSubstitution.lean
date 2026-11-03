import AFT.RepresentedOutput

/-! # Activity bounds for actual substitutions of represented input tables -/

namespace AFT.RepresentedPolynomial

open scoped BigOperators Classical

noncomputable section

variable {Seed Target Index : Type*}

theorem activity_prod_le (weight : Seed → ℝ) (hweight : ∀ seed, 0 ≤ weight seed)
    (tables : Index → Table Seed) (indices : Finset Index) :
    activity weight (∏ index ∈ indices, tables index) ≤ ∏ index ∈ indices, activity weight (tables index) := by
  classical
  induction indices using Finset.induction_on with
  | empty => simp
  | @insert index indices hn ih =>
    rw [Finset.prod_insert hn, Finset.prod_insert hn]
    exact (activity_mul_le weight hweight _ _).trans
      (mul_le_mul_of_nonneg_left ih (activity_nonneg weight hweight _))

/-- A literal table substitution whose seed images meet their assigned
weights contracts activity on every joint polynomial. -/
theorem activity_aeval_le (sourceWeight : Seed → ℝ) (targetWeight : Target → ℝ)
    (htarget : ∀ target, 0 ≤ targetWeight target)
    (images : Seed → Table Target)
    (himages : ∀ seed, activity targetWeight (images seed) ≤ sourceWeight seed)
    (table : Table Seed) :
    activity targetWeight (MvPolynomial.aeval images table) ≤ activity sourceWeight table := by
  conv in MvPolynomial.aeval images table => rw [MvPolynomial.as_sum table]
  rw [map_sum]
  apply (activity_sum_le targetWeight htarget _ _).trans
  change _ ≤ ∑ powers ∈ table.support, |MvPolynomial.coeff powers table| * monomialWeight sourceWeight powers
  apply Finset.sum_le_sum
  intro powers _
  rw [MvPolynomial.aeval_monomial]
  change activity targetWeight (MvPolynomial.C (MvPolynomial.coeff powers table) * _) ≤ _
  apply (activity_mul_le targetWeight htarget _ _).trans
  rw [activity_C]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  unfold Finsupp.prod monomialWeight
  apply (activity_prod_le targetWeight htarget _ _).trans
  apply Finset.prod_le_prod
  · intro seed _
    exact activity_nonneg targetWeight htarget _
  · intro seed _
    exact (activity_pow_le targetWeight htarget _ _).trans
      (pow_le_pow_left₀ (activity_nonneg targetWeight htarget _) (himages seed) _)

theorem hasOrder_prod (order : Seed → ℕ) (orders : Index → ℕ)
    (tables : Index → Table Seed) (indices : Finset Index)
    (h : ∀ index ∈ indices, HasOrder order (orders index) (tables index)) :
    HasOrder order (∑ index ∈ indices, orders index) (∏ index ∈ indices, tables index) := by
  classical
  induction indices using Finset.induction_on with
  | empty => simpa using hasOrder_zero order 1
  | @insert index indices hn ih =>
    rw [Finset.sum_insert hn, Finset.prod_insert hn]
    exact hasOrder_mul order _ _ _ _ (h index (Finset.mem_insert_self _ _))
      (ih (fun other ho => h other (Finset.mem_insert_of_mem ho)))

/-- Substitution may increase degrees; it never discards low input-order
information if each actual seed replacement begins at its assigned order. -/
theorem aeval_hasOrder_of_lower_bounds (sourceOrder : Seed → ℕ) (targetOrder : Target → ℕ)
    (images : Seed → Table Target)
    (himages : ∀ seed, HasOrder targetOrder (sourceOrder seed) (images seed))
    (minimum : ℕ) (table : Table Seed) (h : HasOrder sourceOrder minimum table) :
    HasOrder targetOrder minimum (MvPolynomial.aeval images table) := by
  conv in MvPolynomial.aeval images table => rw [MvPolynomial.as_sum table]
  rw [map_sum]
  apply hasOrder_sum
  intro powers hp
  have hmin : minimum ≤ weightedOrder sourceOrder powers := by
    by_contra hlt
    exact (MvPolynomial.mem_support_iff.mp hp) (h powers (by omega))
  apply hasOrder_mono targetOrder minimum (weightedOrder sourceOrder powers) _ _ hmin
  rw [MvPolynomial.aeval_monomial]
  change HasOrder targetOrder _ (MvPolynomial.C _ * _)
  have hprod : HasOrder targetOrder (weightedOrder sourceOrder powers)
      (powers.prod fun seed power => images seed ^ power) := by
    unfold Finsupp.prod weightedOrder Finsupp.sum
    apply hasOrder_prod
    intro seed _
    exact hasOrder_pow targetOrder (sourceOrder seed) (images seed) (himages seed) (powers seed)
  simpa only [zero_add] using hasOrder_mul targetOrder 0 _ _ _ (hasOrder_zero targetOrder _) hprod

end

end AFT.RepresentedPolynomial
