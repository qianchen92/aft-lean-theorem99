import AFT.RootBodyCosts

/-! # Finite source-set budgets without a cardinality loss -/
namespace AFT.RootTensor
open scoped BigOperators Classical
noncomputable section
variable {Index : Type*} [Fintype Index] [DecidableEq Index]

/-- Every source subset of size at least two is accounted for exactly in
the product expansion, after removing the empty and singleton terms. -/
theorem source_sets_expansion (cost : Index → ℝ) :
    (∑ selected : Finset Index,if 2≤selected.card then ∏ index ∈ selected,cost index else 0) =
      (∏ index,(1+cost index))-1-∑ index,cost index := by
  have hzero : (∑ selected : Finset Index,if selected.card=0 then ∏ index ∈ selected,cost index else 0)=1 := by
    simp only [Finset.card_eq_zero]
    simp
  have hone : (∑ selected : Finset Index,if selected.card=1 then ∏ index ∈ selected,cost index else 0)=∑ index,cost index := by
    rw [← Finset.sum_filter]
    have hsets : (Finset.univ : Finset (Finset Index)).filter (fun selected => selected.card=1) =
        Finset.univ.powersetCard 1 := by ext selected; simp
    rw [hsets,Finset.powersetCard_one,Finset.sum_map]
    simp only [Function.Embedding.coeFn_mk,Finset.prod_singleton]
  have hsplit : (∑ selected : Finset Index,∏ index ∈ selected,cost index) =
      (∑ selected : Finset Index,if selected.card=0 then ∏ index ∈ selected,cost index else 0)+
      (∑ selected : Finset Index,if selected.card=1 then ∏ index ∈ selected,cost index else 0)+
      (∑ selected : Finset Index,if 2≤selected.card then ∏ index ∈ selected,cost index else 0) := by
    rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro selected _
    by_cases hz : selected.card=0
    · simp [hz]
    · by_cases ho : selected.card=1
      · simp [ho]
      · have ht : 2≤selected.card := by omega
        simp only [if_neg hz,if_neg ho,if_pos ht,zero_add]
  have hexp : (∏ index,(1+cost index)) = ∑ selected : Finset Index,∏ index ∈ selected,cost index := by
    simpa only [Finset.prod_const_one,mul_one,add_comm] using Fintype.prod_add cost (fun _ => (1 : ℝ))
  rw [hzero,hone] at hsplit
  linarith

/-- The complete finite source sum is quadratic in the sum of the allocated
local costs. Its proof includes every subset, so no hidden population
power occurs in the source enumeration. -/
theorem source_sets_quadratic (cost : Index → ℝ) (hc : ∀ index,0≤cost index)
    (hsmall : (∑ index,cost index)≤1) :
    (∑ selected : Finset Index,if 2≤selected.card then ∏ index ∈ selected,cost index else 0) ≤
      (∑ index,cost index)^2 := by
  have hsum0 : 0≤∑ index,cost index := Finset.sum_nonneg fun index _ => hc index
  have hprod : (∏ index,(1+cost index)) ≤ Real.exp (∑ index,cost index) := by
    rw [Real.exp_sum]
    exact Finset.prod_le_prod (fun index _ => by linarith [hc index])
      (fun index _ => by linarith [Real.add_one_le_exp (cost index)])
  have he := Real.abs_exp_sub_one_sub_id_le
    (show |∑ index,cost index|≤1 by rw [abs_of_nonneg hsum0]; exact hsmall)
  rw [source_sets_expansion]
  exact (sub_le_sub_right (sub_le_sub_right hprod 1) _).trans ((le_abs_self _).trans he)

/-- Arbitrary nonnegative coefficients attached to a finite-order source
expansion may be bounded after, rather than before, summing source sets. -/
theorem source_sets_weighted_quadratic (cost : Index → ℝ) (coefficient : Finset Index → ℝ)
    (bound : ℝ) (hc : ∀ index,0≤cost index) (hb : 0≤bound)
    (hcoefficient : ∀ selected,2≤selected.card → coefficient selected≤bound)
    (hsmall : (∑ index,cost index)≤1) :
    (∑ selected : Finset Index,if 2≤selected.card then
      coefficient selected*(∏ index ∈ selected,cost index) else 0) ≤
      bound*(∑ index,cost index)^2 := by
  calc
    _ ≤ ∑ selected : Finset Index,if 2≤selected.card then bound*(∏ index ∈ selected,cost index) else 0 := by
      apply Finset.sum_le_sum
      intro selected _
      split_ifs with hs
      · exact mul_le_mul_of_nonneg_right (hcoefficient selected hs) (Finset.prod_nonneg fun index _ => hc index)
      · rfl
    _ = bound*(∑ selected : Finset Index,if 2≤selected.card then ∏ index ∈ selected,cost index else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro selected _
      split_ifs <;> simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (source_sets_quadratic cost hc hsmall) hb

end
end AFT.RootTensor
