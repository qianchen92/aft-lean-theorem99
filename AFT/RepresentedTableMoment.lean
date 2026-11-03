import AFT.RepresentedMonomialMoment
import AFT.FiniteMomentSum
import AFT.FiniteExpectationAlgebra

/-! # Complete finite input-table moments without a term-count loss -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance representedTableMomentSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
variable {Color : Type*} [Fintype Color]

/-- Literal signed control weight, using the actual distinct-index
statistic of each disjoint seed product and its original coefficient. -/
def tableInputStatistic (primaryPool bodyPool : ℕ) (table : Table (InputSeed Color)) :
    ((Fin primaryPool ⊕ Fin bodyPool) → Color) → ℝ :=
  fun word => table.sum fun powers coefficient => coefficient * monomialInputStatistic primaryPool bodyPool powers word

/-- Every fixed even moment is controlled by the original represented
activity. There is no constant depending on the number of monomials. -/
theorem tableInputStatistic_even_moment (primary body : FiniteDist Color)
    (primaryPool bodyPool : ℕ) (hprimary : 0 < primaryPool) (hbody : 0 < bodyPool)
    (radius : ℝ) (hradius : 1 ≤ radius) (table : Table (InputSeed Color))
    (hc : InputTableCanonical primary body table)
    (order : ℕ) (horder : ∀ powers ∈ table.support, finiteControlCount (monomialOccurrences powers) ≤ order)
    (hprimaryLarge : 2 * order ≤ primaryPool) (hbodyLarge : 2 * order ≤ bodyPool)
    (moment : ℕ) (hmoment : 0 < moment) :
    (FiniteDist.independent (Sum.elim (fun _ : Fin primaryPool => primary) (fun _ : Fin bodyPool => body))).expectation
      (fun word => |tableInputStatistic primaryPool bodyPool table word| ^ (2 * moment)) ≤
      (representedInputMomentConstant order moment * activity (inputWeight primary body primaryPool bodyPool radius) table) ^ (2 * moment) := by
  let law := FiniteDist.independent (Sum.elim (fun _ : Fin primaryPool => primary) (fun _ : Fin bodyPool => body))
  let weight := inputWeight primary body primaryPool bodyPool radius
  let value (term : table.support) (word) := MvPolynomial.coeff term.val table * monomialInputStatistic primaryPool bodyPool term.val word
  let bound (term : table.support) := |MvPolynomial.coeff term.val table| *
    (representedInputMomentConstant order moment * monomialWeight weight term.val)
  have hn (term : table.support) : 0 ≤ bound term := mul_nonneg (abs_nonneg _)
    (mul_nonneg (representedInputMomentConstant_nonneg order moment)
      (monomialWeight_nonneg weight (fun seed => inputWeight_nonneg _ _ _ _ _ seed (le_trans zero_le_one hradius)) _))
  have hm (term : table.support) : law.expectation (fun word => |value term word| ^ (2 * moment)) ≤ bound term ^ (2 * moment) := by
    have ht := monomialInputStatistic_even_moment primary body primaryPool bodyPool hprimary hbody radius hradius term.val
      (hc term.val term.property) order (horder term.val term.property) hprimaryLarge hbodyLarge moment hmoment
    dsimp only [value, bound]
    simp only [abs_mul, mul_pow]
    rw [FiniteDist.expectation_const_mul]
    simpa only [mul_pow] using mul_le_mul_of_nonneg_left ht (pow_nonneg (abs_nonneg (MvPolynomial.coeff term.val table)) (2 * moment))
  have hh := FiniteDist.expectation_abs_sum_pow_le law value bound hn (2 * moment) (by omega) hm
  have hvalue (word) : (∑ term : table.support, value term word) = tableInputStatistic primaryPool bodyPool table word := by
    exact Finset.sum_coe_sort table.support (fun powers => MvPolynomial.coeff powers table * monomialInputStatistic primaryPool bodyPool powers word)
  have hbound : (∑ term : table.support, bound term) =
      representedInputMomentConstant order moment * activity weight table := by
    calc
      _ = ∑ powers ∈ table.support, |MvPolynomial.coeff powers table| *
          (representedInputMomentConstant order moment * monomialWeight weight powers) :=
        Finset.sum_coe_sort table.support _
      _ = _ := by
        unfold activity Finsupp.sum
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro powers _
        simp only [MvPolynomial.coeff]
        ring
  simpa only [hvalue, hbound] using hh

/-- Truncation supplies the actual monomial input-order bound automatically. -/
theorem truncated_tableInputStatistic_even_moment (primary body : FiniteDist Color)
    (primaryPool bodyPool : ℕ) (hprimary : 0 < primaryPool) (hbody : 0 < bodyPool)
    (radius : ℝ) (hradius : 1 ≤ radius) (table : Table (InputSeed Color))
    (hc : InputTableCanonical primary body table) (order : ℕ)
    (hprimaryLarge : 2 * order ≤ primaryPool) (hbodyLarge : 2 * order ≤ bodyPool)
    (moment : ℕ) (hmoment : 0 < moment) :
    (FiniteDist.independent (Sum.elim (fun _ : Fin primaryPool => primary) (fun _ : Fin bodyPool => body))).expectation
      (fun word => |tableInputStatistic primaryPool bodyPool
        (truncate (fun seed => seed.primaryOrder + seed.bodyOrder) order table) word| ^ (2 * moment)) ≤
      (representedInputMomentConstant order moment * activity (inputWeight primary body primaryPool bodyPool radius) table) ^ (2 * moment) := by
  apply (tableInputStatistic_even_moment primary body primaryPool bodyPool hprimary hbody radius hradius _
    (hc.truncate _ order) order (fun powers hp => truncated_monomial_order_le table order powers hp)
    hprimaryLarge hbodyLarge moment hmoment).trans
  apply pow_le_pow_left₀ (mul_nonneg (representedInputMomentConstant_nonneg _ _)
    (activity_nonneg _ (fun seed => inputWeight_nonneg _ _ _ _ _ seed (le_trans zero_le_one hradius)) _))
  exact mul_le_mul_of_nonneg_left (activity_truncate_le _
    (fun seed => inputWeight_nonneg _ _ _ _ _ seed (le_trans zero_le_one hradius)) _ _ _) (representedInputMomentConstant_nonneg _ _)

end
end AFT.RepresentedPolynomial
