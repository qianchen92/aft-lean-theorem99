import AFT.ConditionalRepair
import AFT.FiniteExpectationAlgebra
import AFT.CompatibleFibers

/-! # Exact expectations with retained public data and unequal input pools -/
namespace AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {First Second Color : Type*} [Fintype First] [Fintype Second] [Fintype Color]

theorem expectation_joint (law : FiniteDist First) (conditional : First → FiniteDist Second)
    (value : First × Second → ℝ) :
    (joint law conditional).expectation value =
      law.expectation (fun first => (conditional first).expectation (fun second => value (first, second))) := by
  simp only [expectation, joint_weight, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

theorem expectation_independent_sum (first : First → FiniteDist Color) (second : Second → FiniteDist Color)
    (value : (First ⊕ Second → Color) → ℝ) :
    (independent (Sum.elim first second)).expectation value =
      (independent first).expectation (fun left => (independent second).expectation
        (fun right => value (Sum.elim left right))) := by
  unfold expectation independent
  rw [← (Equiv.sumArrowEquivProdArrow First Second Color).symm.sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro left _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro right _
  simp only [Equiv.sumArrowEquivProdArrow, Equiv.coe_fn_symm_mk, Fintype.prod_sum_type,
    Sum.elim_inl, Sum.elim_inr]
  ring

/-- A retained body subset keeps the true product law when all other
centers are integrated, jointly with every retained primary coordinate. -/
theorem joint_embedded_pools_expectation {FullBody : Type*} [Fintype FullBody]
    (primary body : FiniteDist Color) (embedding : Second ↪ FullBody)
    (value : (First ⊕ Second → Color) → ℝ) :
    (joint (independent (fun _ : First => primary)) (fun _ => independent (fun _ : FullBody => body))).expectation
      (fun pair => value (Sum.elim pair.1 (pair.2 ∘ embedding))) =
    (independent (Sum.elim (fun _ : First => primary) (fun _ : Second => body))).expectation value := by
  rw [expectation_joint, expectation_independent_sum]
  apply Finset.sum_congr rfl
  intro first _
  congr 1
  exact CanonicalMoments.independent_embedding_expectation_general (fun _ : FullBody => body) embedding
    (fun right => value (Sum.elim first right))

/-- Averaging unchanged public data does not add a cell-probability loss. -/
theorem joint_expectation_difference_le (publicLaw : FiniteDist First)
    (first second : First → FiniteDist Second) (value : First × Second → ℝ)
    (bound : First → ℝ)
    (hbound : ∀ index, |(first index).expectation (fun point => value (index, point)) -
      (second index).expectation (fun point => value (index, point))| ≤ bound index) :
    |(joint publicLaw first).expectation value - (joint publicLaw second).expectation value| ≤ publicLaw.expectation bound := by
  rw [expectation_joint, expectation_joint]
  unfold expectation
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro index _
  rw [← mul_sub, abs_mul, abs_of_nonneg (publicLaw.nonneg index)]
  exact mul_le_mul_of_nonneg_left (hbound index) (publicLaw.nonneg index)

end
end AFT.FiniteDist
