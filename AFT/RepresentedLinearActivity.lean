import AFT.RepresentedCorrection

/-! # Column bounds on literal finite table linear operators -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Seed Target : Type*}

theorem activity_linearCombination_le (sourceWeight : Seed → ℝ) (targetWeight : Target → ℝ)
    (htarget : ∀ seed,0 ≤ targetWeight seed)
    (columns : (Seed →₀ ℕ) → Table Target) (bound : ℝ)
    (hcolumns : ∀ powers,activity targetWeight (columns powers) ≤ bound*monomialWeight sourceWeight powers)
    (table : Table Seed) :
    activity targetWeight (Finsupp.linearCombination ℝ columns table) ≤ bound*activity sourceWeight table := by
  rw [Finsupp.linearCombination_apply]
  unfold Finsupp.sum
  apply (activity_sum_le targetWeight htarget _ _).trans
  calc
    _ ≤ ∑ powers ∈ table.support,|MvPolynomial.coeff powers table| *(bound*monomialWeight sourceWeight powers) := by
      apply Finset.sum_le_sum
      intro powers _
      dsimp only
      rw [MvPolynomial.smul_eq_C_mul]
      apply (activity_mul_le targetWeight htarget _ _).trans
      rw [activity_C]
      exact mul_le_mul_of_nonneg_left (hcolumns powers) (abs_nonneg _)
    _ = _ := by
      simp only [activity,Finsupp.sum]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro powers _
      simp only [MvPolynomial.coeff]
      ring

end
end AFT.RepresentedPolynomial
