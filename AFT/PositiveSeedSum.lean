import AFT.RepresentedPolynomial

/-! # Exact activity for positive sums of literal seed variables -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Seed Index : Type*}

theorem activity_eq_eval_of_coeff_nonneg (weight : Seed → ℝ) (table : Table Seed)
    (hcoeff : ∀ powers, 0 ≤ MvPolynomial.coeff powers table) :
    activity weight table = MvPolynomial.eval weight table := by
  simp only [activity, MvPolynomial.sum_def, MvPolynomial.eval_eq, monomialWeight, Finsupp.prod]
  apply Finset.sum_congr rfl
  intro powers _
  rw [abs_of_nonneg (hcoeff powers)]

/-- Labels may collide: their positive coefficients still add exactly. -/
theorem activity_sum_X (weight : Seed → ℝ) (seeds : Index → Seed) (indices : Finset Index) :
    activity weight (∑ index ∈ indices, MvPolynomial.X (seeds index) : Table Seed) =
      ∑ index ∈ indices, weight (seeds index) := by
  rw [activity_eq_eval_of_coeff_nonneg]
  · simp
  · intro powers
    simp only [MvPolynomial.coeff_sum]
    exact Finset.sum_nonneg fun index _ => by
      rw [MvPolynomial.coeff_X']
      split_ifs <;> norm_num
end
end AFT.RepresentedPolynomial
