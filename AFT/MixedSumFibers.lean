import AFT.MixedTensor
import AFT.FiniteJointExpectation

/-! # Exact split fibers for replacement of one input by a finite output block -/
namespace AFT.MixedKernel
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Left Right Color : Type*} [Fintype Left] [Fintype Right] [Fintype Color]
  [DecidableEq Left] [DecidableEq Right]

theorem fiberSq_sum_apply (p : Left → FiniteDist Color) (q : Right → FiniteDist Color)
    (kernel : (Left → Color) → (Right → Color) → ℝ)
    (first : Finset Left) (second : Finset Right) (values : Left ⊕ Right → Color) :
    fiberSq (Sum.elim p q) (fun word => kernel (word ∘ Sum.inl) (word ∘ Sum.inr))
      (first.disjSum second) values =
    (FiniteDist.independent q).expectation (fun rest => fiberSq p
      (fun word => kernel word (freeze second (values ∘ Sum.inr) rest)) first (values ∘ Sum.inl)) := by
  cases Subsingleton.elim (inferInstance : DecidableEq Left) (Classical.decEq Left)
  cases Subsingleton.elim (inferInstance : DecidableEq Right) (Classical.decEq Right)
  unfold fiberSq FiniteDist.l2Sq
  rw [FiniteDist.expectation_independent_sum,FiniteDist.expectation_comm]
  apply Finset.sum_congr rfl
  intro rest _
  congr 1
  apply Finset.sum_congr rfl
  intro word _
  dsimp only
  rw [freeze_disjSum_left,freeze_disjSum_right]
  rfl

/-- Splitting the finite fixed-set sum preserves all distinct pool rates. -/
theorem activity_sum_expand (leftRate : Left → ℝ) (rightRate : Right → ℝ)
    (p : Left → FiniteDist Color) (q : Right → FiniteDist Color)
    (kernel : (Left ⊕ Right → Color) → ℝ) :
    activity (Sum.elim leftRate rightRate) (Sum.elim p q) kernel =
      (∏ slot,leftRate slot)*(∏ slot,rightRate slot)*
      ∑ first : Finset Left,∑ second : Finset Right,
        (∏ slot ∈ first,leftRate slot)*(∏ slot ∈ second,rightRate slot)*
          fiberNorm (Sum.elim p q) kernel (first.disjSum second) := by
  unfold activity
  rw [← (Finset.sumEquiv (α := Left) (β := Right)).toEquiv.symm.sum_comp,
    Fintype.sum_prod_type,Fintype.prod_sum_type]
  simp only [Sum.elim_inl,Sum.elim_inr]
  congr 1
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  change (∏ slot ∈ first.disjSum second,Sum.elim leftRate rightRate slot)*_ = _
  rw [Finset.prod_disjSum]
  rfl

end
end AFT.MixedKernel
