import CurrentAFT.RootSingletonTensor

/-! # Actual population and cycle-tag budget for joint singleton corrections -/
namespace CurrentAFT.RootSingletonBudget
open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlNorm
  GradedControlAlgebra GradedControlNorm BackgroundRates CycleSelections CycleRootExpansion
  RootTaggedLocal UniformBodyProfiles RootSingletonTensor
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize primaryLaw bodyReference rootReference

theorem singleton_budget (security : ℕ) :
    (Parameters.bodySize security : ℝ) * (primaryFactor security * rootCost security) * currentRootTag security ≤
      (131074 * 4128 : ℝ) / (Parameters.base security : ℝ) ^ 13 := by
  have hb := FirstResponse.base_pos security
  have hbodyNat : Parameters.bodySize security ≤ 131074 * Parameters.base security ^ 160 :=
    (Nat.le_add_right _ _).trans (Parameters.dimension_bounds security).2
  have hbody : (Parameters.bodySize security : ℝ) ≤ 131074 * (Parameters.base security : ℝ) ^ 160 := by
    exact_mod_cast hbodyNat
  rw [primaryFactor_eq, currentRootTag_eq]
  calc
    _ ≤ (131074 * (Parameters.base security : ℝ) ^ 160) *
        (1 / (Parameters.base security : ℝ) ^ 64 * (4128 / (Parameters.base security : ℝ) ^ 30)) *
          (1 / (Parameters.base security : ℝ) ^ 79) := by
      gcongr
      · exact mul_nonneg (by positivity) (rootCost_nonneg security)
      · exact rootCost_decay security
    _ = _ := by field_simp

/-- The input is the complete actual selected-root density. Population
counting offsets only the proved tiny singleton channel and the real root
tag; it does not replace the joint density by a product of marginals. -/
theorem population_scaled_norm (security order count : ℕ) (hcount : count ≤ order)
    (hpositive : 1 ≤ count) (hbody : 2 * count ≤ Parameters.bodySize security)
    (labels : CycleSelections.Selection (Parameters.bodySize security) count)
    (roles : Fin count → BodyRole) (queues : Fin count → ℤ) :
    (Parameters.bodySize security : ℝ) ^ count *
      familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
        (tensorFamily security order count hcount roles queues (selectedCoefficient security count labels)) ≤
      (((2 * (count + 1) : ℕ) : ℝ) ^ count) *
        ((131074 * 4128 : ℝ) / (Parameters.base security : ℝ) ^ 13) ^ count := by
  have hp : 0 ≤ primaryFactor security := by unfold primaryFactor; positivity
  have hc := rootCost_nonneg security
  have ht : 0 ≤ currentRootTag security := by rw [currentRootTag_eq]; positivity
  have hlocal := tensorFamily_norm security order count hcount roles queues
    (selectedCoefficient security count labels)
  have hroot := selectedCoefficient_norm security count hpositive hbody labels
  calc
    _ ≤ (Parameters.bodySize security : ℝ) ^ count *
        ((primaryFactor security * rootCost security) ^ count *
          ((((2 * (count + 1) : ℕ) : ℝ) ^ count) * currentRootTag security ^ count)) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Nat.cast_nonneg _) _)
      apply hlocal.trans
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (mul_nonneg hp hc) _)
      convert hroot using 1
      congr 3 <;> exact Subsingleton.elim _ _
    _ = (((2 * (count + 1) : ℕ) : ℝ) ^ count) *
        ((Parameters.bodySize security : ℝ) * (primaryFactor security * rootCost security) * currentRootTag security) ^ count := by
      simp only [mul_pow]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hp hc)) ht)
        (singleton_budget security) count) (pow_nonneg (Nat.cast_nonneg _) _)

end
end CurrentAFT.RootSingletonBudget
