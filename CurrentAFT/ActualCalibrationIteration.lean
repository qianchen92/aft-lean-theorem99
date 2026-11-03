import CurrentAFT.ActualCalibrationSolution

/-! # Finite iteration and residual certification for the actual response

These are quantitative error guarantees for the already constructed current
response and its unique solution. The rational implementation of its entries
is a separate obligation; no computation of real numbers is inferred here.
-/
namespace CurrentAFT.ActualCalibrationIteration
open AFT ActualCompleteStability LocalCoefficientFamily ActualControls ProposalPrimary
  BackgroundRates GradedControlNorm GradedControlStability
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
local instance iterationFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

private theorem norm_nonneg (security order : ℕ) (family : Family security order) :
    0 ≤ LocalRaisingBounds.coefficientNorm security order family :=
  familyNorm_nonneg _ _ _ _ _ (RaisingPatternBudget.primaryFactor_pos security).le
    (RaisingPatternBudget.bodyFactor_pos security).le family

theorem residual_bound (security order : ℕ) (horder : 2 ≤ order)
    (hsecurity : threshold order horder ≤ security)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (approximation : Family security order) :
    LocalRaisingBounds.coefficientNorm security order
      (approximation - solution security order horder hsecurity layout) ≤
        2 * LocalRaisingBounds.coefficientNorm security order
          (fullResponse security order horder (room security order horder hsecurity) layout approximation - 1) := by
  have hs := stable security order horder hsecurity layout
  have hbound := family_operator_norm_le (primaryLaw security) (bodyReference security) order
    (primaryFactor security) (bodyFactor security)
    (RaisingPatternBudget.primaryFactor_pos security).le (RaisingPatternBudget.bodyFactor_pos security).le
    (fullResponse security order horder (room security order horder hsecurity) layout) _
    (by linarith [hs.1]) hs.2 (approximation - solution security order horder hsecurity layout)
  rw [map_sub, solution_response] at hbound
  apply hbound.trans
  apply (div_le_iff₀ (by linarith [hs.1] :
    0 < 1 - stabilityConstant order / (Parameters.base security : ℝ)^6)).mpr
  have hn := norm_nonneg security order
    (fullResponse security order horder (room security order horder hsecurity) layout approximation - 1)
  simp only [LocalRaisingBounds.coefficientNorm] at hn ⊢
  nlinarith [mul_le_mul_of_nonneg_right hs.1 hn]

def step (security order : ℕ) (horder : 2 ≤ order)
    (hsecurity : threshold order horder ≤ security)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (family : Family security order) : Family security order :=
  1 + family - fullResponse security order horder (room security order horder hsecurity) layout family

def iterate (security order : ℕ) (horder : 2 ≤ order)
    (hsecurity : threshold order horder ≤ security)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security) : ℕ → Family security order
  | 0 => 0
  | count + 1 => step security order horder hsecurity layout (iterate security order horder hsecurity layout count)

theorem step_error (security order : ℕ) (horder : 2 ≤ order)
    (hsecurity : threshold order horder ≤ security)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (family : Family security order) :
    LocalRaisingBounds.coefficientNorm security order
      (step security order horder hsecurity layout family - solution security order horder hsecurity layout) ≤
        (1 / 2 : ℝ) * LocalRaisingBounds.coefficientNorm security order
          (family - solution security order horder hsecurity layout) := by
  have hs := stable security order horder hsecurity layout
  have heq : step security order horder hsecurity layout family - solution security order horder hsecurity layout =
      (family - solution security order horder hsecurity layout) -
        fullResponse security order horder (room security order horder hsecurity) layout
          (family - solution security order horder hsecurity layout) := by
    rw [map_sub, solution_response]
    unfold step
    abel
  rw [heq]
  exact (hs.2 _).trans (mul_le_mul_of_nonneg_right hs.1 (norm_nonneg security order _))

/-- The iteration count needed for inverse-polynomial accuracy is
logarithmic in that accuracy, in the actual complete coefficient norm. -/
theorem iterate_error (security order : ℕ) (horder : 2 ≤ order)
    (hsecurity : threshold order horder ≤ security)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security) (count : ℕ) :
    LocalRaisingBounds.coefficientNorm security order
      (iterate security order horder hsecurity layout count - solution security order horder hsecurity layout) ≤
        2 * (1 / 2 : ℝ)^count := by
  induction count with
  | zero =>
      simp only [iterate, zero_sub, pow_zero, mul_one]
      rw [show LocalRaisingBounds.coefficientNorm security order (-solution security order horder hsecurity layout) =
        LocalRaisingBounds.coefficientNorm security order (solution security order horder hsecurity layout) from
          familyNorm_neg _ _ _ _ _ _]
      exact solution_norm security order horder hsecurity layout
  | succ count ih =>
      exact (step_error security order horder hsecurity layout _).trans
        ((mul_le_mul_of_nonneg_left ih (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans_eq (by rw [pow_succ]; ring))

end
end CurrentAFT.ActualCalibrationIteration
