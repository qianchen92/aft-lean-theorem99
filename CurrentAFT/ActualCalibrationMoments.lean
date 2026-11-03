import CurrentAFT.ActualCalibrationSolution
import CurrentAFT.PublicWeightMoments

/-! # Actual calibrated public weight: all fixed moments and bounded clipping

The coefficient family is the concrete solution of the assembled response.
The moment order changes the estimate, not the sampled public weight.
-/
namespace CurrentAFT.ActualCalibrationMoments
open AFT ActualCompleteStability PublicOutputExperiment BackgroundRates ControlNorm
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  ordinaryPool ProposalPrimary.primaryLaw ActualControls.bodyReference

def momentConstant (order moment : ℕ) : ℝ :=
  2 * PhysicalMoments.coefficientFactor order moment * ActualCompleteStability.stabilityConstant order

theorem momentConstant_nonneg (order moment : ℕ) : 0 ≤ momentConstant order moment :=
  mul_nonneg (mul_nonneg (by norm_num) (PhysicalMoments.coefficientFactor_positive order moment).le)
    (ActualCompleteStability.stabilityConstant_nonneg order)

theorem nonconstant_norm (security order : ℕ) (horder : 2 ≤ order) (hsecurity : threshold order horder ≤ security)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security) :
    coefficientNorm (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security)
      order (primaryFactor security) (bodyFactor security)
      (0, (coefficients security order horder hsecurity layout).2) ≤
        2 * ActualCompleteStability.stabilityConstant order / (Parameters.base security : ℝ)^6 := by
  have h := coefficients_sub_one_norm security order horder hsecurity layout
  change coefficientNorm _ _ order _ _
    ((coefficients security order horder hsecurity layout).1 - 1,
      (coefficients security order horder hsecurity layout).2 - 0) ≤ _ at h
  rwa [coefficients_scalar, sub_self, sub_zero] at h

theorem actual_weight_moment (security order : ℕ) (horder : 2 ≤ order) (hsecurity : threshold order horder ≤ security)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (moment : ℕ) (hmoment : 1 ≤ moment) :
    (reference security).expectation (fun controls =>
      |actualWeight security order (coefficients security order horder hsecurity layout) controls - 1| ^ (2 * moment)) ≤
      (momentConstant order moment / (Parameters.base security : ℝ)^6) ^ (2 * moment) := by
  have h := PublicWeightMoments.actualWeight_even_moment security order moment hmoment
    (room security order horder hsecurity) (coefficients security order horder hsecurity layout)
  rw [coefficients_scalar] at h
  apply h.trans
  have hnorm := nonconstant_norm security order horder hsecurity layout
  have hnonneg : 0 ≤ coefficientNorm (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security)
      order (primaryFactor security) (bodyFactor security) (0, (coefficients security order horder hsecurity layout).2) :=
    coefficientNorm_nonneg _ _ order _ _ (RaisingPatternBudget.primaryFactor_pos security).le
      (RaisingPatternBudget.bodyFactor_pos security).le _
  apply (pow_le_pow_left₀ (mul_nonneg (PhysicalMoments.coefficientFactor_positive order moment).le hnonneg)
    (mul_le_mul_of_nonneg_left hnorm (PhysicalMoments.coefficientFactor_positive order moment).le) (2 * moment)).trans_eq
  congr 1
  unfold momentConstant
  ring

theorem actual_weight_clipping (security order : ℕ) (horder : 2 ≤ order) (hsecurity : threshold order horder ≤ security)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (moment : ℕ) (hmoment : 1 ≤ moment) :
    (reference security).expectation (fun controls =>
      |actualWeight security order (coefficients security order horder hsecurity layout) controls -
        clip (actualWeight security order (coefficients security order horder hsecurity layout) controls)|) ≤
      (momentConstant order moment / (Parameters.base security : ℝ)^6) ^ (2 * moment) := by
  exact (clipping_loss_le_even_moment (reference security).weight
    (actualWeight security order (coefficients security order horder hsecurity layout))
    (reference security).nonneg moment hmoment).trans
      (actual_weight_moment security order horder hsecurity layout moment hmoment)

theorem actual_weight_mass_one (security order : ℕ) (horder : 2 ≤ order) (hsecurity : threshold order horder ≤ security)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security) :
    (reference security).expectation (actualWeight security order (coefficients security order horder hsecurity layout)) = 1 := by
  rw [actualWeight_mean, coefficients_scalar]

end
end CurrentAFT.ActualCalibrationMoments
