import CurrentAFT.PublicOutputExperiment
import CurrentAFT.PhysicalMoments
import CurrentAFT.BoundedClipping

/-! # Moments and clipping of the original weight on its actual public reference -/
namespace CurrentAFT.PublicWeightMoments
open AFT PublicOutputExperiment PhysicalSynthesis ControlCoordinates ControlNorm BackgroundRates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  ordinaryPool ProposalPrimary.primaryLaw ActualControls.bodyReference

theorem weight_test_expectation (security order : ℕ) (coefficient : ActualControls.Coefficients security order)
    (test : ℝ → ℝ) :
    (reference security).expectation (fun controls => test (actualWeight security order coefficient controls)) =
      kernelMean (groupLaw security) (ActualControls.bodyReference security)
        (fun groups centers => test (coefficientWeight security order (Parameters.legCount security)
          (ordinaryPool security) coefficient groups centers)) := by
  have h := SafeControlGroups.common_expectation security (Parameters.legCount security) (ordinaryPool security)
    (fun groups centers => test (coefficientWeight security order (Parameters.legCount security)
      (ordinaryPool security) coefficient groups centers))
  unfold reference actualWeight
  exact (TensorPublicProjection.independent_decision_expectation _ _ _ _).trans h

theorem actualWeight_even_moment (security order moment : ℕ) (hmoment : 1 ≤ moment)
    (hsecurity : 2 * order ≤ security) (coefficient : ActualControls.Coefficients security order) :
    (reference security).expectation (fun controls => |actualWeight security order coefficient controls - coefficient.1| ^ (2 * moment)) ≤
      (PhysicalMoments.coefficientFactor order moment *
        coefficientNorm (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security)
          order (primaryFactor security) (bodyFactor security) (0, coefficient.2)) ^ (2 * moment) := by
  rw [weight_test_expectation security order coefficient (fun value => |value - coefficient.1| ^ (2 * moment))]
  exact PhysicalMoments.coefficientWeight_even_moment_le security order moment hmoment hsecurity coefficient

theorem actualWeight_clipping (security order moment : ℕ) (hmoment : 1 ≤ moment)
    (hsecurity : 2 * order ≤ security) (coefficient : ActualControls.Coefficients security order)
    (hscalar : coefficient.1 = 1) :
    (reference security).expectation (fun controls =>
      |actualWeight security order coefficient controls - clip (actualWeight security order coefficient controls)|) ≤
      (PhysicalMoments.coefficientFactor order moment *
        coefficientNorm (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security)
          order (primaryFactor security) (bodyFactor security) (0, coefficient.2)) ^ (2 * moment) := by
  apply (clipping_loss_le_even_moment (reference security).weight (actualWeight security order coefficient)
    (reference security).nonneg moment hmoment).trans
  have h := actualWeight_even_moment security order moment hmoment hsecurity coefficient
  rwa [hscalar] at h

end
end CurrentAFT.PublicWeightMoments
