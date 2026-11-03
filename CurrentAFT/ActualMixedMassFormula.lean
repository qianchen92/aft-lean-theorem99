import CurrentAFT.ActualWeightedFourier

/-! # An instance-independent formula for the actual complete mixture -/
namespace CurrentAFT.ActualWeightedFourier
open AFT DiffuseProfiles ProposalPrimary ActualBlockMean ActualCycleMeanMGF
  ConditionalHistogramMean CoefficientOutputFock ControlCoordinates
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] CycleMeanMGF.classicalFinDecidableEq

theorem mixedMass_retype_formula (security order : ℕ) (hroom : 2 * order ≤ security)
    (layout : RoleIndex security ≃ BodyIndex security)
    (coefficient : ActualControls.Coefficients security order)
    [target : Fintype (FirstHistogram.Scalar security × Equiv.Perm (BodyIndex security))]
    (word : Fin (Parameters.dimension security) → ActualBlockMean.Palette security) :
    mixedMass security order hroom layout coefficient word =
      (FiniteDist.retype (randomizationLaw security)).expectation (fun sample =>
        familyMass security order hroom layout sample.1.val sample.2 coefficient word) := by
  rw [FiniteDist.expectation_retype]
  rfl

end
end CurrentAFT.ActualWeightedFourier
