import CurrentAFT.RationalFullResponseApproximation

/-! All losses in the literal bounded response calculation are polynomial
at each fixed order; linear precision therefore gives negligible entry error. -/
namespace CurrentAFT.RationalFullResponseProgram
open AFT GradedControlAlgebra RationalActualFamilyApproximation PolynomialErrorEnvelope
noncomputable section
set_option maxHeartbeats 1600000
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize Parameters.dimension

theorem error_polynomial (order : ℕ) : PolynomialErrorEnvelope (fun security => errorConstant security order) := by
  have hB := RationalPackedRootProgram.responseBound_polynomial order
  have hE := RationalPackedRootProgram.error_polynomial order
  have hfB := NumericalPopulationConstants.actual_bound order
  have hfE := NumericalPopulationConstants.complete order
  have hc : PolynomialErrorEnvelope RationalRootMassProgram.primaryErrorConstant := by
    change PolynomialErrorEnvelope (fun security => RationalRootMassProgram.primaryErrorConstant security)
    simp only [RationalRootMassProgram.primaryErrorConstant]
    repeat' first
      | exact PolynomialErrorEnvelope.base
      | exact PolynomialErrorEnvelope.dimension
      | exact PolynomialErrorEnvelope.constant _
      | apply PolynomialErrorEnvelope.mul
  simp only [errorConstant, responseError, fixedQueueError, fixedQueueBound, productError, rootBound,
    rootError, tagCountBound, RationalPackedRootProgram.kernelErrorBound]
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.body
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow

theorem error_negligible (order : ℕ) : Negligible
    (fun security => errorConstant security order*(1/(2:ℝ)^security)) := (error_polynomial order).dyadic

end
end CurrentAFT.RationalFullResponseProgram
