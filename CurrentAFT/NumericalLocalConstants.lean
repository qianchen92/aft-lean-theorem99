import CurrentAFT.PolynomialErrorEnvelope
import CurrentAFT.RationalLegBackgroundProgram
import CurrentAFT.RationalSingletonProgram

/-! Polynomial growth of the literal mixed-data local approximation errors.
The fixed order may affect the polynomial; precision still grows in security. -/
namespace CurrentAFT.NumericalLocalConstants
open AFT PolynomialErrorEnvelope
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.dimension Parameters.bodySize

local macro "finish_envelope" : tactic => `(tactic|
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.base
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.dimension
    | exact PolynomialErrorEnvelope.legs
    | exact PolynomialErrorEnvelope.body
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow
    | apply PolynomialErrorEnvelope.neg
    | apply PolynomialErrorEnvelope.sub)

theorem first_inverse : PolynomialErrorEnvelope RationalFirstResponseProgram.inverseErrorConstant := by
  unfold RationalFirstResponseProgram.inverseErrorConstant
  finish_envelope

theorem inverse_bound : PolynomialErrorEnvelope RationalDensityInverseProgram.inverseBound := by
  unfold RationalDensityInverseProgram.inverseBound
  finish_envelope

theorem mass_lift : PolynomialErrorEnvelope RationalMassLiftProgram.errorConstant := by
  have hf := first_inverse
  have hi := inverse_bound
  unfold RationalMassLiftProgram.errorConstant
  finish_envelope

theorem density_inverse : PolynomialErrorEnvelope RationalDensityInverseProgram.errorConstant := by
  have hf := first_inverse
  have hi := inverse_bound
  unfold RationalDensityInverseProgram.errorConstant
  finish_envelope

theorem tensor_bound : PolynomialErrorEnvelope RationalTensorInverseProgram.actualBound := by
  have hi := inverse_bound
  unfold RationalTensorInverseProgram.actualBound
  finish_envelope

theorem center_error : PolynomialErrorEnvelope RationalBackgroundDensities.centerErrorConstant := by
  unfold RationalBackgroundDensities.centerErrorConstant
  finish_envelope

theorem body_error : PolynomialErrorEnvelope RationalBackgroundDensities.bodyErrorConstant := by
  have hc := center_error
  unfold RationalBackgroundDensities.bodyErrorConstant
  finish_envelope

theorem primary_error : PolynomialErrorEnvelope RationalBackgroundDensities.primaryErrorConstant := by
  have hm := mass_lift
  have ht := tensor_bound
  unfold RationalBackgroundDensities.primaryErrorConstant
  finish_envelope

theorem residual_error : PolynomialErrorEnvelope RationalBackgroundDensities.residualErrorConstant := by
  have hm := mass_lift
  have ht := tensor_bound
  unfold RationalBackgroundDensities.residualErrorConstant
  finish_envelope

theorem free_error : PolynomialErrorEnvelope RationalBackgroundProgram.freeErrorConstant := by
  exact primary_error.add body_error

theorem translation_error : PolynomialErrorEnvelope RationalBackgroundProgram.translationErrorConstant := by
  have hp := primary_error
  have hr := residual_error
  have hb := body_error
  unfold RationalBackgroundProgram.translationErrorConstant
  finish_envelope

theorem coordinate_factor (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalActualFamilyApproximation.coordinateFactor security order) := by
  unfold RationalActualFamilyApproximation.coordinateFactor
  finish_envelope

theorem translation_bound (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalBackgroundLinearProgram.translationBound security order) := by
  unfold RationalBackgroundLinearProgram.translationBound
  finish_envelope

theorem mean_error (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalBackgroundLinearProgram.meanErrorConstant security order) := by
  exact translation_error.add (translation_bound order)

theorem free_mass : PolynomialErrorEnvelope ProposalPrimary.freeMass := by
  unfold ProposalPrimary.freeMass
  finish_envelope

theorem linear_error (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalBackgroundLinearProgram.linearErrorConstant security order) := by
  apply (free_mass.mul free_error |>.add (PolynomialErrorEnvelope.modulus.mul (mean_error order))).div_ge_one
  intro security
  have hl : 0 < Parameters.legCount security := by
    rw [Parameters.legCount_eq]
    exact pow_pos (Parameters.base_pos security) _
  exact_mod_cast hl

theorem primary_deviation : PolynomialErrorEnvelope RationalPrimaryDeviationProgram.errorConstant := by
  have hm := mass_lift
  have ht := tensor_bound
  unfold RationalPrimaryDeviationProgram.errorConstant RationalPrimaryDeviationProgram.profileErrorConstant
  finish_envelope

theorem marked_seed : PolynomialErrorEnvelope RationalMarkedSeedProgram.inverseErrorConstant := by
  have hi := density_inverse
  have ht := tensor_bound
  have hb := body_error
  unfold RationalMarkedSeedProgram.inverseErrorConstant
  simp only [RationalMarkedSeedProgram.profileBound,
    RationalMarkedSeedProgram.seedErrorConstant, RationalMarkedSeedProgram.meanErrorConstant,
    RationalMarkedSeedProgram.uniformErrorConstant, RationalMarkedSeedProgram.primaryErrorConstant]
  finish_envelope

theorem marked_pair (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalMarkedPairProgram.errorConstant security order) := by
  have hm := marked_seed
  have hp := primary_deviation
  have hf := free_error
  have hc := coordinate_factor order
  simp only [RationalMarkedPairProgram.errorConstant, RationalMarkedPairProgram.primaryBound,
    RationalMarkedPairProgram.freeBound, RationalActualFamilyApproximation.productError]
  finish_envelope

theorem conditional_pair : PolynomialErrorEnvelope RationalConditionalPairProgram.errorConstant := by
  have hm := mass_lift
  have ht := tensor_bound
  unfold RationalConditionalPairProgram.errorConstant
  simp only [RationalConditionalPairProgram.computedBound,
    RationalConditionalPairProgram.profileErrorConstant]
  finish_envelope

theorem diffuse_pair : PolynomialErrorEnvelope RationalDiffuseFamilyProgram.errorConstant := by
  have hm := mass_lift
  have ht := tensor_bound
  have hc := center_error
  unfold RationalDiffuseFamilyProgram.errorConstant
  simp only [RationalDiffuseFamilyProgram.primaryErrorConstant,
    RationalDiffuseCertificateProgram.bodyErrorConstant, RationalMassLiftTensorProgram.errorConstant,
    RationalMassLiftTensorProgram.factorBound, RationalDiffuseResidualProgram.pairBound]
  finish_envelope

theorem pair_quadratic (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalPairQuadraticProgram.errorConstant security order) := by
  have hd := diffuse_pair
  have hm := marked_pair order
  have hc := coordinate_factor order
  simp only [RationalPairQuadraticProgram.errorConstant, RationalPairQuadraticProgram.diffuseBound,
    RationalPairQuadraticProgram.markedBound]
  finish_envelope

theorem complete_leg (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalLegBackgroundProgram.errorConstant security order) := by
  have hl := linear_error order
  have hpair := pair_quadratic order
  have hp := conditional_pair
  have ht := translation_error
  have hb := translation_bound order
  have hc := coordinate_factor order
  simp only [RationalLegBackgroundProgram.errorConstant, RationalLegBackgroundProgram.conditionalQuadraticError,
    RationalLegBackgroundProgram.conditionalCubicError, RationalLegBackgroundProgram.conditionalLinearBound,
    RationalLegBackgroundProgram.pairBound, RationalLegBackgroundProgram.quadraticBound,
    RationalLegBackgroundProgram.cubicBound, RationalActualFamilyApproximation.productError]
  finish_envelope

theorem root_first : PolynomialErrorEnvelope RationalRootProfileProgram.firstErrorConstant := by
  have hm := mass_lift
  have ht := tensor_bound
  unfold RationalRootProfileProgram.firstErrorConstant
  simp only [RationalRootProfileProgram.preRootError,
    RationalRootMassProgram.primaryErrorConstant]
  finish_envelope

theorem root_mean : PolynomialErrorEnvelope RationalRootProfileProgram.meanErrorConstant := by
  have hm := mass_lift
  have ht := tensor_bound
  unfold RationalRootProfileProgram.meanErrorConstant
  simp only [RationalRootProfileProgram.preRootError,
    RationalRootMassProgram.primaryErrorConstant]
  finish_envelope

theorem singleton (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalSingletonProgram.errorConstant security order) := by
  have hf := root_first
  have hm := root_mean
  have ht := tensor_bound
  simp only [RationalSingletonProgram.errorConstant, RationalSingletonProgram.inverseBound,
    RationalSingletonProgram.inverseErrorConstant, RationalFamilyProductProgram.growth,
    RationalSingletonProgram.positiveBound, RationalSingletonProgram.firstBound]
  finish_envelope

theorem complete_leg_negligible (order : ℕ) : Negligible (fun security =>
    RationalLegBackgroundProgram.errorConstant security order*(1/(2 : ℝ)^security)) :=
  (complete_leg order).dyadic

theorem singleton_negligible (order : ℕ) : Negligible (fun security =>
    RationalSingletonProgram.errorConstant security order*(1/(2 : ℝ)^security)) :=
  (singleton order).dyadic

end
end CurrentAFT.NumericalLocalConstants
