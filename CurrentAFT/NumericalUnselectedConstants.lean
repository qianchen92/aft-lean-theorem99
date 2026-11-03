import CurrentAFT.NumericalLocalConstants
import CurrentAFT.RationalUnselectedLegNormalized

/-! Polynomial error growth for the original full three-slot root leg. -/
namespace CurrentAFT.NumericalUnselectedConstants
open AFT PolynomialErrorEnvelope NumericalLocalConstants
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.dimension Parameters.bodySize

local macro "finish_envelope" : tactic => `(tactic|
  repeat' first
    | assumption
    | exact PolynomialErrorEnvelope.base
    | exact PolynomialErrorEnvelope.modulus
    | exact PolynomialErrorEnvelope.dimension
    | exact PolynomialErrorEnvelope.constant _
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow
    | apply PolynomialErrorEnvelope.neg
    | apply PolynomialErrorEnvelope.sub)

theorem leg_at_root : PolynomialErrorEnvelope RationalLegMassProgram.atRootErrorConstant := by
  unfold RationalLegMassProgram.atRootErrorConstant
  simp only [RationalPositiveReferenceProgram.fixedErrorConstant, RationalRootMassProgram.primaryErrorConstant]
  finish_envelope

theorem leg_mean : PolynomialErrorEnvelope RationalLegMassProgram.meanErrorConstant := by
  have ha := leg_at_root
  unfold RationalLegMassProgram.meanErrorConstant
  finish_envelope

theorem leg_difference : PolynomialErrorEnvelope RationalLegMassProgram.differenceErrorConstant :=
  leg_at_root.add leg_mean

theorem normalized_error (degree : ℕ) (bound profileError : ℕ → ℝ)
    (hb : PolynomialErrorEnvelope bound) (he : PolynomialErrorEnvelope profileError) :
    PolynomialErrorEnvelope (fun security => RationalLegCoefficientExtraction.normalizedError security degree (bound security) (profileError security)) := by
  have ht := tensor_bound
  have hi := density_inverse
  simp only [RationalLegCoefficientExtraction.normalizedError, RationalLegCoefficientExtraction.extractionBound,
    RationalLegCoefficientExtraction.extractionError, RationalTensorInverseProgram.tensorErrorConstant,
    RationalTensorInverseProgram.factorBound, RationalLegCoefficientExtraction.atomErrorConstant,
    RationalRootMassProgram.primaryErrorConstant]
  finish_envelope

theorem higher_error : PolynomialErrorEnvelope RationalUnselectedLegProgram.higherError := by
  unfold RationalUnselectedLegProgram.higherError RationalLegFamilyTable.higherError
  apply PolynomialErrorEnvelope.sum
  intro selected _
  exact normalized_error selected.card (fun _ => 2) RationalLegMassProgram.differenceErrorConstant
    (constant 2) leg_difference

theorem positive_error : PolynomialErrorEnvelope RationalUnselectedLegProgram.positiveError := by
  unfold RationalUnselectedLegProgram.positiveError RationalLegFamilyTable.positiveError
  apply PolynomialErrorEnvelope.sum
  intro selected _
  exact normalized_error selected.card (fun _ => 1) RationalLegMassProgram.meanErrorConstant (constant 1) leg_mean

theorem selected_bound (bound : ℝ) : PolynomialErrorEnvelope
    (fun security => LegCoefficientPointBounds.selectedBound security bound) := by
  have ht := tensor_bound
  unfold LegCoefficientPointBounds.selectedBound
  finish_envelope

theorem positive_bound : PolynomialErrorEnvelope RationalUnselectedLegProgram.positiveBound := by
  have hb := selected_bound 1
  unfold RationalUnselectedLegProgram.positiveBound
  finish_envelope

theorem inverse_bound (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalUnselectedLegProgram.inverseBound security order) := by
  have hb := positive_bound
  simp only [RationalUnselectedLegProgram.inverseBound, RationalFamilyProductProgram.growth]
  finish_envelope

theorem inverse_error (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalUnselectedLegProgram.inverseError security order) := by
  have hb := positive_bound
  have he := positive_error
  simp only [RationalUnselectedLegProgram.inverseError, RationalFamilyProductProgram.growth]
  finish_envelope

theorem numerator_bound : PolynomialErrorEnvelope RationalUnselectedLegProgram.numeratorBound := by
  have ht := tensor_bound
  have hs := selected_bound 2
  unfold RationalUnselectedLegProgram.numeratorBound
  simp only [RationalSingletonProgram.firstBound]
  finish_envelope

theorem numerator_error : PolynomialErrorEnvelope RationalUnselectedLegProgram.numeratorError :=
  root_first.add higher_error

theorem unselected_leg (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalUnselectedLegProgram.errorConstant security order) := by
  have hn := numerator_bound
  have hi := inverse_bound order
  have he := numerator_error
  have hie := inverse_error order
  simp only [RationalUnselectedLegProgram.errorConstant, RationalActualFamilyApproximation.productError]
  finish_envelope

theorem unselected_leg_negligible (order : ℕ) : Negligible (fun security =>
    RationalUnselectedLegProgram.errorConstant security order*(1/(2 : ℝ)^security)) :=
  (unselected_leg order).dyadic

end
end CurrentAFT.NumericalUnselectedConstants
