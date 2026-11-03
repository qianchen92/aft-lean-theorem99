import CurrentAFT.NumericalUnselectedConstants
import CurrentAFT.RationalRootGroupBounds

/-! Polynomial bounds on the actual constants of all five grouped columns.
The order is fixed before the security parameter; no final error estimate
is supplied as a hypothesis. -/
namespace CurrentAFT.NumericalGroupConstants
open AFT PolynomialErrorEnvelope NumericalLocalConstants
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1400000
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
    | apply PolynomialErrorEnvelope.absolute
    | apply PolynomialErrorEnvelope.add
    | apply PolynomialErrorEnvelope.mul
    | apply PolynomialErrorEnvelope.pow
    | apply PolynomialErrorEnvelope.neg
    | apply PolynomialErrorEnvelope.sub)

theorem normalized_error (degree : ℕ) (bound profileError : ℕ → ℝ)
    (hb : PolynomialErrorEnvelope bound) (he : PolynomialErrorEnvelope profileError) :
    PolynomialErrorEnvelope (fun security => RationalCoefficientExtraction.normalizedError security degree (bound security) (profileError security)) := by
  have ht := tensor_bound
  have hi := density_inverse
  simp only [RationalCoefficientExtraction.normalizedError, RationalCoefficientExtraction.extractionBound,
    RationalCoefficientExtraction.extractionError, RationalTensorInverseProgram.tensorErrorConstant,
    RationalTensorInverseProgram.factorBound, RationalCoefficientExtraction.atomErrorConstant,
    RationalRootMassProgram.primaryErrorConstant]
  finish_envelope

theorem positive_reference : PolynomialErrorEnvelope RationalPositiveReferenceProgram.errorConstant := by
  unfold RationalPositiveReferenceProgram.errorConstant
  simp only [RationalPositiveReferenceProgram.fixedErrorConstant, RationalRootMassProgram.primaryErrorConstant]
  finish_envelope

theorem positive_family : PolynomialErrorEnvelope RationalPositiveFamilyProgram.errorConstant := by
  unfold RationalPositiveFamilyProgram.errorConstant
  apply PolynomialErrorEnvelope.sum
  intro selected _
  exact normalized_error selected.card (fun _ => 1) RationalPositiveReferenceProgram.errorConstant
    (constant 1) positive_reference

theorem primary_mass : PolynomialErrorEnvelope RationalPrimaryColumnProgram.massErrorConstant := by
  unfold RationalPrimaryColumnProgram.massErrorConstant
  simp only [RationalRootMassProgram.primaryMassErrorConstant, RationalRootMassProgram.fixedErrorConstant,
    RationalRootMassProgram.weightedErrorConstant, RationalRootMassProgram.primaryErrorConstant]
  finish_envelope

theorem numerator_error : PolynomialErrorEnvelope RationalLocalFamilyProgram.numeratorErrorConstant := by
  unfold RationalLocalFamilyProgram.numeratorErrorConstant
  apply PolynomialErrorEnvelope.sum
  intro selected _
  exact normalized_error selected.card (fun security => 2*(Parameters.modulus security : ℝ)^2)
    RationalPrimaryColumnProgram.massErrorConstant ((constant 2).mul (PolynomialErrorEnvelope.modulus.pow 2)) primary_mass

theorem numerator_bound : PolynomialErrorEnvelope LocalCoefficientPointBounds.numeratorBound := by
  have ht := tensor_bound
  unfold LocalCoefficientPointBounds.numeratorBound
  simp only [LocalCoefficientPointBounds.selectedBound]
  finish_envelope

theorem positive_bound (order : ℕ) : PolynomialErrorEnvelope (fun security => PositiveFamilyPointBound.bound security order) := by
  unfold PositiveFamilyPointBound.bound
  finish_envelope

theorem primary_inverse_bound (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalNormalizedPrimaryProgram.inverseBound security order) := by
  have hp := positive_bound order
  simp only [RationalNormalizedPrimaryProgram.inverseBound, RationalFamilyProductProgram.growth]
  finish_envelope

theorem primary_inverse_error (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalNormalizedPrimaryProgram.inverseErrorConstant security order) := by
  have hp := positive_bound order
  have he := positive_family
  simp only [RationalNormalizedPrimaryProgram.inverseErrorConstant, RationalFamilyProductProgram.growth]
  finish_envelope

theorem primary_error (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalNormalizedPrimaryProgram.primaryErrorConstant security order) := by
  have hn := numerator_bound
  have he := numerator_error
  have hib := primary_inverse_bound order
  have hie := primary_inverse_error order
  simp only [RationalNormalizedPrimaryProgram.primaryErrorConstant]
  finish_envelope

theorem singleton_inverse_bound (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalSingletonProgram.inverseBound security order) := by
  have ht := tensor_bound
  simp only [RationalSingletonProgram.inverseBound, RationalSingletonProgram.positiveBound,
    RationalSingletonProgram.firstBound, RationalFamilyProductProgram.growth]
  finish_envelope

theorem singleton_inverse_error (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalSingletonProgram.inverseErrorConstant security order) := by
  have ht := tensor_bound
  have he := root_mean
  simp only [RationalSingletonProgram.inverseErrorConstant, RationalSingletonProgram.positiveBound,
    RationalSingletonProgram.firstBound, RationalFamilyProductProgram.growth]
  finish_envelope

theorem ordinary_profile : PolynomialErrorEnvelope RationalOrdinaryProfileProgram.errorConstant := by
  have hm := mass_lift
  have ht := tensor_bound
  have hc := center_error
  unfold RationalOrdinaryProfileProgram.errorConstant
  simp only [RationalOrdinaryProfileProgram.profileErrorConstant]
  finish_envelope

theorem ordinary_at_root_bound (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalOrdinaryFamilyProgram.atRootBound security order) := by
  have ht := tensor_bound
  have hi := singleton_inverse_bound order
  simp only [RationalOrdinaryFamilyProgram.atRootBound]
  finish_envelope

theorem ordinary_error (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalOrdinaryFamilyProgram.errorConstant security order) := by
  have ht := tensor_bound
  have hi := singleton_inverse_bound order
  have hie := singleton_inverse_error order
  have ho := ordinary_profile
  have hb := ordinary_at_root_bound order
  have hc := center_error
  simp only [RationalOrdinaryFamilyProgram.errorConstant, RationalOrdinaryFamilyProgram.meanError,
    RationalOrdinaryFamilyProgram.atRootError, RationalOrdinaryFamilyProgram.independentError,
    RationalActualFamilyApproximation.productError]
  finish_envelope

theorem error (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalRootGroupProgram.errorConstant security order) := by
  have hp := primary_error order
  have ho := ordinary_error order
  have hl := NumericalUnselectedConstants.unselected_leg order
  have hs := singleton order
  simp only [RationalRootGroupProgram.errorConstant]
  finish_envelope

theorem point_bound (order : ℕ) : PolynomialErrorEnvelope
    (fun security => RationalRootGroupProgram.pointBound security order) := by
  have hn := numerator_bound
  have hip := primary_inverse_bound order
  have his := singleton_inverse_bound order
  have ho := ordinary_at_root_bound order
  have hnl := NumericalUnselectedConstants.numerator_bound
  have hil := NumericalUnselectedConstants.inverse_bound order
  have ht := tensor_bound
  simp only [RationalRootGroupProgram.pointBound, RationalRootGroupProgram.primaryBound,
    RationalRootGroupProgram.ordinaryBound, RationalRootGroupProgram.legBound,
    RationalRootGroupProgram.singletonBound, RationalSingletonProgram.firstBound]
  finish_envelope

theorem error_negligible (order : ℕ) : Negligible (fun security =>
    RationalRootGroupProgram.errorConstant security order*(1/(2 : ℝ)^security)) := (error order).dyadic

end
end CurrentAFT.NumericalGroupConstants
