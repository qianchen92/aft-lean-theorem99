import CurrentAFT.RationalFullResponseMatrix
import CurrentAFT.BinaryCalibrationWeightSemantic
import CurrentAFT.BinaryRectangleMaterialization

/-! Numerical stability for the literal full-response entries. The constants
below occur only in error bounds, never in executable sampling. -/
namespace CurrentAFT.RationalFullResponseProgram
open AFT ActualBlockFock GradedControlAlgebra ActualControls FullResponsePointFormula
  CalibrationPrecisionRates CalibratedWeightApproximation CalibrationTableNorm
open Filter
open scoped Classical Topology
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance accuracyFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize Parameters.dimension
  ProposalPrimary.primaryLaw bodyReference

def entryConstant (order : ℕ) : ℝ := Classical.choose (error_polynomial order)
def entryDegree (order : ℕ) : ℕ := Classical.choose (Classical.choose_spec (error_polynomial order))

theorem entry_envelope (order : ℕ) : 0 ≤ entryConstant order ∧
    ∀ security, |errorConstant security order| ≤ entryConstant order*(Parameters.base security:ℝ)^(entryDegree order) :=
  Classical.choose_spec (Classical.choose_spec (error_polynomial order))

def entryError (security order : ℕ) : ℝ := entryBudget (entryConstant order) (entryDegree order) security

def weightError (security order : ℕ) : ℝ := weightBudget security security order security (entryError security order)

theorem entryError_nonneg (security order : ℕ) : 0 ≤ entryError security order :=
  entryBudget_nonneg _ _ _ (entry_envelope order).1

theorem weightError_nonneg (security order : ℕ) : 0 ≤ weightError security order := by
  have hp := pointBudget_nonneg security order security (entryError security order) (entryError_nonneg security order)
  have he := NumericalWeightEvaluation.localError_nonneg security security
  unfold weightError weightBudget NumericalWeightEvaluation.factor encodeFactor
  positivity

theorem entry_error_le (security order : ℕ) :
    errorConstant security order*(1/(2:ℝ)^security) ≤ entryError security order := by
  have h := mul_le_mul_of_nonneg_right ((le_abs_self _).trans ((entry_envelope order).2 security))
    (by positivity : (0:ℝ) ≤ 1/2^security)
  simpa only [entryError, entryBudget, div_pow, one_pow] using h

theorem weightError_negligible (order : ℕ) : Negligible (fun security => weightError security order) :=
  NumericalWeightRates.weightBudget_negligible order (entryConstant order) (entryDegree order) (entry_envelope order).1

theorem body_room (security order : ℕ) (hroom : 2*order ≤ security) : order ≤ Parameters.bodySize security := by
  have hb : security ≤ Parameters.base security := by unfold Parameters.base; omega
  have hb1 : 1 ≤ Parameters.base security := (Parameters.base_ge_two security).trans' (by omega)
  have hp : Parameters.base security ≤ Parameters.base security^96 := by
    simpa only [pow_one] using pow_le_pow_right₀ hb1 (by omega : 1 ≤ 96)
  have hq : 1 ≤ Parameters.modulus security := (Parameters.modulus_spec security).2.one_le
  rw [Parameters.bodySize_eq]
  exact (show order ≤ security by omega).trans (hb.trans (hp.trans (by simpa using Nat.mul_le_mul_right (Parameters.base security^96) hq)))

theorem matrix_error_eventually (order : ℕ) (horder : 2 ≤ order) :
    ∀ᶠ security : ℕ in atTop,
      ∀ hsecurity : ActualCompleteStability.threshold order horder ≤ security,
      ∀ (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security) (output source : FullResponsePointFormula.Index security order),
        |(matrix security security order output source:ℝ)-
          LinearMap.toMatrix' (exactDefect security order horder hsecurity layout) output source| ≤ entryError security order := by
  filter_upwards [NumericReferenceBudgets.precision_budgets_eventually] with security hb hsecurity layout output source
  exact (matrix_error security security order horder hsecurity
    (body_room security order (ActualCompleteStability.room security order horder hsecurity)) layout
    hb.2.2 hb.1 hb.2.1 output source).trans (entry_error_le security order)

theorem materialized_weight_error_eventually (order : ℕ) (horder : 2 ≤ order) :
    ∀ᶠ security : ℕ in atTop,
      ∀ hsecurity : ActualCompleteStability.threshold order horder ≤ security,
      ∀ (layout : ConditionalHistogramMean.RoleIndex security ≃ ActualCycleMeanMGF.BodyIndex security)
        (entry : Fin (BinaryRectangleMaterialization.Size security order) → Fin (BinaryRectangleMaterialization.Size security order) →
          AFT.RationalRejectionProgram.CountedValue AFT.BinaryArithmetic.RationalBits),
      (∀ output input, (entry output input).value.decode =
        CurrentRectangleIndex.defect security order (matrix security security order)
          (finProdFinEquiv.symm output) (finProdFinEquiv.symm input)) →
      ∀ core : ActualPublicCharge.Core security,
        |(BinaryPublicRejection.coreWeight security security order
          (BinaryRectangleMaterialization.run security order security entry).value core:ℝ)-
          ActualCalibratedPublic.weight security order horder hsecurity layout core| ≤ weightError security order := by
  filter_upwards [matrix_error_eventually order horder, NumericReferenceBudgets.precision_budgets_eventually,
    small_entries_eventually order (entryConstant order) (entryDegree order) (entry_envelope order).1]
    with security hm hp hs hsecurity layout entry he core
  exact BinaryCalibrationWeightSemantic.coreWeight_error security security order horder hsecurity layout
    (matrix security security order) (BinaryRectangleMaterialization.current security order entry).matrix
    (BinaryRectangleMaterialization.current security order entry).rhs
    (fun output input => by rw [BinaryRectangleMaterialization.matrix_value, he])
    (fun output => by rw [BinaryRectangleMaterialization.rhs_value, BinaryRectangleMaterialization.rhs_flat])
    (entryError security order) (entryError_nonneg security order)
    (hm hsecurity (ActualLayouts.blockLayout layout)) hs security hp.1 hp.2.1 core

end
end CurrentAFT.RationalFullResponseProgram
