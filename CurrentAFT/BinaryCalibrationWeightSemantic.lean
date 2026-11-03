import CurrentAFT.BinaryRectangleIteration
import CurrentAFT.BinaryPublicRejection
import CurrentAFT.CalibratedWeightApproximation

/-! The materialized rectangular iterate is read by the actual public-weight
program at the same joint coefficient coordinates. This connects matrix
iteration error to the rejection program's public core weight. -/
namespace CurrentAFT.BinaryCalibrationWeightSemantic
open AFT BinaryArithmetic RationalRejectionProgram
open ActualControls ControlCoordinates GradedControlAlgebra
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  PublicParameterProgram.modulus
noncomputable section
open scoped Classical
local instance finDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

 theorem realTable_read (security order : ℕ)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order)
    (point : CurrentRectangleIndex.Point security order) :
    RationalWeightProgram.realTable security order (BinaryWeightLocal.rawTable security order table) point =
      (((table.get (CurrentRectangleIndex.encode security order point).1).get
        (CurrentRectangleIndex.encode security order point).2).decode : ℝ) := by
  have h := BinaryWeightLocal.rawTable_value security order table point.1
    (fun index => (CurrentRectangleIndex.paletteEquiv security).symm (point.2.1 index))
    (fun index => (CurrentRectangleIndex.paletteEquiv security).symm (point.2.2 index).val)
  exact congrArg (fun value : ℚ => (value : ℝ)) h

 theorem iteration_realTable (security order steps : ℕ)
    (rationalMatrix : CurrentRectangleIndex.Point security order → CurrentRectangleIndex.Point security order → ℚ)
    (matrix : Vector (Vector RationalBits (((order+1)^2)*(CurrentRectangleIndex.colors security)^order))
      (((order+1)^2)*(CurrentRectangleIndex.colors security)^order))
    (rhs : Vector RationalBits (((order+1)^2)*(CurrentRectangleIndex.colors security)^order))
    (hmatrix : ∀ output input, ((matrix.get output).get input).decode =
      CurrentRectangleIndex.defect security order rationalMatrix (finProdFinEquiv.symm output) (finProdFinEquiv.symm input))
    (hrhs : ∀ output, (rhs.get output).decode = CurrentRectangleIndex.rhs security order (finProdFinEquiv.symm output))
    (point : CurrentRectangleIndex.Point security order) :
    RationalWeightProgram.realTable security order (BinaryWeightLocal.rawTable security order
      (BinaryRectangleIteration.run ((order+1)^2) ((CurrentRectangleIndex.colors security)^order) matrix rhs steps).value) point =
      (RationalNumerics.linearIteration rationalMatrix (CalibrationMatrixApproximation.rhs security order) steps point : ℝ) := by
  rw [realTable_read, BinaryRectangleIteration.actual_value security order steps rationalMatrix matrix rhs hmatrix hrhs]

 theorem coreWeight_error (security bits order : ℕ) (horder : 2 ≤ order)
    (hsecurity : ActualCompleteStability.threshold order horder ≤ security)
    (layout : ConditionalHistogramMean.RoleIndex security ≃ ActualCycleMeanMGF.BodyIndex security)
    (rationalMatrix : CurrentRectangleIndex.Point security order → CurrentRectangleIndex.Point security order → ℚ)
    (matrix : Vector (Vector RationalBits (((order+1)^2)*(CurrentRectangleIndex.colors security)^order))
      (((order+1)^2)*(CurrentRectangleIndex.colors security)^order))
    (rhs : Vector RationalBits (((order+1)^2)*(CurrentRectangleIndex.colors security)^order))
    (hmatrix : ∀ output input, ((matrix.get output).get input).decode =
      CurrentRectangleIndex.defect security order rationalMatrix (finProdFinEquiv.symm output) (finProdFinEquiv.symm input))
    (hrhs : ∀ output, (rhs.get output).decode = CurrentRectangleIndex.rhs security order (finProdFinEquiv.symm output))
    (entryError : ℝ) (he : 0 ≤ entryError)
    (hentries : ∀ output input, |(rationalMatrix output input : ℝ) -
      LinearMap.toMatrix' (CalibrationTableNorm.exactDefect security order horder hsecurity
        (ActualLayouts.blockLayout layout)) output input| ≤ entryError)
    (hsmall : CalibrationMatrixApproximation.perturbationFactor security order * entryError ≤ 1/4)
    (steps : ℕ)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ)))
    (core : ActualPublicCharge.Core security) :
    |(BinaryPublicRejection.coreWeight security bits order
      (BinaryRectangleIteration.run ((order+1)^2) ((CurrentRectangleIndex.colors security)^order) matrix rhs steps).value core : ℝ) -
      ActualCalibratedPublic.weight security order horder hsecurity layout core| ≤
      CalibratedWeightApproximation.weightBudget security bits order steps entryError := by
  have hc := RationalWeightProgram.current_cast security bits order (Parameters.legCount security)
    (BackgroundRates.ordinaryPool security)
    (BinaryWeightLocal.rawTable security order
      (BinaryRectangleIteration.run ((order+1)^2) ((CurrentRectangleIndex.colors security)^order) matrix rhs steps).value)
    (fun index => core.controls (.inl index)) (fun index => (core.controls (.inr index)).2)
  have ht : RationalWeightProgram.realTable security order
      (BinaryWeightLocal.rawTable security order
        (BinaryRectangleIteration.run ((order+1)^2) ((CurrentRectangleIndex.colors security)^order) matrix rhs steps).value) =
      fun point => (RationalNumerics.linearIteration rationalMatrix (CalibrationMatrixApproximation.rhs security order) steps point : ℝ) :=
    funext (iteration_realTable security order steps rationalMatrix matrix rhs hmatrix hrhs)
  rw [ht] at hc
  have h := CalibratedWeightApproximation.iteration_weight_error security bits order horder hsecurity
    (ActualLayouts.blockLayout layout) rationalMatrix entryError he hentries hsmall steps hprecision hbudget
    (fun index => core.controls (.inl index)) (fun index => (core.controls (.inr index)).2)
  change (BinaryPublicRejection.coreWeight security bits order _ core : ℝ) = _ at hc
  rw [hc]
  exact h

end
end CurrentAFT.BinaryCalibrationWeightSemantic
