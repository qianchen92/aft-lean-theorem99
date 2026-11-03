import CurrentAFT.FullResponseDefectIdentity
import CurrentAFT.RationalFullResponseRates

/-! Actual rational entries of the full calibration defect. -/
namespace CurrentAFT.RationalFullResponseProgram
open AFT ActualBlockFock GradedControlAlgebra ActualControls FullResponsePointFormula RationalActualFamilyApproximation
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def matrix (security bits order : ℕ) (output source : Index security order) : ℚ :=
  defect security bits order source.1 (fun index => (source.2.1 index).val)
    (fun index => (source.2.2 index).val.val) output.1
    (fun index => (output.2.1 index).val) (fun index => (output.2.2 index).val.val)

noncomputable section
open scoped Classical
local instance matrixFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize Parameters.dimension
  ProposalPrimary.primaryLaw bodyReference

theorem matrix_error (security bits order : ℕ) (horder : 2 ≤ order)
    (hsecurity : ActualCompleteStability.threshold order horder ≤ security)
    (hbody : order ≤ Parameters.bodySize security)
    (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ)))
    (output source : Index security order) :
    |(matrix security bits order output source:ℝ)-
      LinearMap.toMatrix' (CalibrationTableNorm.exactDefect security order horder hsecurity layout) output source| ≤
      errorConstant security order*(1/(2:ℝ)^bits) := by
  let room := ActualCompleteStability.room security order horder hsecurity
  have hr := response_error security bits order horder room hbody source layout hfirst hprecision hbudget
    output.1 output.2.1 output.2.2
  have hb := basis_error security bits order source hprecision hbudget output.1 output.2.1 output.2.2
  rw [FullResponseWeightedIdentity.exactDefect_entry]
  simp only [matrix, defect, Pi.sub_apply, Rat.cast_sub]
  simp only [interpret, RationalFamilyProductProgram.pullback, RationalFamilyProductProgram.realTable, Function.comp_def] at hr hb
  simp only [data, Pi.single, Function.update] at hr hb ⊢
  have h := (abs_sub _ _).trans (add_le_add hr hb)
  convert h using 1
  · congr 1
    ring
  · unfold errorConstant
    ring

end
end CurrentAFT.RationalFullResponseProgram
