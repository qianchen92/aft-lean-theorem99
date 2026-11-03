import CurrentAFT.FullResponseWeightedIdentity
import CurrentAFT.CalibrationTableNorm

/-! The numerical response minus its weighted point column is the defect,
with no additional identity matrix or redundant-coordinate correction. -/
namespace CurrentAFT.FullResponseWeightedIdentity
open AFT ActualBlockFock GradedControlAlgebra LocalCoefficientFamily
  ActualControls ProposalPrimary FullResponsePointFormula RationalActualFamilyApproximation
open scoped BigOperators Classical
noncomputable section
local instance defectFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize Parameters.dimension primaryLaw bodyReference

theorem exactDefect_entry (security order : ℕ) (horder : 2 ≤ order)
    (hsecurity : ActualCompleteStability.threshold order horder ≤ security)
    (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security) (output source : Index security order) :
    LinearMap.toMatrix' (CalibrationTableNorm.exactDefect security order horder hsecurity layout) output source =
      data security order (response security order horder (ActualCompleteStability.room security order horder hsecurity) source layout)
        output.1 output.2.1 output.2.2-
      data security order (Pi.single source.1 (sourceKernel security order source)) output.1 output.2.1 output.2.2 := by
  rw [CalibrationTableNorm.exactDefect_matrix]
  simp only [Matrix.sub_apply, FullResponsePointFormula.currentMatrix_entry,
    response_eq, sourceFamily, data, Pi.smul_apply, Submodule.coe_smul, smul_eq_mul]
  by_cases he : output=source
  · subst output
    simp only [ite_true, Matrix.one_apply_eq]
    ring
  · simp only [if_neg he, Matrix.one_apply_ne he]
    ring

end
end CurrentAFT.FullResponseWeightedIdentity
