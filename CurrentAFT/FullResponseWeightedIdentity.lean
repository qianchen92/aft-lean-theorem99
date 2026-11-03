import CurrentAFT.EmptyRootCoefficientIdentity
import CurrentAFT.RationalFullResponseProgram

/-! The one-queue, bounded-tag formula is exactly the full current response
on a weighted point column, including its independent leading component. -/
namespace CurrentAFT.FullResponseWeightedIdentity
open AFT ActualBlockFock TaggedSelection GradedControlAlgebra LocalCoefficientFamily
  ActualControls ProposalPrimary ControlCoordinates ControlProduct CanonicalReconstruction
  UniformTaggedOutput ActualRootFamily FullResponsePointFormula ActualBackground
  RationalActualFamilyApproximation
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance finDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize Parameters.dimension
  primaryLaw bodyReference

def sourceKernel (security order : ℕ) (source : Index security order) :=
  WeightedPointKernelProgram.actualKernel security source.2.1 source.2.2

def selected (security order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (source : Index security order) (chosen : Selection security source.1.val.1.val source.1.val.2.val)
    (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security) : Family security order :=
  ActualRootResponse.response order horder queue chosen ∅ layout (sourceKernel security order source)+
    ∑ tagged ∈ RationalFullResponseProgram.tags security order,
      ActualRootResponse.response order horder queue chosen tagged layout (sourceKernel security order source)

def choiceAverage (security order : ℕ) (horder : 1 ≤ order) (hroom : 2*order ≤ security) (queue : ℤ)
    (source : Index security order) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security) : Family security order :=
  ∑ choice : Choice security source.1.val.1.val source.1.val.2.val,
    (choiceLaw security _ _ (primary_room security order hroom source.1)
      (body_room security order hroom source.1)).weight choice •
        selected security order horder queue source (selection security _ _ choice) layout

def fixedQueue (security order : ℕ) (horder : 2 ≤ order) (hroom : 2*order ≤ security) (queue : ℤ)
    (source : Index security order) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security) : Family security order :=
  fixedQueueBackground security order horder queue * choiceAverage security order (by omega) hroom queue source layout

def response (security order : ℕ) (horder : 2 ≤ order) (hroom : 2*order ≤ security)
    (source : Index security order) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security) : Family security order :=
  ∑ scalar : FirstHistogram.Scalar security, (DiffuseProfiles.scalarLaw security).weight scalar •
    fixedQueue security order horder hroom scalar.val source layout

theorem sourceFamily (security order : ℕ) (source : Index security order) :
    (Pi.single source.1 (sourceKernel security order source) : Family security order) =
      referenceWeight security order source • basisFamily security order source := by
  funext output
  by_cases he : output=source.1
  · subst output
    simp only [basisFamily, Pi.smul_apply, Pi.single_eq_same, sourceKernel,
      WeightedPointKernelProgram.actualKernel, referenceWeight]
  · simp only [basisFamily, Pi.smul_apply, Pi.single_eq_of_ne he, smul_zero]

theorem selected_eq (security order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (source : Index security order) (chosen : Selection security source.1.val.1.val source.1.val.2.val)
    (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security) :
    selected security order horder queue source chosen layout =
      referenceWeight security order source •
        (basisFamily security order source+CompleteRaising.raisingLinear security order horder (basisFamily security order source))+
      referenceWeight security order source •
        (∑ tagged ∈ RationalFullResponseProgram.tags security order,
          ActualRootResponse.response order horder queue chosen tagged layout
            (pointKernel (primaryLaw security) (bodyReference security) (primaryReference_positive security)
              (bodyReference_positive security) source.2.1 source.2.2)) := by
  unfold selected
  rw [EmptyRootCoefficientIdentity.response_empty security order horder queue source.1,
    sourceFamily, map_smul, ← smul_add]
  congr 1
  simp only [sourceKernel, WeightedPointKernelProgram.actualKernel, referenceWeight, map_smul, Finset.smul_sum]

theorem choiceAverage_eq (security order : ℕ) (horder : 1 ≤ order) (hroom : 2*order ≤ security) (queue : ℤ)
    (source : Index security order) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security) :
    choiceAverage security order horder hroom queue source layout =
      referenceWeight security order source •
        (basisFamily security order source+CompleteRaising.raisingLinear security order horder (basisFamily security order source)+
          rootPointResponse security order horder hroom queue layout source) := by
  simp only [choiceAverage, selected_eq, smul_add, Finset.sum_add_distrib,
    ← Finset.sum_smul, FiniteDist.sum_one, one_smul]
  congr 1
  unfold rootPointResponse
  simp only [Finset.smul_sum, RationalFullResponseProgram.tags, smul_smul]
  apply Finset.sum_congr rfl
  intro choice _
  rw [mul_comm]
  apply Finset.sum_congr (by ext tagged; simp only [Finset.mem_filter, FullResponseEnumeration.mem_boundedSubsets])
  intro tagged _
  rfl

theorem response_eq (security order : ℕ) (horder : 2 ≤ order) (hroom : 2*order ≤ security)
    (source : Index security order) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security) :
    response security order horder hroom source layout =
      referenceWeight security order source • pointResponse security order horder hroom layout source := by
  let baseline := basisFamily security order source+
    CompleteRaising.raisingLinear security order (by omega) (basisFamily security order source)
  have hterm (scalar : FirstHistogram.Scalar security) :
      (DiffuseProfiles.scalarLaw security).weight scalar •
        (fixedQueueBackground security order horder scalar.val *
          (referenceWeight security order source •
            (baseline+rootPointResponse security order (by omega) hroom scalar.val layout source))) =
      referenceWeight security order source •
        ((DiffuseProfiles.scalarLaw security).weight scalar • (fixedQueueBackground security order horder scalar.val*baseline)+
          (DiffuseProfiles.scalarLaw security).weight scalar • (fixedQueueBackground security order horder scalar.val*
            rootPointResponse security order (by omega) hroom scalar.val layout source)) := by
    rw [mul_smul_comm, smul_comm, mul_add, smul_add]
  unfold response fixedQueue
  simp_rw [choiceAverage_eq]
  change (∑ scalar, (DiffuseProfiles.scalarLaw security).weight scalar •
    (fixedQueueBackground security order horder scalar.val *
      (referenceWeight security order source •
        (baseline+rootPointResponse security order (by omega) hroom scalar.val layout source)))) = _
  simp_rw [hterm]
  rw [← Finset.smul_sum, Finset.sum_add_distrib]
  congr 1
  unfold pointResponse
  congr 1
  simp only [← smul_mul_assoc, ← Finset.sum_mul]
  rfl

end
end CurrentAFT.FullResponseWeightedIdentity
