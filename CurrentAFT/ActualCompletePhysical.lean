import CurrentAFT.RootActualOutputPolynomial
import CurrentAFT.RootIndependentSelectedPhysical
import CurrentAFT.PhysicalPolynomialAverages
import CurrentAFT.ActualCompleteStability

/-! # The complete physical response, with all actual finite averages -/
namespace CurrentAFT.ActualCompletePhysical
open AFT AFT.RepresentedPolynomial ActualBlockFock TaggedSelection ControlCoordinates
  LocalCoefficientFamily GradedControlAlgebra CycleRootExpansion ActualLayouts
  ActualRootDefectPhysical RootActualOutputPolynomial RootIndependentSelectedPhysical
  PhysicalPolynomialAverages LocalReferenceEnergy ActualFockBound ActualRootFamily
  ConditionalHistogramMean UniformTaggedOutput CompleteRaisingEvaluation ActualCycleMeanMGF
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance finDecEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance sumDecEq {First Second : Type*} : DecidableEq (First ⊕ Second) := Classical.decEq _
local instance vertexDecEq (security : ℕ) : DecidableEq (Vertex security) :=
  instDecidableEqFin (Parameters.bodySize security)
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

theorem selected_physical {security r s : ℕ} (order : ℕ) (horder : 2 ≤ order)
    (queue : ℤ) (selection : Selection security r s)
    (layout : RoleIndex security ≃ BodyIndex security)
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s) :
    TruncatedOutput.quotientMap order
      (expectationLinear (FiniteDist.uniform (Equiv.Perm (BodyIndex security)))
        (fun permutation => centeredGeneratingLinear (uniformReference security).weight
          (TaggedOutputFock.outputMass security r s selection layout queue permutation kernel.val))) =
      BackgroundEvaluation.evaluation security order
        (ActualBackground.fixedQueueBackground security order horder queue *
          (normalizedJoint security order (by omega) kernel +
            ActualRootDefect.selectedDefect order (by omega) queue selection (blockLayout layout) kernel)) := by
  rw [← cycle_output_generating]
  have hdef := selectedDefect_physical order horder queue selection (blockLayout layout) kernel
  have hind := independent_conditional_polynomial order (by omega) queue selection (blockLayout layout) kernel
  rw [mul_add, map_add, hdef, map_mul,
    BackgroundPolynomialEvaluation.fixedQueueBackground_image, ← hind, map_sub]
  change _ = TruncatedOutput.quotientMap order
    (expectationLinear (FiniteDist.independent (fun _ : Vertex security => rootReference security))
      (rootTest queue selection (blockLayout layout) kernel)) + _
  abel

def selectedGenerating (security order : ℕ) (hroom : 2 * order ≤ security)
    (queue : ℤ) (layout : RoleIndex security ≃ BodyIndex security) (arity : TruncatedArity order)
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security)
      arity.val.1.val arity.val.2.val) : MvPolynomial (ActualControls.Palette security) ℝ :=
  ∑ choice : Choice security arity.val.1.val arity.val.2.val,
    (choiceLaw security arity.val.1.val arity.val.2.val
      (ActualRootFamily.primary_room security order hroom arity)
      (ActualRootFamily.body_room security order hroom arity)).weight choice •
        expectationLinear (FiniteDist.uniform (Equiv.Perm (BodyIndex security)))
          (fun permutation => centeredGeneratingLinear (uniformReference security).weight
            (TaggedOutputFock.outputMass security arity.val.1.val arity.val.2.val
              (selection security arity.val.1.val arity.val.2.val choice) layout queue permutation kernel.val))

theorem selectedGenerating_image (security order : ℕ) (horder : 2 ≤ order)
    (hroom : 2 * order ≤ security) (queue : ℤ)
    (layout : RoleIndex security ≃ BodyIndex security) (arity : TruncatedArity order)
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security)
      arity.val.1.val arity.val.2.val) :
    TruncatedOutput.quotientMap order (selectedGenerating security order hroom queue layout arity kernel) =
      BackgroundEvaluation.evaluation security order
        (ActualBackground.fixedQueueBackground security order horder queue *
          (normalizedJoint security order (by omega) kernel +
            selectedAverage security order (by omega) hroom queue (blockLayout layout) arity kernel)) := by
  simp only [selectedGenerating, map_sum, map_smul]
  simp_rw [selected_physical order horder]
  calc
    _ = BackgroundEvaluation.evaluation security order
        (∑ choice : Choice security arity.val.1.val arity.val.2.val,
          (choiceLaw security arity.val.1.val arity.val.2.val
            (ActualRootFamily.primary_room security order hroom arity)
            (ActualRootFamily.body_room security order hroom arity)).weight choice •
          (ActualBackground.fixedQueueBackground security order horder queue *
            (normalizedJoint security order (by omega) kernel +
              ActualRootDefect.selectedDefect order (by omega) queue
                (selection security arity.val.1.val arity.val.2.val choice) (blockLayout layout) kernel))) := by
      simp only [map_sum, map_smul]
    _ = _ := by
      congr 1
      simp only [mul_add, smul_add, Finset.sum_add_distrib, selectedAverage_apply]
      rw [← Finset.sum_smul, FiniteDist.sum_one, one_smul]
      simp only [Finset.mul_sum, mul_smul_comm]

def familyGenerating (security order : ℕ) (hroom : 2 * order ≤ security)
    (queue : ℤ) (layout : RoleIndex security ≃ BodyIndex security) (family : Family security order) :
    MvPolynomial (ActualControls.Palette security) ℝ :=
  ∑ arity : TruncatedArity order, selectedGenerating security order hroom queue layout arity (family arity)

theorem familyGenerating_image (security order : ℕ) (horder : 2 ≤ order)
    (hroom : 2 * order ≤ security) (queue : ℤ)
    (layout : RoleIndex security ≃ BodyIndex security) (family : Family security order) :
    TruncatedOutput.quotientMap order (familyGenerating security order hroom queue layout family) =
      BackgroundEvaluation.evaluation security order
        (ActualBackground.fixedQueueBackground security order horder queue *
          (family + CompleteRaising.raisingLinear security order (by omega) family +
            rootLinear security order (by omega) hroom queue (blockLayout layout) family)) := by
  simp only [familyGenerating, map_sum]
  simp_rw [selectedGenerating_image security order horder]
  rw [← map_sum, ← Finset.mul_sum, Finset.sum_add_distrib]
  rw [rootLinear_apply security order (by omega) hroom queue (blockLayout layout) family]
  have hnormalized := normalizedResponse_image security order (by omega) family
  unfold normalizedResponse at hnormalized
  simp only [map_mul, map_add]
  rw [hnormalized, map_add]

theorem complete_generating_image (security order : ℕ) (horder : 2 ≤ order)
    (hroom : 2 * order ≤ security)
    (layout : RoleIndex security ≃ BodyIndex security) (family : Family security order) :
    TruncatedOutput.quotientMap order
      (∑ scalar, (DiffuseProfiles.scalarLaw security).weight scalar •
        familyGenerating security order hroom scalar.val layout family) =
      BackgroundEvaluation.evaluation security order
        (ActualCompleteStability.fullResponse security order horder hroom (blockLayout layout) family) := by
  simp only [map_sum, map_smul]
  simp_rw [familyGenerating_image security order horder]
  calc
    _ = BackgroundEvaluation.evaluation security order
        (∑ scalar, (DiffuseProfiles.scalarLaw security).weight scalar •
          (ActualBackground.fixedQueueBackground security order horder scalar.val *
            (family + CompleteRaising.raisingLinear security order (by omega) family +
              rootLinear security order (by omega) hroom scalar.val (blockLayout layout) family))) := by
      simp only [map_sum, map_smul]
    _ = _ := by
      congr 1
      simp only [ActualCompleteStability.fullResponse, LinearMap.add_apply,
        ActualCompleteStability.independentResponse, ActualCompleteStability.rootCorrection,
        LinearMap.coe_mk, AddHom.coe_mk, ActualBackground.background,
        mul_add, smul_add, Finset.sum_add_distrib, Finset.sum_mul, smul_mul_assoc]

end
end CurrentAFT.ActualCompletePhysical
