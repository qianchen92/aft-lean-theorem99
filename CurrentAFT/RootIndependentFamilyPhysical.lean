import CurrentAFT.RootIndependentSelectedPhysical
import CurrentAFT.ActualCompleteStability

/-! # The literal independently rooted reference for the complete public weight

Distinct choices are averaged under their actual finite uniform law. The
same queue is then used in every background factor. Its resulting image is
exactly the previously constructed `Bavg * (Id + U)` response.
-/
namespace CurrentAFT.RootIndependentFamilyPhysical
open AFT AFT.RepresentedPolynomial DiffuseProfiles ProposalPrimary ActualControls
  ActualBlockFock TaggedSelection UniformTaggedOutput CycleRootExpansion ControlCoordinates
  GradedControlAlgebra LocalCoefficientFamily CompleteRaisingEvaluation RootIndependentSelectedPhysical
open scoped BigOperators Classical
noncomputable section
local instance familyBaselineFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance familyBaselineVertexDecidableEq (security : ℕ) : DecidableEq (Vertex security) :=
  instDecidableEqFin (Parameters.bodySize security)
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  ProposalPrimary.primaryLaw ActualControls.bodyReference BackgroundRates.ordinaryPool

def conditionalAverage {security r s : ℕ} (queue : ℤ) (selection : Selection security r s)
    (layout : BlockIndex security ≃ Vertex security)
    (kernel : canonicalKernels (primaryLaw security) (bodyReference security) r s) :
    MvPolynomial (ActualControls.Palette security) ℝ :=
  expectationLinear (FiniteDist.independent (fun _ : Vertex security => rootReference security))
    (fun roots => TypedTaggedPhysical.conditionalPolynomial selection queue
      (fun block => (roots (layout block)).val) kernel.val)

def selectedAverage (security order : ℕ) (hroom : 2 * order ≤ security) (queue : ℤ)
    (layout : BlockIndex security ≃ Vertex security) (arity : TruncatedArity order)
    (kernel : canonicalKernels (primaryLaw security) (bodyReference security) arity.val.1.val arity.val.2.val) :
    MvPolynomial (ActualControls.Palette security) ℝ :=
  expectationLinear
    (choiceLaw security arity.val.1.val arity.val.2.val
      (ActualRootFamily.primary_room security order hroom arity) (ActualRootFamily.body_room security order hroom arity))
    (fun choice => conditionalAverage queue (selection security arity.val.1.val arity.val.2.val choice) layout kernel)

def familyAverage (security order : ℕ) (hroom : 2 * order ≤ security) (queue : ℤ)
    (layout : BlockIndex security ≃ Vertex security) (family : Family security order) :
    MvPolynomial (ActualControls.Palette security) ℝ :=
  ∑ arity : TruncatedArity order, selectedAverage security order hroom queue layout arity (family arity)

theorem selectedAverage_image (security order : ℕ) (horder : 1 ≤ order) (hroom : 2 * order ≤ security)
    (queue : ℤ) (layout : BlockIndex security ≃ Vertex security) (arity : TruncatedArity order)
    (kernel : canonicalKernels (primaryLaw security) (bodyReference security) arity.val.1.val arity.val.2.val) :
    TruncatedOutput.quotientMap order (selectedAverage security order hroom queue layout arity kernel) =
      TruncatedOutput.quotientMap order (BackgroundPolynomialEvaluation.fixedQueueGenerating security queue) *
        BackgroundEvaluation.evaluation security order (normalizedJoint security order horder kernel) := by
  unfold selectedAverage expectationLinear
  simp only [LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul]
  simp only [conditionalAverage, independent_conditional_polynomial order horder]
  rw [← Finset.sum_smul, FiniteDist.sum_one, one_smul]

theorem familyAverage_image (security order : ℕ) (horder : 1 ≤ order) (hroom : 2 * order ≤ security)
    (queue : ℤ) (layout : BlockIndex security ≃ Vertex security) (family : Family security order) :
    TruncatedOutput.quotientMap order (familyAverage security order hroom queue layout family) =
      TruncatedOutput.quotientMap order (BackgroundPolynomialEvaluation.fixedQueueGenerating security queue) *
        BackgroundEvaluation.evaluation security order (normalizedResponse security order horder family) := by
  simp only [familyAverage, map_sum, selectedAverage_image security order horder]
  rw [← Finset.mul_sum, ← map_sum]
  rfl

theorem familyAverage_actual_response (security order : ℕ) (horder : 2 ≤ order) (hroom : 2 * order ≤ security)
    (queue : ℤ) (layout : BlockIndex security ≃ Vertex security) (family : Family security order) :
    TruncatedOutput.quotientMap order (familyAverage security order hroom queue layout family) =
      BackgroundEvaluation.evaluation security order
        (ActualBackground.fixedQueueBackground security order horder queue *
          (family + CompleteRaising.raisingLinear security order (by omega) family)) := by
  rw [familyAverage_image security order (by omega), normalizedResponse_image, map_mul,
    BackgroundPolynomialEvaluation.fixedQueueBackground_image]

def average (security order : ℕ) (hroom : 2 * order ≤ security)
    (layout : BlockIndex security ≃ Vertex security) (family : Family security order) :
    MvPolynomial (ActualControls.Palette security) ℝ :=
  ∑ scalar : FirstHistogram.Scalar security, (scalarLaw security).weight scalar •
    familyAverage security order hroom scalar.val layout family

theorem average_actual_response (security order : ℕ) (horder : 2 ≤ order) (hroom : 2 * order ≤ security)
    (layout : BlockIndex security ≃ Vertex security) (family : Family security order) :
    TruncatedOutput.quotientMap order (average security order hroom layout family) =
      BackgroundEvaluation.evaluation security order (ActualCompleteStability.independentResponse security order horder family) := by
  simp only [average, map_sum, map_smul, familyAverage_actual_response security order horder]
  calc
    _ = BackgroundEvaluation.evaluation security order
        (∑ scalar : FirstHistogram.Scalar security, (scalarLaw security).weight scalar •
          (ActualBackground.fixedQueueBackground security order horder scalar.val *
            (family + CompleteRaising.raisingLinear security order (by omega) family))) := by
      simp only [map_sum, map_smul]
    _ = _ := by
      congr 1
      simp only [ActualCompleteStability.independentResponse, LinearMap.coe_mk, AddHom.coe_mk,
        ActualBackground.background, Finset.sum_mul, smul_mul_assoc]

end
end CurrentAFT.RootIndependentFamilyPhysical
