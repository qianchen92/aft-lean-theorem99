import CurrentAFT.ActualCompletePhysical
import CurrentAFT.ActualFamilyPolynomial
import CurrentAFT.RootScalarOutputPolynomial
import CurrentAFT.PhysicalPolynomialEnumeration

/-! # Actual complete output PGF and its coefficient response -/
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
local instance pgfFinDecEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

theorem selectedGenerating_zero (security order : ℕ) (hroom : 2 * order ≤ security)
    (queue : ℤ) (layout : RoleIndex security ≃ BodyIndex security)
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) 0 0) :
    selectedGenerating security order hroom queue layout (zeroArity order) kernel =
      scalarAt (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) kernel •
        expectationLinear (FiniteDist.uniform (Equiv.Perm (BodyIndex security)))
          (fun permutation => centeredGeneratingLinear (uniformReference security).weight
            (outputLaw security layout queue permutation).weight) := by
  unfold selectedGenerating
  dsimp only [zeroArity]
  have hkernel := scalarKernel_scalarAt (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) kernel
  conv_lhs => rw [← hkernel]
  have hlocal (choice : Choice security 0 0) := RootScalarOutputPolynomial.scalar_output_average
    (selection security 0 0 choice) layout queue
    (scalarAt (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) kernel)
  have hmean (choice : Choice security 0 0) :
      expectationLinear (FiniteDist.uniform (Equiv.Perm (BodyIndex security)))
        (fun permutation => centeredGeneratingLinear (uniformReference security).weight
          (TaggedOutputFock.outputMass security 0 0 (selection security 0 0 choice) layout queue permutation
            (scalarKernel (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security)
              (scalarAt (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) kernel)).val)) =
        scalarAt (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) kernel •
          expectationLinear (FiniteDist.uniform (Equiv.Perm (BodyIndex security)))
            (fun permutation => centeredGeneratingLinear (uniformReference security).weight
              (outputLaw security layout queue permutation).weight) := hlocal choice
  have hweights := (choiceLaw security 0 0 (ActualRootFamily.primary_room security order hroom (zeroArity order))
    (ActualRootFamily.body_room security order hroom (zeroArity order))).sum_one
  conv_rhs => rw [← one_smul ℝ (scalarAt _ _ kernel • _), ← hweights, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro choice _
  congr 1
  refine Eq.trans ?_ (hmean choice)
  unfold expectationLinear
  simp only [LinearMap.coe_mk, AddHom.coe_mk, FiniteDist.uniform_weight, Fintype.card_eq_nat_card]
  apply Finset.sum_congr (by ext permutation; simp)
  intro permutation _
  apply congrArg (fun polynomial => ((Nat.card (Equiv.Perm (BodyIndex security)) : ℝ))⁻¹ • polynomial)
  exact generating_enumeration _ _ _ _

theorem familyGenerating_eq_average (security order : ℕ) (hroom : 2 * order ≤ security)
    (queue : ℤ) (layout : RoleIndex security ≃ BodyIndex security) (family : Family security order) :
    familyGenerating security order hroom queue layout family =
      expectationLinear (FiniteDist.uniform (Equiv.Perm (BodyIndex security)))
        (fun permutation => centeredGeneratingLinear (uniformReference security).weight
          (CoefficientOutputFock.familyMass security order hroom layout queue permutation
            (familyToCoefficients (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) order family))) := by
  rw [familyGenerating, sum_arities, selectedGenerating_zero]
  simp_rw [ActualFamilyPolynomial.family_generating]
  simp only [familyToCoefficients, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [expectationLinear, LinearMap.coe_mk, AddHom.coe_mk, smul_add, Finset.smul_sum,
    Finset.sum_add_distrib, selectedGenerating, FiniteDist.uniform_weight, Fintype.card_eq_nat_card]
  apply congrArg₂ (· + ·)
  · simp only [smul_smul]
    apply Finset.sum_congr (by ext permutation; simp)
    intro permutation _
    rw [mul_comm]
  · rw [Finset.sum_comm]
    apply Finset.sum_congr (by ext permutation; simp)
    intro arity _
    rw [Finset.sum_comm]
    apply Finset.sum_congr (by ext permutation; simp)
    intro permutation _
    apply Finset.sum_congr (by ext choice; simp)
    intro choice _
    simp only [positiveArity, smul_smul, mul_comm]

theorem mixed_generating (security order : ℕ) (hroom : 2 * order ≤ security)
    (layout : RoleIndex security ≃ BodyIndex security) (family : Family security order) :
    centeredGeneratingLinear (uniformReference security).weight
      (ActualWeightedFourier.mixedMass security order hroom layout
        (familyToCoefficients (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) order family)) =
      ∑ scalar, (DiffuseProfiles.scalarLaw security).weight scalar •
        familyGenerating security order hroom scalar.val layout family := by
  unfold ActualWeightedFourier.mixedMass
  rw [linear_average, ActualWeightedFourier.randomizationLaw, expectationLinear_prod]
  simp_rw [← familyGenerating_eq_average]
  rfl

/-- The actual complete coefficient response is exactly the truncated PGF
of the physical signed output, including the scalar baseline and every
original joint kernel, after the true common queue and body permutation. -/
theorem fullResponse_physical (security order : ℕ) (horder : 2 ≤ order)
    (hroom : 2 * order ≤ security) (layout : RoleIndex security ≃ BodyIndex security)
    (family : Family security order) :
    TruncatedOutput.quotientMap order
      (centeredGeneratingLinear (uniformReference security).weight
        (ActualWeightedFourier.mixedMass security order hroom layout
          (familyToCoefficients (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) order family))) =
      BackgroundEvaluation.evaluation security order
        (ActualCompleteStability.fullResponse security order horder hroom (blockLayout layout) family) := by
  rw [mixed_generating, complete_generating_image]

end
end CurrentAFT.ActualCompletePhysical
