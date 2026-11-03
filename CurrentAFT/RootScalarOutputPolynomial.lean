import CurrentAFT.RootActualOutputPolynomial

/-! # The scalar arity is the literal unselected positive output law -/
namespace CurrentAFT.RootScalarOutputPolynomial
open AFT AFT.RepresentedPolynomial ActualBlockFock ActualBlockMean ActualFockBound
  ActualCycleMeanMGF TaggedSelection TaggedOutputFock CycleRootExpansion ActualLayouts
  LocalReferenceEnergy ControlCoordinates GradedControlAlgebra RootActualOutputPolynomial
  RootBackgroundPolynomial RootLocalDenominators
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount

theorem selection_kept_zero {security : ℕ} (selection : Selection security 0 0) :
    selection.kept = Finset.univ := by
  have hremoved : selection.removed = ∅ := by
    haveI : IsEmpty (RemovedLabel 0 0) := inferInstance
    simp only [Selection.removed, Finset.univ_eq_empty, Finset.map_empty]
  simp only [Selection.kept, hremoved, Finset.sdiff_empty]

def blockPolynomial (security : ℕ) (queue : ℤ) (roots : BlockIndex security → ℤ) :
    MvPolynomial (ActualControls.Palette security) ℝ :=
  centeredGeneratingLinear (uniformReference security).weight
    (BlockProducts.blockMass (Slots security) (TypedTaggedPhysical.blockLaw security queue roots))

theorem blockPolynomial_product (security : ℕ) (queue : ℤ) (roots : BlockIndex security → ℤ) :
    blockPolynomial security queue roots =
      ∏ block, blockGenerating security (TypedTaggedPhysical.blockLaw security queue roots block) := by
  change centeredGeneratingLinear (uniformReference security).weight
    (BlockProducts.blockMass (Slots security) (TypedTaggedPhysical.blockLaw security queue roots)) = _
  unfold BlockProducts.blockMass
  have h := TypedTaggedPhysical.signed_block_generating (Slots security) (uniformReference security).weight
    (fun block => (TypedTaggedPhysical.blockLaw security queue roots block).weight)
  simp_rw [generating_eq_block] at h
  refine Eq.trans ?_ h
  simp only [centeredGeneratingLinear, LinearMap.coe_mk, AddHom.coe_mk]

theorem conditionalPolynomial_scalar {security : ℕ} (selection : Selection security 0 0)
    (queue : ℤ) (roots : BlockIndex security → ℤ) (scalar : ℝ) :
    TypedTaggedPhysical.conditionalPolynomial selection queue roots
      (scalarKernel (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) scalar).val =
      scalar • blockPolynomial security queue roots := by
  rw [TypedTaggedPhysical.conditionalPolynomial_product]
  have hselected : centeredGeneratingLinear (uniformReference security).weight
      (TypedTaggedPhysical.selectedMass selection roots
        (scalarKernel (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) scalar).val) =
        scalar • (1 : MvPolynomial (ActualControls.Palette security) ℝ) := by
    unfold TypedTaggedPhysical.selectedMass
    haveI : IsEmpty (Sigma (JointTaggedPhysicalFock.physicalSlots 0 0)) :=
      ⟨fun point => Fin.elim0 point.fst⟩
    unfold centeredGeneratingLinear JointTaggedPhysicalFock.jointMass JointPhysicalChannel.mass
    simp [JointTaggedPhysicalFock.finiteKernel, JointTaggedPhysicalFock.unpairedKernel, scalarKernel]
  rw [hselected, smul_mul_assoc, one_mul, blockPolynomial_product]
  congr 1
  rw [← Finset.prod_subtype selection.kept (fun _ => Iff.rfl)
    (fun block => blockGenerating security (TypedTaggedPhysical.blockLaw security queue roots block)), selection_kept_zero]

theorem outputLaw_generating (security : ℕ)
    (layout : ConditionalHistogramMean.RoleIndex security ≃ BodyIndex security) (queue : ℤ)
    (permutation : Equiv.Perm (BodyIndex security)) :
    centeredGeneratingLinear (uniformReference security).weight (outputLaw security layout queue permutation).weight =
      expectationLinear (latentLaw security) (fun latent => blockPolynomial security queue
        (fun block => rootAt security permutation latent (blockLayout layout block))) := by
  change centeredGeneratingLinear (uniformReference security).weight
    (fun output => (latentLaw security).expectation (fun latent =>
      BlockProducts.blockMass (Slots security) (rootedLaw security layout queue permutation latent) output)) = _
  rw [linear_average]
  rfl

/-- For every actual body permutation, zero selected controls leave exactly
the scalar multiple of the complete original positive block experiment. -/
theorem scalar_output_generating {security : ℕ} (selection : Selection security 0 0)
    (layout : ConditionalHistogramMean.RoleIndex security ≃ BodyIndex security) (queue : ℤ)
    (permutation : Equiv.Perm (BodyIndex security)) (scalar : ℝ) :
    centeredGeneratingLinear (uniformReference security).weight
      (TaggedOutputFock.outputMass security 0 0 selection layout queue permutation
        (scalarKernel (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) scalar).val) =
      scalar • centeredGeneratingLinear (uniformReference security).weight (outputLaw security layout queue permutation).weight := by
  letI : DecidableEq (OutputIndex selection) := Classical.decEq _
  change centeredGeneratingLinear (uniformReference security).weight
    (fun output => (latentLaw security).expectation (fun latent =>
      TaggedOutputFock.conditionalMass security 0 0 selection layout queue permutation latent
        (scalarKernel (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) scalar).val output)) = _
  rw [linear_average (Output := OutputIndex selection → ActualControls.Palette security)
    (centeredGeneratingLinear (uniformReference security).weight) (latentLaw security)
    (fun latent => TaggedOutputFock.conditionalMass security 0 0 selection layout queue permutation latent
      (scalarKernel (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) scalar).val),
    outputLaw_generating]
  have hlocal (latent : BodyIndex security → Edge security) :
      centeredGeneratingLinear (uniformReference security).weight
        (TaggedOutputFock.conditionalMass security 0 0 selection layout queue permutation latent
          (scalarKernel (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) scalar).val) =
      scalar • blockPolynomial security queue (fun block => rootAt security permutation latent (blockLayout layout block)) := by
    rw [← RootConditionalResidues.conditionalPolynomial_rootAt, conditionalPolynomial_scalar]
  simp_rw [hlocal]
  exact (expectationLinear (latentLaw security)).map_smul scalar _

theorem scalar_output_average {security : ℕ} (selection : Selection security 0 0)
    (layout : ConditionalHistogramMean.RoleIndex security ≃ BodyIndex security) (queue : ℤ) (scalar : ℝ) :
    expectationLinear (FiniteDist.uniform (Equiv.Perm (BodyIndex security)))
      (fun permutation => centeredGeneratingLinear (uniformReference security).weight
        (TaggedOutputFock.outputMass security 0 0 selection layout queue permutation
          (scalarKernel (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) scalar).val)) =
      scalar • expectationLinear (FiniteDist.uniform (Equiv.Perm (BodyIndex security)))
        (fun permutation => centeredGeneratingLinear (uniformReference security).weight
          (outputLaw security layout queue permutation).weight) := by
  simp_rw [scalar_output_generating]
  exact (expectationLinear (FiniteDist.uniform (Equiv.Perm (BodyIndex security)))).map_smul scalar _

end
end CurrentAFT.RootScalarOutputPolynomial
