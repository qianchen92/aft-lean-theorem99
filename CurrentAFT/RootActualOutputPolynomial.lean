import CurrentAFT.ActualRootDefectPhysical
import CurrentAFT.RootConditionalResidues

/-! # The cycle-root PGF is the literal actual averaged signed output PGF -/
namespace CurrentAFT.RootActualOutputPolynomial
open AFT AFT.RepresentedPolynomial ActualBlockFock ActualBlockMean ActualFockBound
  TaggedSelection TaggedOutputFock CycleRootExpansion ActualLayouts ActualRootDefectPhysical
  LocalReferenceEnergy RootBackgroundPolynomial ActualCycleMeanMGF
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
local instance vertexDecidableEq (security : ℕ) : DecidableEq (Vertex security) :=
  instDecidableEqFin (Parameters.bodySize security)
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount

section Generic
variable {Source Target Value : Type*} [Fintype Source] [Fintype Target]
  [AddCommGroup Value] [Module ℝ Value]

theorem expectationLinear_map (law : FiniteDist Source) (map : Source → Target) (test : Target → Value) :
    expectationLinear (law.map map) test = expectationLinear law (test ∘ map) := by
  simp only [expectationLinear, LinearMap.coe_mk, AddHom.coe_mk,
    FiniteDist.map_weight, Finset.sum_smul, ite_smul, zero_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro source _
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Function.comp_apply]

theorem expectationLinear_mix (law : FiniteDist Source) (channel : Source → FiniteDist Target)
    (test : Target → Value) :
    expectationLinear (law.mix channel) test =
      expectationLinear law (fun source => expectationLinear (channel source) test) := by
  simp only [expectationLinear, LinearMap.coe_mk, AddHom.coe_mk,
    FiniteDist.mix_weight, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]

theorem linear_average {Output : Type*} [Fintype Output]
    (channel : (Output → ℝ) →ₗ[ℝ] Value) (law : FiniteDist Source) (mass : Source → Output → ℝ) :
    channel (fun output => law.expectation (fun source => mass source output)) =
      expectationLinear law (fun source => channel (mass source)) := by
  have hmass : (fun output => law.expectation (fun source => mass source output)) =
      ∑ source, law.weight source • mass source := by
    funext output
    simp only [FiniteDist.expectation, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hmass, map_sum]
  simp only [map_smul, expectationLinear, LinearMap.coe_mk, AddHom.coe_mk]

end Generic

theorem rootTest_latent {security r s : ℕ} (queue : ℤ) (selection : Selection security r s)
    (layout : ConditionalHistogramMean.RoleIndex security ≃ BodyIndex security)
    (kernel : ControlCoordinates.canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s)
    (permutation : Equiv.Perm (BodyIndex security)) (latent : BodyIndex security → Edge security) :
    rootTest queue selection (blockLayout layout) kernel (rootedResidues security permutation latent) =
      centeredGeneratingLinear (uniformReference security).weight
        (TaggedOutputFock.conditionalMass security r s selection layout queue permutation latent kernel.val) := by
  change TypedTaggedPhysical.conditionalPolynomial selection queue
    (fun block => (((rootAt security permutation latent (blockLayout layout block) : ℤ) : Root security).val : ℤ)) kernel.val = _
  rw [← RootConditionalResidues.conditionalPolynomial_residues,
    RootConditionalResidues.conditionalPolynomial_rootAt]

/-- Both the body permutation and the closed-cycle latent sources are the
ones of the actual output experiment. Only the exact root residues are used
to invoke the root-component expansion. -/
theorem cycle_output_generating {security r s : ℕ} (queue : ℤ) (selection : Selection security r s)
    (layout : ConditionalHistogramMean.RoleIndex security ≃ BodyIndex security)
    (kernel : ControlCoordinates.canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s) :
    expectationLinear (rootLaw security) (rootTest queue selection (blockLayout layout) kernel) =
      expectationLinear (FiniteDist.uniform (Equiv.Perm (BodyIndex security)))
        (fun permutation => centeredGeneratingLinear (uniformReference security).weight
          (TaggedOutputFock.outputMass security r s selection layout queue permutation kernel.val)) := by
  rw [rootLaw_latent, expectationLinear_mix]
  simp_rw [expectationLinear_map]
  apply congrArg (expectationLinear (FiniteDist.uniform (Equiv.Perm (BodyIndex security))))
  funext permutation
  change expectationLinear (FiniteDist.independent (fun _ : BodyIndex security => DiffuseProfiles.edgeLaw security))
    (fun latent => rootTest queue selection (blockLayout layout) kernel (rootedResidues security permutation latent)) = _
  simp_rw [rootTest_latent]
  rw [← linear_average]
  apply congrArg (centeredGeneratingLinear (uniformReference security).weight)
  funext output
  simp only [TaggedOutputFock.outputMass, latentLaw, FiniteDist.expectation, FiniteDist.independent]
  apply Finset.sum_congr (by ext latent; simp)
  intro latent _
  rfl

end
end CurrentAFT.RootActualOutputPolynomial
