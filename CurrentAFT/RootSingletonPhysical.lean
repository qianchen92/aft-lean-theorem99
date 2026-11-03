import CurrentAFT.RootSingletonTensor
import CurrentAFT.GroupedKernelPolynomial

/-! # Exact physical image of the joint singleton root coefficient -/
namespace CurrentAFT.RootSingletonPhysical
open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct
  GradedControlAlgebra BackgroundFamilies BackgroundRates CycleRootExpansion
  RootTaggedLocal RootTaggedFamilies UniformBodyProfiles RootSingletonTensor
  LeadingEvaluation BackgroundEvaluation BackgroundFirstEvaluation LocalCoefficientEvaluation
  LocalCoefficientFamily PrimaryMassFamilies PrimaryTensorInverse GroupedKernelProduct
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalRootDecidableEq (security : ℕ) : DecidableEq (Root security) := Classical.decEq _
local instance classicalSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} :
    DecidableEq (Sigma Slots) := Classical.decEq _
attribute [local irreducible] Parameters.base primaryLaw bodyReference rootReference

theorem rootKernel_polynomial (security : ℕ) (role : BodyRole) (queue : ℤ) (input : Root security → ℝ) :
    kernelPolynomial (primaryLaw security) (bodyReference security) (primaryForm security) (bodyForm security)
      (rootKernelLinear security role queue input).val =
        RepresentedPolynomial.profileForm (rootMass security role queue input) := by
  change kernelPolynomial _ _ _ _ (primaryKernel (primaryLaw security) (bodyReference security)
    (rootLift security role queue input) (rootLift_mean security role queue input)).val = _
  rw [primaryKernel_polynomial]
  have hpoly := primary_kernelPolynomial security 1 (oneWordProfile (rootLift security role queue input)) (bodyForm security)
  rw [kernelPolynomial_no_body] at hpoly
  rw [hpoly]
  unfold primaryLeadingPolynomial
  rw [massLeading_one, massPolynomial_one, rootLift_massLeading]

theorem rootMass_single (security : ℕ) (role : BodyRole) (queue : ℤ) (root : Root security) :
    rootMass security role queue (Pi.single root 1) =
      (rootReference security).weight root • deviationProfile security role queue root := by
  funext color
  simp [rootMass, Pi.single_apply]

theorem tensorKernel_polynomial (security count : ℕ) (roles : Fin count → BodyRole) (queues : Fin count → ℤ)
    (input : (Fin count → Root security) → ℝ) :
    kernelPolynomial (primaryLaw security) (bodyReference security) (primaryForm security) (bodyForm security)
      (tensorKernel security count roles queues input).val =
      ∑ roots, input roots • ∏ index,
        RepresentedPolynomial.profileForm (rootMass security (roles index) (queues index) (Pi.single (roots index) 1)) := by
  have h := GroupedKernelPolynomial.tensor_polynomial (primaryLaw security) (bodyReference security)
    (primaryForm security) (bodyForm security) (fun _ : Fin count => 1) (fun _ : Fin count => 0)
    (RootSingletonTensor.primaryEquiv count) (RootSingletonTensor.bodyEquiv count)
    (fun index => rootKernelLinear security (roles index) (queues index)) input
  simp only [rootKernel_polynomial] at h
  exact h

/-- The exact weighted joint-root average of centered local physical
profiles, with the original joint coefficient inside one finite sum. -/
theorem tensorFamily_image (security order count : ℕ) (hcount : count ≤ order)
    (roles : Fin count → BodyRole) (queues : Fin count → ℤ)
    (input : (Fin count → Root security) → ℝ) :
    evaluation security order (tensorFamily security order count hcount roles queues input) =
      ∑ roots, ((∏ index, (rootReference security).weight (roots index)) * input roots) •
        TruncatedOutput.quotientMap order
          (∏ index, RepresentedPolynomial.profileForm (deviationProfile security (roles index) (queues index) (roots index))) := by
  change familyLinear _ _ _ _ order (Pi.single _ _) = _
  rw [familyLinear_single]
  change TruncatedOutput.quotientMap order
    (kernelPolynomial _ _ _ _ (tensorKernel security count roles queues input).val) = _
  rw [tensorKernel_polynomial]
  simp only [rootMass_single, map_sum, map_smul, map_prod, Finset.prod_smul, smul_smul]
  apply Finset.sum_congr rfl
  intro roots _
  rw [mul_comm]

end
end CurrentAFT.RootSingletonPhysical
