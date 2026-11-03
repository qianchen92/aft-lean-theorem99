import CurrentAFT.ActualRootPhysicalResponse
import CurrentAFT.GroupedFamilyComposition

/-! # Removing root masks before coefficient evaluation

The actual joint input is fixed by every root mask. This file removes
those masks in the canonical coefficient family itself. The selected
ordinary channel retains its original hybrid body coefficient.
-/
namespace CurrentAFT.ActualRootProjectionData
open AFT ActualBlockFock TaggedSelection PairedRootPlacement PairedRootInput
  CycleRootExpansion ControlCoordinates GradedControlAlgebra LocalCoefficientFamily
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
local instance classicalProdDecidableEq {Left Right : Type*} : DecidableEq (Left × Right) := Classical.decEq _
local instance classicalSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} : DecidableEq (Sigma Slots) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount

theorem unselected_constant (security order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (block : BlockIndex security) (constant : ℝ) :
    RootUnselectedBlockChannel.channel security order horder queue block (fun _ => constant) = 0 := by
  have hconstant : (fun _ : Root security => constant) = constant • (fun _ => (1 : ℝ)) := by
    funext root
    simp only [Pi.smul_apply, smul_eq_mul, mul_one]
  rw [hconstant, map_smul]
  suffices h : RootUnselectedBlockChannel.channel security order horder queue block (fun _ => 1) = 0 by
    rw [h, smul_zero]
  have hsingle (role : UniformBodyProfiles.BodyRole) (shift : ℤ) :
      RootUnselectedChannels.singletonChannel security order horder role shift (fun _ => 1) = 0 := by
    change RootTaggedFamilies.rootFamilyLinear security order horder role shift (fun _ => 1) * _ = 0
    rw [RootTaggedFamilies.rootFamily_constant, zero_mul]
  rcases block with leg | single
  · change (RootTaggedFamilies.rootFamilyLinear security order horder .attachment 0 (fun _ => 1) +
      RootLegCoefficientLinear.rootHigherLinear security order (fun _ => 1)) * _ = 0
    rw [RootTaggedFamilies.rootFamily_constant]
    change (0 + RootLegCoefficientLinear.higherFamilyLinear security order
      (RootTaggedLegHigher.massLinear security (fun _ => 1))) * _ = 0
    rw [RootTaggedLegHigher.massLinear_constant, map_zero, add_zero, zero_mul]
  · rcases single with center | point
    · exact hsingle .free 0
    · exact hsingle .queue queue

theorem unselected_center (security order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (block : BlockIndex security) (score : RootUnselectedGrouped.Input security → ℝ) :
    RootUnselectedGrouped.channel security order horder queue block
      (RootCoordinateProjection.center (rootReference security) (0 : Fin 1) score) =
        RootUnselectedGrouped.channel security order horder queue block score := by
  have haverage : RootUnselectedGrouped.extractLinear security
      (RootCoordinateProjection.average (rootReference security) (0 : Fin 1) score) =
      fun _ => (rootReference security).expectation (RootUnselectedGrouped.extractLinear security score) := by
    funext root
    change (rootReference security).expectation (fun other =>
      score (Function.update (fun _ : Fin 1 => root) 0 other, ())) = _
    simp only [Function.update_eq_const_of_subsingleton]
    rfl
  change RootUnselectedBlockChannel.channel security order horder queue block
    (RootUnselectedGrouped.extractLinear security (score - RootCoordinateProjection.average (rootReference security) (0 : Fin 1) score)) = _
  rw [map_sub, haverage, map_sub, unselected_constant, sub_zero]
  rfl

def unprojectedChannel {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : Selection security r s) (tagged : Finset (BlockIndex security)) :
    (group : ActiveGroup selection tagged) →
      (ActualRootGroupedChannel.Input selection tagged group → ℝ) →ₗ[ℝ] Family security order
  | .inl (.inl _) => (RootTaggedSelectedChannel.channel security order).comp (RootPrimaryGroupedChannel.pairLinear security)
  | .inl (.inr _) => (SelectedOrdinaryHybrid.channel security order horder).comp (RootOrdinaryGroupedChannel.toRaw security)
  | .inr index => RootUnselectedGrouped.channel security order horder queue index.val.val

theorem channel_eq_comp {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (group : ActiveGroup selection tagged) :
    ActualRootGroupedChannel.channel order horder queue selection tagged group =
      (unprojectedChannel order horder queue selection tagged group).comp
        (PairedRootProjection.projector selection tagged group) := by
  rcases group with (primary | ordinary) | kept
  · rw [ActualRootPhysicalResponse.primary_rootProjector]
    rfl
  · rw [ActualRootPhysicalResponse.ordinary_rootProjector]
    rfl
  · rw [ActualRootPhysicalResponse.kept_rootProjector]
    apply LinearMap.ext
    intro score
    exact (unselected_center security order horder queue kept.val.val score).symm

/-- An equality of the actual response data, valid before physical
evaluation and preserving the full joint root/control input. -/
theorem response_unprojected {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (layout : BlockIndex security ≃ Vertex security)
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s) :
    ActualRootResponse.response order horder queue selection tagged layout kernel =
      GroupedFamilyTensor.response (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) order
        (unprojectedChannel order horder queue selection tagged) (jointInput selection tagged layout kernel) := by
  rw [ActualRootResponse.response_apply]
  have hchannels : ActualRootGroupedChannel.channel order horder queue selection tagged = fun group =>
      (unprojectedChannel order horder queue selection tagged group).comp
        (PairedRootProjection.projector selection tagged group) :=
    funext (channel_eq_comp order horder queue selection tagged)
  rw [hchannels, GroupedFamilyComposition.response_comp, PairedRootProjection.projected_jointInput]

end
end CurrentAFT.ActualRootProjectionData
