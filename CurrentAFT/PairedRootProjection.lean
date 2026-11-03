import CurrentAFT.PairedRootCentering
import CurrentAFT.RootCoordinateProjection
import CurrentAFT.GroupedRootUpdates
import CurrentAFT.DependentTensorFixedInput

/-! # The root mask preserves the actual joint selected coefficient

Tagged coordinates are centered and unused root coordinates are averaged.
The full joint density is unchanged under every resulting local projection.
-/
namespace CurrentAFT.PairedRootProjection
open AFT ActualBlockFock TaggedSelection PairedRootPlacement PairedRootInput
  PairedRootCentering ControlCoordinates GroupedRootUpdates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
local instance classicalSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} : DecidableEq (Sigma Slots) := Classical.decEq _
local instance slotDecidableEq {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (group : ActiveGroup selection tagged) :
    DecidableEq (groupRootSlots selection tagged group) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount

theorem source_range_iff {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (slot : Sigma (groupRootSlots selection tagged)) :
    slot ∈ Set.range (sourceEmbedding selection tagged) ↔ rootEmbedding selection tagged slot ∈ tagged := by
  constructor
  · rintro ⟨index, rfl⟩
    change rootEmbedding selection tagged (tagEmbedding selection tagged (tagged.equivFin.symm index)) ∈ tagged
    rw [tag_image]
    exact (tagged.equivFin.symm index).property
  · intro hslot
    refine ⟨tagged.equivFin ⟨rootEmbedding selection tagged slot, hslot⟩, ?_⟩
    apply (rootEmbedding selection tagged).injective
    simp only [sourceEmbedding, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
      Equiv.symm_apply_apply, tag_image]

theorem jointInput_flat {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s)
    (word : GroupInput selection tagged) :
    jointInput selection tagged layout kernel word =
      rootDensity selection tagged layout (roots (groupRootSlots selection tagged) (ControlInput selection tagged) word) *
        controlKernel selection tagged kernel (controls (groupRootSlots selection tagged) (ControlInput selection tagged) word) := rfl

theorem tagged_update_mean {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s)
    (word : GroupInput selection tagged) (group : ActiveGroup selection tagged)
    (slot : groupRootSlots selection tagged group)
    (htag : rootEmbedding selection tagged ⟨group, slot⟩ ∈ tagged) :
    (CycleRootExpansion.rootReference security).expectation (fun value =>
      jointInput selection tagged layout kernel
        (updateRoot (groupRootSlots selection tagged) (ControlInput selection tagged) word group slot value)) = 0 := by
  obtain ⟨index, hindex⟩ := (source_range_iff selection tagged ⟨group, slot⟩).mpr htag
  simp_rw [jointInput_flat, roots_updateRoot, controls_updateRoot]
  rw [← hindex]
  unfold FiniteDist.expectation
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul, rootDensity_centered selection tagged layout index, zero_mul]

theorem untagged_update_invariant {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s)
    (word : GroupInput selection tagged) (group : ActiveGroup selection tagged)
    (slot : groupRootSlots selection tagged group)
    (htag : rootEmbedding selection tagged ⟨group, slot⟩ ∉ tagged) (value : CycleRootExpansion.Root security) :
    jointInput selection tagged layout kernel
      (updateRoot (groupRootSlots selection tagged) (ControlInput selection tagged) word group slot value) =
        jointInput selection tagged layout kernel word := by
  rw [jointInput_flat, roots_updateRoot, controls_updateRoot, jointInput_flat]
  rw [rootDensity_unselected_update selection tagged layout ⟨group, slot⟩
    (fun h => htag ((source_range_iff selection tagged ⟨group, slot⟩).mp h))]

def mask {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (group : ActiveGroup selection tagged) :
    List (groupRootSlots selection tagged group × Bool) :=
  (Finset.univ : Finset (groupRootSlots selection tagged group)).toList.map
    (fun slot => (slot, decide (rootEmbedding selection tagged ⟨group, slot⟩ ∈ tagged)))

def projector {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (group : ActiveGroup selection tagged) :
    (((groupRootSlots selection tagged group → CycleRootExpansion.Root security) ×
      ControlInput selection tagged group) → ℝ) →ₗ[ℝ]
    (((groupRootSlots selection tagged group → CycleRootExpansion.Root security) ×
      ControlInput selection tagged group) → ℝ) :=
  RootCoordinateProjection.sequence (CycleRootExpansion.rootReference security) (mask selection tagged group)

theorem projector_energy_le {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (group : ActiveGroup selection tagged)
    (score : ((groupRootSlots selection tagged group → CycleRootExpansion.Root security) ×
      ControlInput selection tagged group) → ℝ) :
    (GroupedSourceNorm.groupReference (groupRootSlots selection tagged) (ControlInput selection tagged)
      (CycleRootExpansion.rootReference security) (controlReference selection tagged) group).l2Sq
        (projector selection tagged group score) ≤
    (GroupedSourceNorm.groupReference (groupRootSlots selection tagged) (ControlInput selection tagged)
      (CycleRootExpansion.rootReference security) (controlReference selection tagged) group).l2Sq score :=
  RootCoordinateProjection.sequence_energy_le (CycleRootExpansion.rootReference security)
    (controlReference selection tagged group) (mask selection tagged group) score

theorem projector_fixes_slice {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s)
    (word : GroupInput selection tagged) (group : ActiveGroup selection tagged) :
    projector selection tagged group (fun sample => jointInput selection tagged layout kernel (Function.update word group sample)) =
      fun sample => jointInput selection tagged layout kernel (Function.update word group sample) := by
  apply RootCoordinateProjection.sequence_fixed
  intro item hitem
  obtain ⟨slot, _, rfl⟩ := List.mem_map.mp hitem
  by_cases htag : rootEmbedding selection tagged ⟨group, slot⟩ ∈ tagged
  · simp only [htag, decide_true, RootCoordinateProjection.coordinate, if_true]
    apply RootCoordinateProjection.center_fixed_of_centered
    intro sample
    simp_rw [← updateRoot_updated_group]
    exact tagged_update_mean selection tagged layout kernel (Function.update word group sample) group slot htag
  · simp only [htag, decide_false, RootCoordinateProjection.coordinate, Bool.false_eq_true, if_false]
    apply RootCoordinateProjection.average_fixed_of_invariant
    intro sample value
    rw [← updateRoot_updated_group]
    exact untagged_update_invariant selection tagged layout kernel (Function.update word group sample) group slot htag value

theorem projected_jointInput {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s) :
    DependentTensorChannel.apply (projector selection tagged) (jointInput selection tagged layout kernel) =
      jointInput selection tagged layout kernel :=
  DependentTensorFixedInput.apply_eq_self _ _ (fun group word =>
    projector_fixes_slice selection tagged layout kernel word group)

theorem projected_response_eq {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s)
    {Output : ActiveGroup selection tagged → Type*} [∀ group, Fintype (Output group)]
    (channels : ∀ group, (((groupRootSlots selection tagged group → CycleRootExpansion.Root security) ×
      ControlInput selection tagged group) → ℝ) →ₗ[ℝ] (Output group → ℝ)) :
    DependentTensorChannel.apply (fun group => (channels group).comp (projector selection tagged group))
        (jointInput selection tagged layout kernel) =
      DependentTensorChannel.apply channels (jointInput selection tagged layout kernel) := by
  rw [DependentTensorComposition.apply_comp, projected_jointInput]

end
end CurrentAFT.PairedRootProjection
