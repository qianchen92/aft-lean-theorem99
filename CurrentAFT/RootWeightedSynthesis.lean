import CurrentAFT.RootReferenceColumns
import CurrentAFT.RootSignedMassProgram

/-! # The actual root response with signed masses instead of root densities

Every tagged root reference factor is absorbed into its centered cycle
coefficient. The remaining factors are ordinary reference probabilities.
This is a data identity in the current canonical family algebra, including
zero root atoms, and exposes the bounded sparse-cycle program interface.
-/
namespace CurrentAFT.RootWeightedSynthesis
open AFT ActualBlockFock TaggedSelection PairedRootPlacement PairedRootInput
  CycleRootExpansion ControlCoordinates GradedControlAlgebra
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance nativeVertexDecidableEq (security : ℕ) : DecidableEq (Vertex security) := instDecidableEqFin _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
local instance classicalProdDecidableEq {Left Right : Type*} : DecidableEq (Left × Right) := Classical.decEq _
local instance classicalSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} : DecidableEq (Sigma Slots) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount rootReference

abbrev RootSlot {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) := Sigma (groupRootSlots selection tagged)

def taggedOutput {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (source : GroupInput selection tagged) : Fin tagged.card → Root security :=
  fun index => (source (sourceEmbedding selection tagged index).fst).1 (sourceEmbedding selection tagged index).snd

def untaggedWeight {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (source : GroupInput selection tagged) : ℝ :=
  ∏ slot ∈ (Finset.univ.map (sourceEmbedding selection tagged))ᶜ,
    (rootReference security).weight ((source slot.fst).1 slot.snd)

def weightedCoefficient {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ Vertex security)
    (source : GroupInput selection tagged) : ℝ :=
  (rootLaw security).expectation
    (fun input => ∏ index, ((if input (labels tagged layout index) = taggedOutput selection tagged source index then (1 : ℝ) else 0) -
      (rootReference security).weight (taggedOutput selection tagged source index)))

theorem reference_product {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (source : GroupInput selection tagged) :
    (∏ group, ∏ slot, (rootReference security).weight ((source group).1 slot)) =
      (∏ index, (rootReference security).weight (taggedOutput selection tagged source index)) *
        untaggedWeight selection tagged source := by
  have h := Finset.prod_mul_prod_compl (Finset.univ.map (sourceEmbedding selection tagged))
    (fun slot : RootSlot selection tagged => (rootReference security).weight ((source slot.fst).1 slot.snd))
  simpa only [Finset.prod_map, Fintype.prod_sigma, taggedOutput, untaggedWeight] using h.symm

theorem weighted_jointInput {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ Vertex security)
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s)
    (source : GroupInput selection tagged) :
    jointInput selection tagged layout kernel source *
        (∏ group, ∏ slot, (rootReference security).weight ((source group).1 slot)) =
      controlKernel selection tagged kernel (fun group => (source group).2) *
        untaggedWeight selection tagged source * weightedCoefficient selection tagged layout source := by
  letI : DecidableEq (Fin tagged.card) := instDecidableEqFin _
  have h := RootSignedMassProgram.actual_weighted_coefficient security tagged.card (labels tagged layout)
    (taggedOutput selection tagged source)
  rw [FiniteDist.expectation_map] at h
  change (∏ index, (rootReference security).weight (taggedOutput selection tagged source index)) *
    selectedCoefficient security tagged.card (labels tagged layout) (taggedOutput selection tagged source) =
      weightedCoefficient selection tagged layout source at h
  rw [← h, reference_product]
  unfold jointInput
  change selectedCoefficient security tagged.card (labels tagged layout) (taggedOutput selection tagged source) * _ * _ = _
  ring

/-- Literal sparse-mass expansion of the actual root response. No local
control or root source is factored, and no root probability is inverted. -/
theorem response_eq {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (layout : BlockIndex security ≃ Vertex security)
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s) :
    ActualRootResponse.response order horder queue selection tagged layout kernel =
      ∑ source : GroupInput selection tagged,
        (controlKernel selection tagged kernel (fun group => (source group).2) *
          untaggedWeight selection tagged source * weightedCoefficient selection tagged layout source) •
            ∏ group, RootReferenceColumns.reducedColumn order horder queue selection tagged group (source group) := by
  rw [ActualRootProjectionData.response_unprojected, GroupedFamilyIdentity.response_eq]
  apply Finset.sum_congr rfl
  intro source _
  have hcolumn (group : ActiveGroup selection tagged) :
      ActualRootProjectionData.unprojectedChannel order horder queue selection tagged group
        (@Pi.single (ActualRootGroupedChannel.Input selection tagged group) (fun _ => ℝ) (fun _ => Real.instZero)
          (Classical.decEq _) (source group) 1) =
        (∏ slot, (rootReference security).weight ((source group).1 slot)) •
          RootReferenceColumns.reducedColumn order horder queue selection tagged group (source group) := by
    convert RootReferenceColumns.unprojected_column order horder queue selection tagged group (source group) using 1
    congr 1
    funext word
    by_cases hequal : word = source group <;> simp only [Pi.single_apply, hequal, if_true, if_false]
  simp_rw [hcolumn, Finset.prod_smul, smul_smul]
  rw [weighted_jointInput]

theorem weightedCoefficient_error {security r s : ℕ} (securityBits : ℕ) (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (hroom : tagged.card ≤ Parameters.bodySize security)
    (layout : BlockIndex security ≃ Vertex security) (source : GroupInput selection tagged) :
    |(RootSignedMassProgram.weightedEntry security securityBits tagged.card
        (fun index => (taggedOutput selection tagged source index).val) : ℝ) -
      weightedCoefficient selection tagged layout source| ≤ 4 * tagged.card / (2 : ℝ)^securityBits := by
  letI : DecidableEq (Fin tagged.card) := instDecidableEqFin _
  have h := RootSignedMassProgram.weightedEntry_error security securityBits tagged.card hroom
    (labels tagged layout) (taggedOutput selection tagged source)
  rw [RootSignedMassProgram.actual_weighted_coefficient, FiniteDist.expectation_map] at h
  simpa only [weightedCoefficient, Nat.cast_mul, Nat.cast_ofNat] using h

end
end CurrentAFT.RootWeightedSynthesis
