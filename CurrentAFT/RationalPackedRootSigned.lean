import CurrentAFT.RationalPackedRootSource

/-! # The sorted tagged-root entry computes the original joint signed cycle mass -/
namespace CurrentAFT.RationalPackedRootProgram
open AFT ActualBlockFock TaggedSelection PairedRootPlacement CurrentGroupSourcePadding CurrentRootOrdering
  CurrentRootSlotIndex CurrentRectangleIndex GroupSourcePadding RationalRootGroupProgram CycleRootExpansion
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance packedSignedFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance packedSignedVertexDecidableEq (security : ℕ) : DecidableEq (Vertex security) := instDecidableEqFin _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount rootReference rootLaw

theorem sourceNatural_slot {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (source : PairedRootInput.GroupInput selection tagged)
    (root : CurrentRootSlotIndex.Slot selection tagged) :
    RationalRootGroupProgram.sourceNatural selection tagged root.fst (source root.fst)
      (slotNumber selection tagged root).castSucc = ((source root.fst).1 root.snd).val := by
  rcases root with ⟨(primary | ordinary) | kept, slot⟩
  · change Fin 2 at slot
    fin_cases slot <;> rfl
  · change Fin 1 at slot
    have hs : slot = 0 := Subsingleton.elim _ _
    subst slot
    rfl
  · change Fin 1 at slot
    have hs : slot = 0 := Subsingleton.elim _ _
    subst slot
    rfl

theorem sourceIndex_slot {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (source : PairedRootInput.GroupInput selection tagged)
    (root : CurrentRootSlotIndex.Slot selection tagged) :
    sourceWord security (groupCount selection tagged) (sourceIndex selection tagged source)
      ((ordering selection tagged).symm root.fst) (slotNumber selection tagged root).castSucc =
      ((source root.fst).1 root.snd).val := by
  rw [sourceWord_sourceIndex]
  dsimp only
  rw [Equiv.apply_symm_apply, sourceNatural_slot]

def sortedOutput {security r s : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (source : PairedRootInput.GroupInput selection tagged) : Fin tagged.card → Root security :=
  fun index => (source (tagEmbedding selection tagged (tagOrdering tagged index)).fst).1
    (tagEmbedding selection tagged (tagOrdering tagged index)).snd

def sortedLabels {security : ℕ} (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ Vertex security) :
    CycleSelections.Selection (Parameters.bodySize security) tagged.card :=
  (tagOrdering tagged).toEmbedding.trans ((Function.Embedding.subtype _).trans layout.toEmbedding)

theorem signed_sourceIndex {security r s : ℕ} (bits : ℕ) (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (source : PairedRootInput.GroupInput selection tagged) :
    signed security bits (actualMetadata selection tagged)
      (sourceWord security (groupCount selection tagged) (sourceIndex selection tagged source)) =
      RootSignedMassProgram.weightedEntry security bits tagged.card (fun index => (sortedOutput selection tagged source index).val) := by
  unfold signed
  congr 1
  funext index
  simp only [actualMetadata, CurrentRootSlotIndex.taggedSlots, tagPosition_eq]
  exact sourceIndex_slot selection tagged source _

theorem sorted_weightedCoefficient {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ Vertex security)
    (source : PairedRootInput.GroupInput selection tagged) :
    (rootLaw security).expectation (fun roots => ∏ index,
      ((if roots (sortedLabels tagged layout index) = sortedOutput selection tagged source index then (1 : ℝ) else 0) -
        (rootReference security).weight (sortedOutput selection tagged source index))) =
      RootWeightedSynthesis.weightedCoefficient selection tagged layout source := by
  apply congrArg (rootLaw security).expectation
  funext roots
  let test := fun tag : tagged =>
    ((if roots (layout tag.val) = (source (tagEmbedding selection tagged tag).fst).1 (tagEmbedding selection tagged tag).snd then (1 : ℝ) else 0) -
      (rootReference security).weight ((source (tagEmbedding selection tagged tag).fst).1 (tagEmbedding selection tagged tag).snd))
  change (∏ index : Fin tagged.card, test (tagOrdering tagged index)) =
    ∏ index : Fin tagged.card, test (tagged.equivFin.symm index)
  exact (tagOrdering tagged).prod_comp test |>.trans (tagged.equivFin.symm.prod_comp test).symm

theorem signed_error {security r s : ℕ} (bits : ℕ) (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ Vertex security)
    (hroom : tagged.card ≤ Parameters.bodySize security) (source : PairedRootInput.GroupInput selection tagged) :
    |(signed security bits (actualMetadata selection tagged)
      (sourceWord security (groupCount selection tagged) (sourceIndex selection tagged source)) : ℝ) -
      RootWeightedSynthesis.weightedCoefficient selection tagged layout source| ≤ (4 * tagged.card : ℕ) / (2 : ℝ)^bits := by
  letI : DecidableEq (Fin tagged.card) := instDecidableEqFin _
  rw [signed_sourceIndex]
  have h := RootSignedMassProgram.weightedEntry_error security bits tagged.card hroom
    (sortedLabels tagged layout) (sortedOutput selection tagged source)
  have hmass := RootSignedMassProgram.actual_weighted_coefficient security tagged.card
    (sortedLabels tagged layout) (sortedOutput selection tagged source)
  rw [FiniteDist.expectation_map] at hmass
  have heq := hmass.trans (sorted_weightedCoefficient selection tagged layout source)
  rw [heq] at h
  exact h

theorem weightedCoefficient_bound {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ Vertex security)
    (source : PairedRootInput.GroupInput selection tagged) :
    |RootWeightedSynthesis.weightedCoefficient selection tagged layout source| ≤ 1 := by
  apply CalibrationCoordinateError.expectation_abs_bound
  intro roots
  rw [Finset.abs_prod]
  apply Finset.prod_le_one (fun _ _ => abs_nonneg _)
  intro index _
  have hlo := (rootReference security).nonneg (RootWeightedSynthesis.taggedOutput selection tagged source index)
  have hhi := (rootReference security).atom_le_one (RootWeightedSynthesis.taggedOutput selection tagged source index)
  split_ifs <;> exact abs_le.mpr ⟨by linarith, by linarith⟩

end
end CurrentAFT.RationalPackedRootProgram
