import CurrentAFT.RationalPackedRootSigned

/-! # The untagged references in the native joint source program -/
namespace CurrentAFT.RationalPackedRootProgram
open AFT TaggedSelection PairedRootPlacement CurrentGroupSourcePadding CurrentRootOrdering
  CurrentRootSlotIndex CycleRootExpansion
open ActualBlockFock (BlockIndex)
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance packedUntaggedFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance packedUntaggedSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} : DecidableEq (Sigma Slots) := Classical.decEq _
local instance packedUntaggedSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
local instance packedUntaggedProdDecidableEq {Left Right : Type*} : DecidableEq (Left × Right) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount rootReference

theorem taggedSlot_iff {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (root : Slot selection tagged) :
    (∃ index, (actualMetadata selection tagged).taggedSlots index =
      ((ordering selection tagged).symm root.fst, slotNumber selection tagged root)) ↔
      rootEmbedding selection tagged root ∈ tagged := by
  constructor
  · rintro ⟨index, h⟩
    change CurrentRootSlotIndex.tagPosition selection tagged (ordering selection tagged)
      (tagOrdering tagged index) = _ at h
    rw [tagPosition_eq] at h
    have he := congrArg finProdFinEquiv h
    change CurrentRootSlotIndex.encode selection tagged (ordering selection tagged)
      (tagEmbedding selection tagged (tagOrdering tagged index)) =
      CurrentRootSlotIndex.encode selection tagged (ordering selection tagged) root at he
    have hr : tagEmbedding selection tagged (tagOrdering tagged index) = root := by
      have hd := congrArg (CurrentRootSlotIndex.decode selection tagged (ordering selection tagged)) he
      simpa only [decode_encode, Option.some.injEq] using hd
    rw [← hr, tag_image]
    exact (tagOrdering tagged index).property
  · intro h
    let tag : tagged := ⟨rootEmbedding selection tagged root, h⟩
    have hr : tagEmbedding selection tagged tag = root :=
      (rootEmbedding selection tagged).injective (tag_image selection tagged tag)
    refine ⟨(tagOrdering tagged).symm tag, ?_⟩
    change CurrentRootSlotIndex.tagPosition selection tagged (ordering selection tagged)
      (tagOrdering tagged ((tagOrdering tagged).symm tag)) = _
    rw [Equiv.apply_symm_apply, tagPosition_eq, hr]

theorem sourceEmbedding_mem_iff {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (root : Slot selection tagged) :
    root ∈ Finset.univ.map (PairedRootInput.sourceEmbedding selection tagged) ↔
      rootEmbedding selection tagged root ∈ tagged := by
  constructor
  · intro h
    obtain ⟨index, _, he⟩ := Finset.mem_map.mp h
    rw [← he]
    change rootEmbedding selection tagged
      (tagEmbedding selection tagged (tagged.equivFin.symm index)) ∈ tagged
    rw [tag_image]
    exact (tagged.equivFin.symm index).property
  · intro h
    let tag : tagged := ⟨rootEmbedding selection tagged root, h⟩
    refine Finset.mem_map.mpr ⟨tagged.equivFin tag, Finset.mem_univ _, ?_⟩
    change tagEmbedding selection tagged (tagged.equivFin.symm (tagged.equivFin tag)) = root
    rw [Equiv.symm_apply_apply]
    exact (rootEmbedding selection tagged).injective (tag_image selection tagged tag)

theorem rootActive_slot {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (root : Slot selection tagged) :
    rootActive (nativeRole selection tagged root.fst) (slotNumber selection tagged root) := by
  rcases root with ⟨(primary | ordinary) | kept, slot⟩
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr rfl

def untaggedFactor {security r s : ℕ} (bits : ℕ) (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (source : PairedRootInput.GroupInput selection tagged)
    (root : Slot selection tagged) : ℚ :=
  if rootEmbedding selection tagged root ∈ tagged then 1 else
    RootSignedMassProgram.referenceEntry security bits ((source root.fst).1 root.snd).val

theorem nativeUntagged_factor {security r s : ℕ} (bits : ℕ) (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (source : PairedRootInput.GroupInput selection tagged)
    (root : Slot selection tagged) :
    (if rootActive ((actualMetadata selection tagged).roles ((ordering selection tagged).symm root.fst))
        (slotNumber selection tagged root) ∧ ¬∃ index,
          (actualMetadata selection tagged).taggedSlots index =
            ((ordering selection tagged).symm root.fst, slotNumber selection tagged root)
      then RootSignedMassProgram.referenceEntry security bits
        (sourceWord security (groupCount selection tagged) (sourceIndex selection tagged source)
          ((ordering selection tagged).symm root.fst) (slotNumber selection tagged root).castSucc) else 1) =
      untaggedFactor bits selection tagged source root := by
  rw [sourceIndex_slot]
  have ha : rootActive ((actualMetadata selection tagged).roles ((ordering selection tagged).symm root.fst))
      (slotNumber selection tagged root) := by
    change rootActive (nativeRole selection tagged (ordering selection tagged ((ordering selection tagged).symm root.fst))) _
    rw [Equiv.apply_symm_apply]
    exact rootActive_slot selection tagged root
  unfold untaggedFactor
  by_cases ht : rootEmbedding selection tagged root ∈ tagged <;> simp only [taggedSlot_iff, ha, ht, not_true_eq_false,
    not_false_eq_true, true_and, ite_true, ite_false]

theorem untagged_sourceIndex {security r s : ℕ} (bits : ℕ) (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (source : PairedRootInput.GroupInput selection tagged) :
    untagged security bits (actualMetadata selection tagged)
      (sourceWord security (groupCount selection tagged) (sourceIndex selection tagged source)) =
      ∏ root : Slot selection tagged, untaggedFactor bits selection tagged source root := by
  unfold untagged
  have hp := (ordering selection tagged).symm.prod_comp (fun group => ∏ slot : Fin 2,
    if rootActive ((actualMetadata selection tagged).roles group) slot ∧ ¬∃ tag,
      (actualMetadata selection tagged).taggedSlots tag = (group, slot) then
        RootSignedMassProgram.referenceEntry security bits
          (sourceWord security (groupCount selection tagged) (sourceIndex selection tagged source) group slot.castSucc) else (1 : ℚ))
  trans ∏ group : ActiveGroup selection tagged, ∏ slot : Fin 2,
    if rootActive ((actualMetadata selection tagged).roles ((ordering selection tagged).symm group)) slot ∧ ¬∃ tag,
      (actualMetadata selection tagged).taggedSlots tag = ((ordering selection tagged).symm group, slot) then
        RootSignedMassProgram.referenceEntry security bits
          (sourceWord security (groupCount selection tagged) (sourceIndex selection tagged source)
            ((ordering selection tagged).symm group) slot.castSucc) else 1
  · convert hp.symm using 1
    apply Finset.prod_congr rfl
    intro group _
    apply Finset.prod_congr rfl
    intro slot _
    split_ifs <;> rfl
  rw [Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro group _
  rcases group with (primary | ordinary) | kept
  · change (∏ slot : Fin 2, _) = ∏ slot : Fin 2, _
    apply Finset.prod_congr rfl
    intro slot _
    exact nativeUntagged_factor bits selection tagged source ⟨.inl (.inl primary), slot⟩
  · change (∏ slot : Fin 2, _) = ∏ slot : Fin 1, _
    rw [Fin.prod_univ_two, Fin.prod_univ_one]
    have hf := nativeUntagged_factor bits selection tagged source ⟨.inl (.inr ordinary), (0 : Fin 1)⟩
    have hinactive : ¬rootActive ((actualMetadata selection tagged).roles
      ((ordering selection tagged).symm (.inl (.inr ordinary)))) (1 : Fin 2) := by
      simp [actualMetadata, nativeRole, rootActive]
    simpa only [hinactive, false_and, ite_false, mul_one] using hf
  · change (∏ slot : Fin 2, _) = ∏ slot : Fin 1, _
    rw [Fin.prod_univ_two, Fin.prod_univ_one]
    have hf := nativeUntagged_factor bits selection tagged source ⟨.inr kept, (0 : Fin 1)⟩
    have hinactive : ¬rootActive ((actualMetadata selection tagged).roles
      ((ordering selection tagged).symm (.inr kept))) (1 : Fin 2) := by
      simp only [actualMetadata, Equiv.apply_symm_apply, rootActive, nativeRole]
      rcases kept.val.val with leg | (center | queue) <;> simp
    simpa only [hinactive, false_and, ite_false, mul_one] using hf

theorem untaggedWeight_product {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (source : PairedRootInput.GroupInput selection tagged) :
    RootWeightedSynthesis.untaggedWeight selection tagged source =
      ∏ root : Slot selection tagged, if rootEmbedding selection tagged root ∈ tagged then 1 else
        (rootReference security).weight ((source root.fst).1 root.snd) := by
  unfold RootWeightedSynthesis.untaggedWeight
  have hc : (Finset.univ.map (PairedRootInput.sourceEmbedding selection tagged))ᶜ =
      Finset.univ.filter (fun root => rootEmbedding selection tagged root ∉ tagged) := by
    ext root
    simp only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, sourceEmbedding_mem_iff]
  rw [hc, Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro root _
  by_cases ht : rootEmbedding selection tagged root ∈ tagged <;> simp only [ht, not_true_eq_false,
    not_false_eq_true, ite_true, ite_false]

end
end CurrentAFT.RationalPackedRootProgram
