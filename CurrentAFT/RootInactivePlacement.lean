import CurrentAFT.RootBackgroundDenominatorProduct

/-! # Roots outside the active tensor are exactly the untagged kept blocks -/
namespace CurrentAFT.RootInactivePlacement
open AFT ActualBlockFock TaggedSelection PairedRootPlacement
  RootBackgroundDenominatorProduct
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount

theorem active_range_iff {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (block : BlockIndex security) :
    block ∈ Set.range (activeRootEmbedding selection tagged) ↔
      block ∈ selection.removed ∨ block ∈ tagged := by
  constructor
  · rintro ⟨index | index, hindex⟩
    · left
      change selection.removedEmbedding (selectedRootEquiv r s index) = block at hindex
      exact Finset.mem_map.mpr ⟨selectedRootEquiv r s index, Finset.mem_univ _, hindex⟩
    · right
      change index.val.val = block at hindex
      exact hindex ▸ index.property
  · rintro (hremoved | htagged)
    · obtain ⟨index, _, hindex⟩ := Finset.mem_map.mp hremoved
      refine ⟨.inl ((selectedRootEquiv r s).symm index), ?_⟩
      change selection.removedEmbedding ((selectedRootEquiv r s) ((selectedRootEquiv r s).symm index)) = block
      simpa only [Equiv.apply_symm_apply] using hindex
    · exact tagged_in_active_range selection tagged block htagged

theorem root_range_iff {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (block : BlockIndex security) :
    block ∈ Set.range (rootEmbedding selection tagged) ↔
      block ∈ selection.removed ∨ block ∈ tagged := by
  rw [← active_range_iff]
  constructor
  · rintro ⟨index, hindex⟩
    exact ⟨activeSlotsEquiv selection tagged index, hindex⟩
  · rintro ⟨index, hindex⟩
    refine ⟨(activeSlotsEquiv selection tagged).symm index, ?_⟩
    change activeRootEmbedding selection tagged
      ((activeSlotsEquiv selection tagged) ((activeSlotsEquiv selection tagged).symm index)) = block
    simpa only [Equiv.apply_symm_apply] using hindex

theorem root_mem_map_iff {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (block : BlockIndex security) :
    block ∈ Finset.univ.map (rootEmbedding selection tagged) ↔
      block ∈ selection.removed ∨ block ∈ tagged := by
  rw [← root_range_iff]
  simp only [Finset.mem_map, Finset.mem_univ, true_and, Set.mem_range]

abbrev InactiveRoot {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) :=
  {block : BlockIndex security // block ∉ Finset.univ.map (rootEmbedding selection tagged)}

def inactiveEquiv {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) : InactiveRoot selection tagged ≃ InactiveKept selection tagged where
  toFun block :=
    ⟨⟨block.val, by
      have h := block.property
      rw [root_mem_map_iff] at h
      simp only [Selection.kept, Finset.mem_sdiff, Finset.mem_univ, true_and]
      exact fun hremoved => h (.inl hremoved)⟩, by
        have h := block.property
        rw [root_mem_map_iff] at h
        exact fun htagged => h (.inr htagged)⟩
  invFun index := ⟨index.val.val, by
    rw [root_mem_map_iff]
    rintro (hremoved | htagged)
    · exact (Finset.mem_sdiff.mp index.val.property).2 hremoved
    · exact index.property htagged⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem inactiveEquiv_val {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (block : InactiveRoot selection tagged) :
    (inactiveEquiv selection tagged block).val.val = block.val := rfl

@[simp] theorem inactiveEquiv_symm_val {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (index : InactiveKept selection tagged) :
    ((inactiveEquiv selection tagged).symm index).val = index.val.val := rfl

end
end CurrentAFT.RootInactivePlacement
