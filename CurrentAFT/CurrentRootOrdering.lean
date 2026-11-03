import CurrentAFT.CurrentGroupSourcePadding

/-! Sorted block ordinals for tagged and retained roots. The runtime
ordering filters the supplied bounded tag list and compares the selected
indices; it does not enumerate the complement of the body population. -/
namespace CurrentAFT.CurrentRootOrdering
open AFT ActualBlockFock TaggedSelection PairedRootPlacement
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount

def blockNumbering (security : ℕ) : BlockIndex security ≃
    Fin (Parameters.legCount security + (centerCount security + Parameters.modulus security)) :=
  (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv

def isKept {security r s : ℕ} (selection : Selection security r s) (index : BlockIndex security) : Prop :=
  (∀ primary, index ≠ .inl (selection.primary primary)) ∧
    (∀ compensator, index ≠ .inr (.inl (selection.compensator compensator))) ∧
    (∀ body, index ≠ .inr (.inl (selection.body body)))

instance isKeptDecidable {security r s : ℕ} (selection : Selection security r s) : DecidablePred (isKept selection) :=
  fun index => by unfold isKept; infer_instance

def keptTags {security r s : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security)) :
    Finset (BlockIndex security) := tagged.filter (isKept selection)

def tagIndices {security : ℕ} (tagged : Finset (BlockIndex security)) :=
  tagged.map (blockNumbering security).toEmbedding

def keptIndices {security r s : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security)) :=
  tagIndices (keptTags selection tagged)

def numberedTags {security : ℕ} (tagged : Finset (BlockIndex security)) : tagIndices tagged ≃ tagged where
  toFun index := ⟨(blockNumbering security).symm index.val, by
    obtain ⟨original, ho, he⟩ := Finset.mem_map.mp index.property
    simpa only [← he, Equiv.toEmbedding_apply, Equiv.symm_apply_apply] using ho⟩
  invFun index := ⟨blockNumbering security index.val, Finset.mem_map.mpr ⟨index.val, index.property, rfl⟩⟩
  left_inv index := by apply Subtype.ext; exact Equiv.apply_symm_apply _ _
  right_inv index := by apply Subtype.ext; exact Equiv.symm_apply_apply _ _

def tagOrdering {security : ℕ} (tagged : Finset (BlockIndex security)) : Fin tagged.card ≃ tagged :=
  (Finset.orderIsoOfFin (tagIndices tagged) (Finset.card_map _)).toEquiv.trans (numberedTags tagged)

theorem isKept_iff {security r s : ℕ} (selection : Selection security r s) (index : BlockIndex security) :
    isKept selection index ↔ index ∈ selection.kept := by
  classical
  simp only [Selection.kept, Finset.mem_sdiff, Finset.mem_univ, true_and,
    Selection.removed, Finset.mem_map, Finset.mem_univ, true_and, not_exists]
  constructor
  · rintro ⟨hp, hc, hb⟩ (primary | (compensator | body))
    · exact (hp primary).symm
    · exact (hc compensator).symm
    · exact (hb body).symm
  · intro h
    exact ⟨fun p hp => h (.inl p) hp.symm, fun c hc => h (.inr (.inl c)) hc.symm,
      fun b hb => h (.inr (.inr b)) hb.symm⟩

def keptTagsEquiv {security r s : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security)) :
    keptTags selection tagged ≃ HitKept selection tagged where
  toFun index := ⟨⟨index.val, (isKept_iff selection index.val).mp (Finset.mem_filter.mp index.property).2⟩,
    (Finset.mem_filter.mp index.property).1⟩
  invFun index := ⟨index.val.val, Finset.mem_filter.mpr
    ⟨index.property, (isKept_iff selection index.val.val).mpr index.val.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

def keptOrdering {security r s : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security)) :
    Fin (keptIndices selection tagged).card ≃ HitKept selection tagged :=
  ((Finset.orderIsoOfFin (keptIndices selection tagged) rfl).toEquiv.trans
    (numberedTags (keptTags selection tagged))).trans (keptTagsEquiv selection tagged)

theorem kept_count_le {security r s : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security)) :
    (keptIndices selection tagged).card ≤ tagged.card := by
  unfold keptIndices tagIndices keptTags
  rw [Finset.card_map]
  exact Finset.card_filter_le _ _

theorem tagOrdering_number {security : ℕ} (tagged : Finset (BlockIndex security)) (index : Fin tagged.card) :
    blockNumbering security (tagOrdering tagged index).val =
      (Finset.orderIsoOfFin (tagIndices tagged) (Finset.card_map _) index).val := by
  exact (blockNumbering security).apply_symm_apply _

end CurrentAFT.CurrentRootOrdering
