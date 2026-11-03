import CurrentAFT.PairedRootPlacement

/-! # Exact tag counts in the actual paired groups

A paired group with two tagged roots consumes two output degrees. All
other active groups consume at least one. These finite counts permit a
degree cutoff without summing all root subsets in a norm bound.
-/
namespace CurrentAFT.PairedRootDegrees
open AFT ActualBlockFock TaggedSelection PairedRootPlacement
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
local instance classicalSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} : DecidableEq (Sigma Slots) := Classical.decEq _

abbrev TaggedSlot {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (group : ActiveGroup selection tagged) :=
  {slot : groupRootSlots selection tagged group // rootEmbedding selection tagged ⟨group, slot⟩ ∈ tagged}

def physicalTagsEquiv {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) :
    tagged ≃ {slot : Sigma (groupRootSlots selection tagged) // rootEmbedding selection tagged slot ∈ tagged} where
  toFun index := ⟨tagEmbedding selection tagged index, by rw [tag_image]; exact index.property⟩
  invFun slot := ⟨rootEmbedding selection tagged slot.val, slot.property⟩
  left_inv index := by apply Subtype.ext; exact tag_image selection tagged index
  right_inv slot := by
    apply Subtype.ext
    apply (rootEmbedding selection tagged).injective
    exact tag_image selection tagged ⟨rootEmbedding selection tagged slot.val, slot.property⟩

def groupedTagsEquiv {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) :
    {slot : Sigma (groupRootSlots selection tagged) // rootEmbedding selection tagged slot ∈ tagged} ≃
      Sigma (TaggedSlot selection tagged) where
  toFun slot := ⟨slot.val.fst, ⟨slot.val.snd, slot.property⟩⟩
  invFun slot := ⟨⟨slot.fst, slot.snd.val⟩, slot.snd.property⟩
  left_inv := by rintro ⟨⟨group, slot⟩, hslot⟩; rfl
  right_inv := by rintro ⟨group, ⟨slot, hslot⟩⟩; rfl

def tagCount {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (group : ActiveGroup selection tagged) : ℕ :=
  Fintype.card (TaggedSlot selection tagged group)

theorem sum_tagCount {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) :
    ∑ group, tagCount selection tagged group = tagged.card := by
  have h := Fintype.card_congr ((physicalTagsEquiv selection tagged).trans (groupedTagsEquiv selection tagged))
  simpa only [Fintype.card_coe, Fintype.card_sigma, tagCount] using h.symm

def minimumDegree {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (group : ActiveGroup selection tagged) : ℕ :=
  max 1 (tagCount selection tagged group)

theorem tags_le_degree {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) :
    tagged.card ≤ ∑ group, minimumDegree selection tagged group := by
  rw [← sum_tagCount selection tagged]
  exact Finset.sum_le_sum (fun group _ => le_max_right 1 (tagCount selection tagged group))

theorem tagCount_le_slots {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (group : ActiveGroup selection tagged) :
    tagCount selection tagged group ≤ Fintype.card (groupRootSlots selection tagged group) :=
  Fintype.card_subtype_le _

theorem ordinary_minimumDegree {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (index : Fin s) :
    minimumDegree selection tagged (.inl (.inr index)) = 1 := by
  have h := tagCount_le_slots selection tagged (.inl (.inr index))
  change tagCount selection tagged (.inl (.inr index)) ≤ Fintype.card (Fin 1) at h
  norm_num only [Fintype.card_fin] at h
  exact max_eq_left h

theorem kept_minimumDegree {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (index : HitKept selection tagged) :
    minimumDegree selection tagged (.inr index) = 1 := by
  have h := tagCount_le_slots selection tagged (.inr index)
  change tagCount selection tagged (.inr index) ≤ Fintype.card (Fin 1) at h
  norm_num only [Fintype.card_fin] at h
  exact max_eq_left h

theorem primary_minimumDegree_le_two {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (index : Fin r) :
    minimumDegree selection tagged (.inl (.inl index)) ≤ 2 := by
  have h := tagCount_le_slots selection tagged (.inl (.inl index))
  change tagCount selection tagged (.inl (.inl index)) ≤ Fintype.card (Fin 2) at h
  norm_num only [Fintype.card_fin] at h
  exact max_le (by omega) h

theorem primary_tagCount {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (index : Fin r) :
    tagCount selection tagged (.inl (.inl index)) =
      (if Sum.inr (Sum.inl (selection.compensator index)) ∈ tagged then 1 else 0) +
      (if Sum.inl (selection.primary index) ∈ tagged then 1 else 0) := by
  unfold tagCount TaggedSlot
  rw [Fintype.card_subtype]
  change (Finset.univ.filter (fun slot : Fin 2 =>
    rootEmbedding selection tagged ⟨.inl (.inl index), slot⟩ ∈ tagged)).card = _
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, Fin.sum_univ_two]
  rfl

theorem primary_minimumDegree_two_requires_attachment {security r s : ℕ}
    (selection : Selection security r s) (tagged : Finset (BlockIndex security)) (index : Fin r)
    (hdegree : minimumDegree selection tagged (.inl (.inl index)) = 2) :
    Sum.inl (selection.primary index) ∈ tagged := by
  have hcount := primary_tagCount selection tagged index
  unfold minimumDegree at hdegree
  by_contra hnot
  rw [if_neg hnot] at hcount
  split_ifs at hcount <;> omega

end
end CurrentAFT.PairedRootDegrees
