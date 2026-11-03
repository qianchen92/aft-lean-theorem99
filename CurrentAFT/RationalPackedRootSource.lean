import CurrentAFT.RationalPackedRootProgram
import CurrentAFT.CurrentRootSourceNatural
import CurrentAFT.CurrentRootSlotIndex

/-! # The actual native metadata and source numbering for the packed program -/
namespace CurrentAFT.RationalPackedRootProgram
open AFT ActualBlockFock TaggedSelection PairedRootPlacement CurrentGroupSourcePadding
  CurrentRootOrdering CurrentRootSlotIndex CurrentRectangleIndex GroupSourcePadding RationalRootGroupProgram
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def nativeRole {security r s : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security)) :
    ActiveGroup selection tagged → LocalRole
  | .inl (.inl _) => .primary
  | .inl (.inr _) => .ordinary
  | .inr index => match index.val.val with
    | .inl _ => .leg
    | .inr (.inl _) => .center
    | .inr (.inr _) => .queue

def groupCount {security r s : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security)) : ℕ :=
  (r+s)+(keptIndices selection tagged).card

def ordering {security r s : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security)) :
    Fin (groupCount selection tagged) ≃ ActiveGroup selection tagged :=
  groupOrdering selection tagged (keptOrdering selection tagged)

def actualMetadata {security r s : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security)) :
    Metadata r s (keptIndices selection tagged).card tagged.card where
  roles index := nativeRole selection tagged (ordering selection tagged index)
  taggedSlots := CurrentRootSlotIndex.taggedSlots selection tagged (ordering selection tagged)

def nativeKind : LocalRole → Kind
  | .primary => .primary
  | .ordinary => .ordinary
  | .leg | .center | .queue => .kept

theorem nativeRole_eq {security r s : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (group : ActiveGroup selection tagged) : nativeRole selection tagged group = RationalRootGroupProgram.role selection tagged group := rfl

theorem nativeKind_role {security r s : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (group : ActiveGroup selection tagged) : nativeKind (nativeRole selection tagged group) = groupKind selection tagged group := by
  rcases group with (primary | ordinary) | kept
  · rfl
  · rfl
  · rcases hk : kept.val.val with leg | (center | queue) <;> simp only [nativeRole, hk, nativeKind, groupKind]

theorem validGroup_native (security : ℕ) (role : LocalRole) (word : Fin 3 → Fin (colors security)) :
    validGroup security role (fun slot => (word slot).val) ↔
      GroupSourcePadding.Valid (colors security) (safe security) (nativeKind role) word := by
  cases role <;> rfl

theorem sourceWord_tuple (security groups : ℕ) (word : Fin groups → Fin 3 → Fin (colors security)) :
    sourceWord security groups
      ((tupleEquiv (colors security) (groups*3) (colors_pos security))
        (fun index => word (finProdFinEquiv.symm index).1 (finProdFinEquiv.symm index).2)) =
      fun group slot => (word group slot).val := by
  funext group slot
  change (WeightCoordinates.tupleDecode (colors security) (colors_pos security) (groups*3)
    (WeightCoordinates.tupleCode (colors security) (groups*3)
      (fun index => (word (finProdFinEquiv.symm index).1 (finProdFinEquiv.symm index).2).val))
      (finProdFinEquiv (group, slot))).val = (word group slot).val
  rw [WeightCoordinates.tupleDecode_code]
  simp only [Equiv.symm_apply_apply]

section NativeEncoding
variable {Group : Type*} [Fintype Group] [DecidableEq Group]

omit [Fintype Group] [DecidableEq Group] in
theorem sourceWord_indexEncode (security count : ℕ) (kind : Group → Kind) (order : Fin count ≃ Group)
    (source : Source (colors security) (safe security) kind) :
    sourceWord security count (indexEncode (colors security) (colors_pos security) (safe security) kind count order source) =
      fun index slot => (GroupSourcePadding.encode (colors security) (colors_pos security) (safe security)
        (kind (order index)) (source (order index)) slot).val := by
  exact sourceWord_tuple security count (fun index =>
    GroupSourcePadding.encode (colors security) (colors_pos security) (safe security) (kind (order index)) (source (order index)))

end NativeEncoding

noncomputable section
open scoped Classical
local instance packedSourceFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance packedSourceSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize

def sourceIndex {security r s : ℕ} (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (source : PairedRootInput.GroupInput selection tagged) : Fin ((colors security)^((groupCount selection tagged)*3)) :=
  indexEncode (colors security) (colors_pos security) (safe security) (groupKind selection tagged)
    (groupCount selection tagged) (ordering selection tagged) ((sourceEquiv selection tagged).symm source)

theorem sourceWord_sourceIndex {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (source : PairedRootInput.GroupInput selection tagged) :
    sourceWord security (groupCount selection tagged) (sourceIndex selection tagged source) =
      fun index => RationalRootGroupProgram.sourceNatural selection tagged (ordering selection tagged index)
        (source (ordering selection tagged index)) := by
  rw [sourceIndex, sourceWord_indexEncode]
  funext index
  have h := CurrentRootSourceNatural.sourceNatural_encode selection tagged (ordering selection tagged index)
    (((sourceEquiv selection tagged).symm source) (ordering selection tagged index))
  have hs := congrFun ((sourceEquiv selection tagged).apply_symm_apply source) (ordering selection tagged index)
  change groupEquiv selection tagged (ordering selection tagged index)
    (((sourceEquiv selection tagged).symm source) (ordering selection tagged index)) = _ at hs
  rw [hs] at h
  exact h.symm

theorem valid_sourceIndex {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (source : PairedRootInput.GroupInput selection tagged) :
    Valid security (actualMetadata selection tagged)
      (sourceWord security (groupCount selection tagged) (sourceIndex selection tagged source)) := by
  rw [sourceIndex, sourceWord_indexEncode]
  intro index
  rw [validGroup_native]
  simp only [actualMetadata, nativeKind_role]
  exact encode_valid (colors security) (colors_pos security) (safe security) _ _

theorem decodedWord_val {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security))
    (index : Fin ((colors security)^((groupCount selection tagged)*3)))
    (group : ActiveGroup selection tagged) (slot : Fin 3) :
    (((indexEquiv (colors security) (colors_pos security) (groupCount selection tagged)
      (ordering selection tagged)).symm index) group slot).val =
      sourceWord security (groupCount selection tagged) index ((ordering selection tagged).symm group) slot := rfl

theorem valid_native_iff {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (index : Fin ((colors security)^((groupCount selection tagged)*3))) :
    Valid security (actualMetadata selection tagged) (sourceWord security (groupCount selection tagged) index) ↔
      ∀ group, GroupSourcePadding.Valid (colors security) (safe security) (groupKind selection tagged group)
        (((indexEquiv (colors security) (colors_pos security) (groupCount selection tagged)
          (ordering selection tagged)).symm index) group) := by
  constructor
  · intro h group
    have hg := h ((ordering selection tagged).symm group)
    have hw : (fun slot => (((indexEquiv (colors security) (colors_pos security) (groupCount selection tagged)
        (ordering selection tagged)).symm index) group slot).val) =
        sourceWord security (groupCount selection tagged) index ((ordering selection tagged).symm group) := by
      funext slot
      exact decodedWord_val selection tagged index group slot
    rw [← hw, validGroup_native] at hg
    simpa only [actualMetadata, nativeKind_role, Equiv.apply_symm_apply] using hg
  · intro h groupIndex
    have hg := h (ordering selection tagged groupIndex)
    have hw : (fun slot => (((indexEquiv (colors security) (colors_pos security) (groupCount selection tagged)
        (ordering selection tagged)).symm index) (ordering selection tagged groupIndex) slot).val) =
        sourceWord security (groupCount selection tagged) index groupIndex := by
      funext slot
      rw [decodedWord_val, Equiv.symm_apply_apply]
    rw [← hw, validGroup_native]
    simpa only [actualMetadata, nativeKind_role] using hg

theorem decode_none_iff {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (index : Fin ((colors security)^((groupCount selection tagged)*3))) :
    CurrentGroupSourcePadding.decode selection tagged (keptOrdering selection tagged) index = none ↔
      ¬Valid security (actualMetadata selection tagged) (sourceWord security (groupCount selection tagged) index) := by
  rw [valid_native_iff]
  change (sourceDecode (colors security) (safe security) (groupKind selection tagged)
    ((indexEquiv (colors security) (colors_pos security) (groupCount selection tagged)
      (ordering selection tagged)).symm index)).map (sourceEquiv selection tagged) = none ↔ _
  by_cases h : ∀ group, GroupSourcePadding.Valid (colors security) (safe security) (groupKind selection tagged group)
      (((indexEquiv (colors security) (colors_pos security) (groupCount selection tagged)
        (ordering selection tagged)).symm index) group)
  · rw [GroupSourcePadding.sourceDecode, dif_pos h]
    constructor
    · intro hnone; cases hnone
    · intro hnot; exact False.elim (hnot h)
  · rw [GroupSourcePadding.sourceDecode, dif_neg h]
    exact ⟨fun _ => h, fun _ => rfl⟩

theorem decode_eq_some {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (index : Fin ((colors security)^((groupCount selection tagged)*3)))
    (source : PairedRootInput.GroupInput selection tagged) :
    CurrentGroupSourcePadding.decode selection tagged (keptOrdering selection tagged) index = some source ↔
      index = sourceIndex selection tagged source := by
  unfold CurrentGroupSourcePadding.decode
  constructor
  · intro h
    obtain ⟨native, hn, hs⟩ := Option.map_eq_some_iff.mp h
    have heq : native = (sourceEquiv selection tagged).symm source := (sourceEquiv selection tagged).apply_eq_iff_eq_symm_apply.mp hs
    subst native
    exact (GroupSourcePadding.indexDecode_eq_some (colors security) (colors_pos security) (safe security)
      (groupKind selection tagged) (groupCount selection tagged) (ordering selection tagged) index _).mp hn
  · intro h
    subst index
    have hn := (GroupSourcePadding.indexDecode_eq_some (colors security) (colors_pos security) (safe security)
      (groupKind selection tagged) (groupCount selection tagged) (ordering selection tagged)
      (sourceIndex selection tagged source) ((sourceEquiv selection tagged).symm source)).mpr rfl
    change (indexDecode (colors security) (colors_pos security) (safe security) (groupKind selection tagged)
      (groupCount selection tagged) (ordering selection tagged) (sourceIndex selection tagged source)).map
      (sourceEquiv selection tagged) = some source
    rw [hn]
    exact congrArg some ((sourceEquiv selection tagged).apply_symm_apply source)

end
end CurrentAFT.RationalPackedRootProgram
