import CurrentAFT.BinaryRootMetadataMeaning

/-! The executed role and tagged-slot arrays agree with the actual sorted
active-group numbering. All cardinal transports are proof-only. -/
namespace CurrentAFT.BinaryRootMetadataSerializer
open AFT BinaryArithmetic ActualBlockFock TaggedSelection PairedRootPlacement CurrentRootOrdering
open scoped BigOperators
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize


def groupCast {security r s : ℕ} (choice : UniformTaggedOutput.Choice security r s)
    (tagged : Finset (BlockIndex security)) :
    Fin (groupCount (primaryInput choice) (ordinaryInput choice) (tagsInput tagged)) ≃
    Fin (RationalPackedRootProgram.groupCount (RationalFullResponseProgram.selection security r s choice) tagged) :=
  finCongr (congrArg (fun count => (r+s)+count) (retainedInput_length choice tagged))


def inputOrdering {security r s : ℕ} (choice : UniformTaggedOutput.Choice security r s)
    (tagged : Finset (BlockIndex security)) :
    Fin (groupCount (primaryInput choice) (ordinaryInput choice) (tagsInput tagged)) ≃
      ActiveGroup (RationalFullResponseProgram.selection security r s choice) tagged :=
  (groupCast choice tagged).trans (RationalPackedRootProgram.ordering (RationalFullResponseProgram.selection security r s choice) tagged)

 theorem inputOrdering_symm_primary {security r s : ℕ} (choice : UniformTaggedOutput.Choice security r s)
    (tagged : Finset (BlockIndex security)) (index : Fin r) :
    ((inputOrdering choice tagged).symm (.inl (.inl index))).val=index.val := rfl

 theorem inputOrdering_symm_ordinary {security r s : ℕ} (choice : UniformTaggedOutput.Choice security r s)
    (tagged : Finset (BlockIndex security)) (index : Fin s) :
    ((inputOrdering choice tagged).symm (.inl (.inr index))).val=r+index.val := rfl

 theorem inputOrdering_symm_kept {security r s : ℕ} (choice : UniformTaggedOutput.Choice security r s)
    (tagged : Finset (BlockIndex security))
    (index : HitKept (RationalFullResponseProgram.selection security r s choice) tagged) :
    ((inputOrdering choice tagged).symm (.inr index)).val=(r+s)+
      ((CurrentRootOrdering.keptOrdering (RationalFullResponseProgram.selection security r s choice) tagged).symm index).val := rfl

 theorem retainedInput_at_group {security r s : ℕ} (choice : UniformTaggedOutput.Choice security r s)
    (tagged : Finset (BlockIndex security))
    (index : HitKept (RationalFullResponseProgram.selection security r s choice) tagged) :
    (retainedInput choice tagged).get
      ⟨((inputOrdering choice tagged).symm (.inr index)).val-(r+s),by
        rw [inputOrdering_symm_kept]
        have h := ((CurrentRootOrdering.keptOrdering (RationalFullResponseProgram.selection security r s choice) tagged).symm index).isLt
        have hlen := retainedInput_length choice tagged
        omega⟩ = numbering security index.val.val := by
  rw [retainedInput_get]
  have hi : finCongr (retainedInput_length choice tagged)
      (⟨((inputOrdering choice tagged).symm (.inr index)).val-(r+s),by
        rw [inputOrdering_symm_kept]
        have h := ((CurrentRootOrdering.keptOrdering (RationalFullResponseProgram.selection security r s choice) tagged).symm index).isLt
        have hlen := retainedInput_length choice tagged
        omega⟩ : Fin (retainedInput choice tagged).length)=
      (CurrentRootOrdering.keptOrdering (RationalFullResponseProgram.selection security r s choice) tagged).symm index := by
    apply Fin.ext
    simp only [finCongr_apply,Fin.val_cast,inputOrdering_symm_kept]
    omega
  rw [hi,Equiv.apply_symm_apply]

 theorem candidate_input {security r s : ℕ} (choice : UniformTaggedOutput.Choice security r s)
    (tagged : Finset (BlockIndex security))
    (group : ActiveGroup (RationalFullResponseProgram.selection security r s choice) tagged) (slot : Fin 2) :
    (candidate (primaryInput choice) (ordinaryInput choice) (retainedInput choice tagged)
      ((inputOrdering choice tagged).symm group) slot).value =
      (CurrentRootSlotIndex.within (RationalFullResponseProgram.selection security r s choice) tagged group slot).map
        (fun root => (numbering security (CurrentRootSlotIndex.rootBlock (RationalFullResponseProgram.selection security r s choice) tagged root)).val) := by
  rcases group with (primary | ordinary) | retained
  · have hg : ((inputOrdering choice tagged).symm (.inl (.inl primary))).val<r := by
      rw [inputOrdering_symm_primary]
      exact primary.isLt
    rw [candidate_primary (primaryInput choice) (ordinaryInput choice) (retainedInput choice tagged)
      ((inputOrdering choice tagged).symm (.inl (.inl primary))) slot hg]
    simp only [primaryInput,Vector.get_ofFn,CurrentRootSlotIndex.within,Option.map_some,CurrentRootSlotIndex.rootBlock]
    split_ifs
    · simp only [numbering_compensator]
      apply congrArg (fun index : Fin r => some (Parameters.legCount security+(choice.1 index).val))
      apply Fin.ext
      change ((inputOrdering choice tagged).symm (.inl (.inl primary))).val=primary.val
      exact inputOrdering_symm_primary choice tagged primary
    · simp only [numbering_primary]
      apply congrArg (fun index : Fin r => some (choice.1 index).val)
      apply Fin.ext
      change ((inputOrdering choice tagged).symm (.inl (.inl primary))).val=primary.val
      exact inputOrdering_symm_primary choice tagged primary
  · have hp : ¬((inputOrdering choice tagged).symm (.inl (.inr ordinary))).val<r := by
      rw [inputOrdering_symm_ordinary]
      omega
    have hg : ((inputOrdering choice tagged).symm (.inl (.inr ordinary))).val<r+s := by
      rw [inputOrdering_symm_ordinary]
      have := ordinary.isLt
      omega
    rw [candidate_ordinary (primaryInput choice) (ordinaryInput choice) (retainedInput choice tagged)
      ((inputOrdering choice tagged).symm (.inl (.inr ordinary))) slot hp hg]
    simp only [ordinaryInput,Vector.get_ofFn,CurrentRootSlotIndex.within]
    split_ifs
    · simp only [Option.map_some,CurrentRootSlotIndex.rootBlock,numbering_ordinary]
      apply congrArg (fun index : Fin s => some (Parameters.legCount security+Parameters.legCount security+(choice.2 index).val))
      apply Fin.ext
      change ((inputOrdering choice tagged).symm (.inl (.inr ordinary))).val-r=ordinary.val
      have hval := inputOrdering_symm_ordinary choice tagged ordinary
      omega
    · rfl
  · have hg : ¬((inputOrdering choice tagged).symm (.inr retained)).val<r+s := by
      rw [inputOrdering_symm_kept]
      omega
    rw [candidate_kept (primaryInput choice) (ordinaryInput choice) (retainedInput choice tagged)
      ((inputOrdering choice tagged).symm (.inr retained)) slot hg]
    rw [retainedInput_at_group]
    simp only [CurrentRootSlotIndex.within]
    split_ifs <;> simp only [Option.map_some,Option.map_none,CurrentRootSlotIndex.rootBlock]


def keptRole {security : ℕ} : BlockIndex security → RationalRootGroupProgram.LocalRole
  | .inl _ => .leg
  | .inr (.inl _) => .center
  | .inr (.inr _) => .queue

 theorem classify_numbering (security : ℕ) (block : BlockIndex security) :
    (if (numbering security block).val<Parameters.legCount security then RationalRootGroupProgram.LocalRole.leg else
      if (numbering security block).val<Parameters.legCount security+(Parameters.legCount security+BackgroundRates.ordinaryPool security) then .center else .queue)=keptRole block := by
  have hs := UniformTaggedOutput.centerCount_split security
  rcases block with leg | (center | queue)
  · rw [numbering_primary]
    exact if_pos leg.isLt
  · have hv : (numbering security (.inr (.inl center))).val=Parameters.legCount security+center.val := rfl
    rw [hv,if_neg (by omega),if_pos (by have := center.isLt;omega)]
    rfl
  · have hv : (numbering security (.inr (.inr queue))).val=Parameters.legCount security+centerCount security+queue.val := by
      change Parameters.legCount security+(centerCount security+queue.val)=_
      omega
    rw [hv,if_neg (by omega),if_neg (by omega)]
    rfl

 theorem role_input {security r s : ℕ} (choice : UniformTaggedOutput.Choice security r s)
    (tagged : Finset (BlockIndex security)) (group : ActiveGroup (RationalFullResponseProgram.selection security r s choice) tagged) :
    (role (primaryInput choice) (ordinaryInput choice) (retainedInput choice tagged) ((inputOrdering choice tagged).symm group)).value=
      RationalPackedRootProgram.nativeRole (RationalFullResponseProgram.selection security r s choice) tagged group := by
  rcases group with (primary | ordinary) | retained
  · apply role_primary
    rw [inputOrdering_symm_primary]
    exact primary.isLt
  · apply role_ordinary
    · rw [inputOrdering_symm_ordinary]
      omega
    · rw [inputOrdering_symm_ordinary]
      have := ordinary.isLt
      omega
  · rw [role_kept (primaryInput choice) (ordinaryInput choice) (retainedInput choice tagged)
      ((inputOrdering choice tagged).symm (.inr retained)) (by rw [inputOrdering_symm_kept];omega),retainedInput_at_group]
    exact classify_numbering security retained.val.val

 theorem current_role_actual {security r s : ℕ} (choice : UniformTaggedOutput.Choice security r s)
    (tagged : Finset (BlockIndex security))
    (group : Fin (groupCount (primaryInput choice) (ordinaryInput choice) (tagsInput tagged))) :
    (current (primaryInput choice) (ordinaryInput choice) (tagsInput tagged)).data.roles.get group=
      RationalPackedRootProgram.nativeRole (RationalFullResponseProgram.selection security r s choice) tagged (inputOrdering choice tagged group) := by
  rw [current_role]
  simpa only [Equiv.symm_apply_apply] using role_input choice tagged (inputOrdering choice tagged group)

 theorem matchesBlock_input {security r s : ℕ} (choice : UniformTaggedOutput.Choice security r s)
    (tagged : Finset (BlockIndex security)) (block : BlockIndex security)
    (index : Fin ((groupCount (primaryInput choice) (ordinaryInput choice) (tagsInput tagged))*2)) :
    (matchesBlock (primaryInput choice) (ordinaryInput choice) (retainedInput choice tagged) (numbering security block) index).value=
      CurrentRootSlotIndex.test (RationalFullResponseProgram.selection security r s choice) tagged (inputOrdering choice tagged) block index := by
  rw [matchesBlock_value]
  have hc := candidate_input choice tagged ((inputOrdering choice tagged) (finProdFinEquiv.symm index).1) (finProdFinEquiv.symm index).2
  simp only [Equiv.symm_apply_apply] at hc
  have hmap := congrArg (fun value : Option ℕ => value.any (fun number => decide (number=(numbering security block).val))) hc
  apply hmap.trans
  unfold CurrentRootSlotIndex.test CurrentRootSlotIndex.decode
  cases hr : CurrentRootSlotIndex.within (RationalFullResponseProgram.selection security r s choice) tagged
      ((inputOrdering choice tagged) (finProdFinEquiv.symm index).1) (finProdFinEquiv.symm index).2 with
  | none => rfl
  | some root =>
    simp only [Option.map_some,Option.any_some]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro he
      exact (numbering security).injective (Fin.ext he)
    · intro he
      rw [he]

 theorem position_input {security r s : ℕ} (choice : UniformTaggedOutput.Choice security r s)
    (tagged : Finset (BlockIndex security)) (block : BlockIndex security) :
    (position (primaryInput choice) (ordinaryInput choice) (retainedInput choice tagged) (numbering security block)).value=
      CurrentRootSlotIndex.position (RationalFullResponseProgram.selection security r s choice) tagged (inputOrdering choice tagged) block := by
  change (find _ _).value=_
  rw [find_value]
  unfold CurrentRootSlotIndex.position
  congr 1
  funext index
  exact matchesBlock_input choice tagged block index

 theorem tagSlot_input {security r s : ℕ} (choice : UniformTaggedOutput.Choice security r s)
    (tagged : Finset (BlockIndex security)) (index : Fin tagged.card) :
    (tagSlot (primaryInput choice) (ordinaryInput choice) (tagsInput tagged) index).value=
      CurrentRootSlotIndex.taggedSlots (RationalFullResponseProgram.selection security r s choice) tagged (inputOrdering choice tagged) index := by
  simp only [tagSlot,readVector_value,tagsInput_get]
  have hp := position_input choice tagged (CurrentRootOrdering.tagOrdering tagged index).val
  unfold retainedInput at hp
  rw [hp,CurrentRootSlotIndex.position_tag,splitIndex_value]
  simp only [Option.getD_some,CurrentRootSlotIndex.encode]
  have hinverse (pair : Fin (groupCount (primaryInput choice) (ordinaryInput choice) (tagsInput tagged)) × Fin 2) :
      finProdFinEquiv.symm (finProdFinEquiv pair)=pair := Equiv.symm_apply_apply finProdFinEquiv pair
  exact (hinverse ((inputOrdering choice tagged).symm
      (PairedRootPlacement.tagEmbedding (RationalFullResponseProgram.selection security r s choice) tagged (CurrentRootOrdering.tagOrdering tagged index)).fst,
    CurrentRootSlotIndex.slotNumber (RationalFullResponseProgram.selection security r s choice) tagged
      (PairedRootPlacement.tagEmbedding (RationalFullResponseProgram.selection security r s choice) tagged (CurrentRootOrdering.tagOrdering tagged index)))).trans
    (CurrentRootSlotIndex.tagPosition_eq (RationalFullResponseProgram.selection security r s choice) tagged
      (inputOrdering choice tagged) (CurrentRootOrdering.tagOrdering tagged index)).symm

 theorem current_tagSlot_actual {security r s : ℕ} (choice : UniformTaggedOutput.Choice security r s)
    (tagged : Finset (BlockIndex security)) (index : Fin tagged.card) :
    (current (primaryInput choice) (ordinaryInput choice) (tagsInput tagged)).data.tagged.get index=
      CurrentRootSlotIndex.taggedSlots (RationalFullResponseProgram.selection security r s choice) tagged (inputOrdering choice tagged) index := by
  rw [current_tagSlot]
  exact tagSlot_input choice tagged index

end CurrentAFT.BinaryRootMetadataSerializer
