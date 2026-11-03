import CurrentAFT.BinaryRootMetadataActual

/-! Proof-only cardinal transport identifies the produced finite metadata
with the paper's actual arrays, before any polynomial physical image. -/
namespace CurrentAFT.BinaryRootMetadataSerializer
open AFT BinaryArithmetic ActualBlockFock TaggedSelection PairedRootPlacement CurrentRootOrdering
open RationalRootGroupProgram
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize


def castMetadata {r s kept kept' tags : ℕ} (h : kept=kept') (data : RationalPackedRootProgram.Metadata r s kept tags) :
    RationalPackedRootProgram.Metadata r s kept' tags where
  roles index := data.roles ((finCongr (congrArg (fun count => (r+s)+count) h)).symm index)
  taggedSlots tag := ((finCongr (congrArg (fun count => (r+s)+count) h)) (data.taggedSlots tag).1,(data.taggedSlots tag).2)

 theorem current_castMetadata {r s kept kept' tags : ℕ} (security bits order : ℕ) (queue : ℤ)
    (h : kept=kept') (data : RationalPackedRootProgram.Metadata r s kept tags)
    (sourcePrimary : Fin r → ℕ) (sourceBody : Fin s → ℕ) :
    RationalPackedRootProgram.current security bits order queue data sourcePrimary sourceBody=
      RationalPackedRootProgram.current security bits order queue (castMetadata h data) sourcePrimary sourceBody := by
  subst kept'
  rfl

 theorem current_metadata_actual {security r s : ℕ} (choice : UniformTaggedOutput.Choice security r s)
    (tagged : Finset (BlockIndex security)) :
    castMetadata (retainedInput_length choice tagged)
      (current (primaryInput choice) (ordinaryInput choice) (tagsInput tagged)).data.metadata =
      RationalPackedRootProgram.actualMetadata (RationalFullResponseProgram.selection security r s choice) tagged := by
  apply congrArg₂ RationalPackedRootProgram.Metadata.mk
  · funext group
    change (current (primaryInput choice) (ordinaryInput choice) (tagsInput tagged)).data.roles.get
      ((groupCast choice tagged).symm group)=_
    rw [current_role_actual]
    change RationalPackedRootProgram.nativeRole _ _
      ((RationalPackedRootProgram.ordering _ _) ((groupCast choice tagged) ((groupCast choice tagged).symm group)))=_
    rw [Equiv.apply_symm_apply]
  · funext tag
    change ((groupCast choice tagged) ((current (primaryInput choice) (ordinaryInput choice) (tagsInput tagged)).data.tagged.get tag).1,
      ((current (primaryInput choice) (ordinaryInput choice) (tagsInput tagged)).data.tagged.get tag).2)=_
    simp only [current_tagSlot_actual]
    change ((groupCast choice tagged) (CurrentRootSlotIndex.tagPosition _ _ (inputOrdering choice tagged) (CurrentRootOrdering.tagOrdering tagged tag)).1,
      (CurrentRootSlotIndex.tagPosition _ _ (inputOrdering choice tagged) (CurrentRootOrdering.tagOrdering tagged tag)).2)=
        CurrentRootSlotIndex.tagPosition _ _ (RationalPackedRootProgram.ordering _ _) (CurrentRootOrdering.tagOrdering tagged tag)
    simp only [CurrentRootSlotIndex.tagPosition_eq]
    apply Prod.ext
    · change (groupCast choice tagged) ((inputOrdering choice tagged).symm _)=_
      simp only [inputOrdering,Equiv.symm_trans_apply,Equiv.apply_symm_apply]
    · rfl

 theorem current_rational_actual {security r s : ℕ} (bits order : ℕ) (queue : ℤ)
    (choice : UniformTaggedOutput.Choice security r s) (tagged : Finset (BlockIndex security))
    (sourcePrimary : Fin r → ℕ) (sourceBody : Fin s → ℕ) :
    RationalPackedRootProgram.current security bits order queue
      (current (primaryInput choice) (ordinaryInput choice) (tagsInput tagged)).data.metadata sourcePrimary sourceBody =
      RationalPackedRootProgram.current security bits order queue
        (RationalPackedRootProgram.actualMetadata (RationalFullResponseProgram.selection security r s choice) tagged) sourcePrimary sourceBody := by
  rw [current_castMetadata security bits order queue (retainedInput_length choice tagged),current_metadata_actual]

end CurrentAFT.BinaryRootMetadataSerializer
