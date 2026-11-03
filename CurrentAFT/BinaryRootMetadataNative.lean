import CurrentAFT.BinaryRootMetadataInput
import CurrentAFT.BinaryRootMetadataTransport

/-! The executed native metadata produces the literal actual response table. -/
namespace CurrentAFT.BinaryRootMetadataSerializer
open AFT
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize BinaryFullResponseCounts.current

theorem current_rational_native {security r s tagOrder : ℕ} (bits order : ℕ) (queue : ℤ)
    (primary : Vector (Fin (BinaryFullResponseCounts.current security).leg) r)
    (body : Vector (Fin (BinaryFullResponseCounts.current security).ordinary) s)
    (hp : Function.Injective primary.get) (hb : Function.Injective body.get)
    (tag : CountedBoundedRootTags.Tag (BinaryFullResponseCounts.current security).body tagOrder)
    (sourcePrimary : Fin r → ℕ) (sourceBody : Fin s → ℕ) :
    RationalPackedRootProgram.current security bits order queue
      (current primary body (nativeTag tag)).data.metadata sourcePrimary sourceBody=
    RationalPackedRootProgram.current security bits order queue
      (RationalPackedRootProgram.actualMetadata
        (RationalFullResponseProgram.selection security r s (actualChoice primary body hp hb)) (tagBlocks tag))
      sourcePrimary sourceBody := by
  rw [← current_native_counts primary body tag,actualChoice_primary primary body hp hb,
    actualChoice_ordinary primary body hp hb,nativeTag_tagsInput_vector,current_cast_tags,rational_current_cast_tags]
  exact current_rational_actual bits order queue (actualChoice primary body hp hb) (tagBlocks tag) sourcePrimary sourceBody

theorem tagBlockEquiv_number (security : ℕ) (block : Fin (BinaryFullResponseCounts.current security).body) :
    (CurrentRootOrdering.blockNumbering security (tagBlockEquiv security block)).val=block.val := by
  have hnumber (value : ActualBlockFock.BlockIndex security) :
      (numbering security value).val=(CurrentRootOrdering.blockNumbering security value).val := rfl
  rw [← hnumber]
  simp only [tagBlockEquiv,Equiv.trans_apply,Equiv.apply_symm_apply,countEquiv,finCongr_apply,Fin.val_cast]

end CurrentAFT.BinaryRootMetadataSerializer
