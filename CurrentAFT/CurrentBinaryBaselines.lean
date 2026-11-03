import CurrentAFT.CurrentBinaryLoadColumns
import CurrentAFT.CurrentBinaryChartData

/-! Stored body baselines in the executed attachment, center, queue ordering. -/
namespace CurrentAFT.CurrentBinaryBaselines
open AFT BinaryArithmetic RationalRejectionProgram CurrentCoreProposal CurrentEmissionMetadata
open CurrentBinaryLoadColumns
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current

 theorem controls_count (security : ℕ) : (CurrentProposalDimensions.current security).controls = (current security).centers := by
  rw [(CurrentProposalDimensions.current_values security).2.2.2.2.2, (current_values security).2.2.2]
  exact UniformTaggedOutput.centerCount_split security


def read (security : ℕ) (core : MaterializedCore security) :
    (Fin (Legs security) ⊕ Fin (current security).rest) → CountedValue IntegerBits
  | .inl leg =>
    let selected := readVector (defaultLeg security) core.legs leg
    let encoded := CurrentPublicShiftProgram.encode selected.value.2.val
    ⟨encoded.value, selected.work + encoded.work + 2⟩
  | .inr body =>
    let selected := lessCounter body.val (current security).centers
    if h : selected.value = true then
      let index : Fin (CurrentProposalDimensions.current security).controls := ⟨body.val, by
        rw [controls_count]; exact (lessCounter_value _ _).mp h⟩
      let selectedControl := readVector (defaultControl security) core.controls index
      let encoded := CurrentPublicShiftProgram.encode selectedControl.value.2.val.val
      ⟨encoded.value, selected.work + selectedControl.work + encoded.work + 3⟩
    else
      let address := subtractCounter body.val (current security).centers
      let index : Fin (CurrentProposalDimensions.current security).colors := ⟨address.count, by
        rw [subtractCounter_value]
        have hi : ¬body.val < (current security).centers := fun hi => h ((lessCounter_value _ _).mpr hi)
        have hc := (current_counts security).2.2.2.2.1
        have hb := body.isLt
        omega⟩
      let selectedBaseline := readVector (defaultControl security).1 core.baselines index
      let encoded := CurrentPublicShiftProgram.encode selectedBaseline.value.val
      ⟨encoded.value, selected.work + address.work + selectedBaseline.work + encoded.work + 4⟩


def role (security : ℕ) : Fin (Legs security) ⊕ Fin (current security).rest → ConditionalHistogramMean.RoleIndex security
  | .inl leg => .inr (.inr (legEquiv security leg))
  | .inr body => match finSumFinEquiv.symm (restEquiv security body) with
    | .inl center => .inl center
    | .inr queue => .inr (.inl queue)

 theorem center_address (security : ℕ) (body : Fin (current security).rest) (center : Fin (ActualBlockFock.centerCount security))
    (he : finSumFinEquiv (.inl center) = restEquiv security body)
    (index : Fin (CurrentProposalDimensions.current security).controls) (hi : index.val = body.val) :
    CurrentProposalDimensions.controlsEquiv security index = (UniformTaggedOutput.centerSplit security).symm center := by
  apply (UniformTaggedOutput.centerSplit security).injective
  apply Fin.ext
  have hv := congrArg Fin.val he
  change center.val = body.val at hv
  have hc : (UniformTaggedOutput.centerSplit security (CurrentProposalDimensions.controlsEquiv security index)).val = index.val := by
    simp only [UniformTaggedOutput.centerSplit, CurrentProposalDimensions.controlsEquiv, Equiv.trans_apply,
      finCongr_apply, Equiv.apply_symm_apply, Fin.val_cast]
  simpa only [Equiv.apply_symm_apply, hc, hi] using hv.symm

 theorem read_value (security : ℕ) (core : MaterializedCore security)
    (layout : ConditionalHistogramMean.RoleIndex security ≃ ActualCycleMeanMGF.BodyIndex security)
    (point : Fin (Legs security) ⊕ Fin (current security).rest) :
    (read security core point).value.decode = ActualPublicCharge.centerAt security layout core.core (layout (role security point)) := by
  rcases point with leg | body
  · simp only [read, CurrentPublicShiftProgram.encode_value, readVector_value, role,
      ActualPublicCharge.centerAt, Equiv.symm_apply_apply, MaterializedCore.core, decode, CurrentEmissionMetadata.legEquiv]
  · obtain ⟨center | queue, he⟩ := finSumFinEquiv.surjective (restEquiv security body)
    · have hv := congrArg Fin.val he
      change center.val = body.val at hv
      have hb : body.val < (current security).centers := by
        rw [(current_values security).2.2.2, ← hv]
        exact center.isLt
      have hs := (lessCounter_value _ _).mpr hb
      simp only [read, dif_pos hs, CurrentPublicShiftProgram.encode_value, readVector_value,
        role, ← he, Equiv.symm_apply_apply, ActualPublicCharge.centerAt]
      have ha := center_address security body center he ⟨body.val, by rw [controls_count]; exact hb⟩ rfl
      simp only [MaterializedCore.core, decode]
      rw [← ha, Equiv.symm_apply_apply]
    · have hv := congrArg Fin.val he
      change ActualBlockFock.centerCount security + queue.val = body.val at hv
      have hb : ¬body.val < (current security).centers := by
        rw [(current_values security).2.2.2]; omega
      have hs : ¬(lessCounter body.val (current security).centers).value = true := fun hs => hb ((lessCounter_value _ _).mp hs)
      simp only [read, dif_neg hs, CurrentPublicShiftProgram.encode_value, readVector_value,
        role, ← he, Equiv.symm_apply_apply, ActualPublicCharge.centerAt, MaterializedCore.core, decode]
      have ha : (subtractCounter body.val (current security).centers).count =
          ((CurrentProposalDimensions.queueEquiv security).symm queue).val := by
        change (subtractCounter body.val (current security).centers).count = queue.val
        rw [subtractCounter_value, (current_values security).2.2.2]
        omega
      have hi (h : (subtractCounter body.val (current security).centers).count < (CurrentProposalDimensions.current security).colors) :
          (⟨(subtractCounter body.val (current security).centers).count, h⟩ : Fin (CurrentProposalDimensions.current security).colors) =
            (CurrentProposalDimensions.queueEquiv security).symm queue := Fin.ext ha
      rw [hi]

end CurrentAFT.CurrentBinaryBaselines
