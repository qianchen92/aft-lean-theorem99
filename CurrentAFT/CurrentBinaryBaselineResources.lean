import CurrentAFT.CurrentBinaryBaselines

/-! Actual baseline-buffer reading and color encoding have bounded bit cost. -/
namespace CurrentAFT.CurrentBinaryBaselineResources
open AFT BinaryArithmetic RationalRejectionProgram CurrentCoreProposal CurrentEmissionMetadata CurrentBinaryLoadColumns
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current

theorem color_length (security : ℕ) (color : FirstHistogram.Palette security) :
    (CurrentPublicShiftProgram.encode color.val).value.digits.length ≤ Parameters.modulus security := by
  apply (CurrentPublicShiftProgram.encode_length _).trans
  rw [Int.natAbs_natCast]
  exact color.isLt.le

 theorem color_work (security : ℕ) (color : FirstHistogram.Palette security) :
    (CurrentPublicShiftProgram.encode color.val).work ≤ 50 * (Parameters.modulus security + 1)^2 + 1 := by
  apply (CurrentPublicShiftProgram.encode_work _).trans
  rw [Int.natAbs_natCast]
  gcongr
  exact color.isLt.le

 theorem read_length (security : ℕ) (core : MaterializedCore security)
    (point : Fin (Legs security) ⊕ Fin (current security).rest) :
    (CurrentBinaryBaselines.read security core point).value.digits.length ≤ Parameters.modulus security := by
  cases point with
  | inl leg => exact color_length security _
  | inr body =>
    dsimp only [CurrentBinaryBaselines.read]
    split_ifs <;> exact color_length security _


def readWork (security : ℕ) : ℕ :=
  20 * ((CurrentProposalDimensions.current security).legs + (CurrentProposalDimensions.current security).controls +
    (CurrentProposalDimensions.current security).colors + (current security).rest + 1) +
    50 * (Parameters.modulus security + 1)^2 + 20

 theorem read_work (security : ℕ) (core : MaterializedCore security)
    (point : Fin (Legs security) ⊕ Fin (current security).rest) :
    (CurrentBinaryBaselines.read security core point).work ≤ readWork security := by
  cases point with
  | inl leg =>
    have hr := readVector_work (defaultLeg security) core.legs leg
    have he := color_work security (readVector (defaultLeg security) core.legs leg).value.2
    change (readVector _ core.legs leg).work + (CurrentPublicShiftProgram.encode _).work + 2 ≤ _
    unfold readWork
    omega
  | inr body =>
    have htest := lessCounter_work_left body.val (current security).centers
    have hb := body.isLt
    dsimp only [CurrentBinaryBaselines.read]
    split_ifs with h
    · let index : Fin (CurrentProposalDimensions.current security).controls := ⟨body.val, by
        rw [CurrentBinaryBaselines.controls_count]; exact (lessCounter_value _ _).mp h⟩
      have hr := readVector_work (defaultControl security) core.controls index
      have he := color_work security (readVector (defaultControl security) core.controls index).value.2.val
      change (lessCounter body.val (current security).centers).work + (readVector _ core.controls index).work +
        (CurrentPublicShiftProgram.encode _).work + 3 ≤ _
      dsimp only [index] at hr he ⊢
      unfold readWork
      omega
    · let address := subtractCounter body.val (current security).centers
      have hi : address.count < (CurrentProposalDimensions.current security).colors := by
        rw [show address.count = body.val - (current security).centers from subtractCounter_value _ _]
        have hn : ¬body.val < (current security).centers := fun hh => h ((lessCounter_value _ _).mpr hh)
        have hc := (current_counts security).2.2.2.2.1
        omega
      let index : Fin (CurrentProposalDimensions.current security).colors := ⟨address.count, hi⟩
      have ha := subtractCounter_work_left body.val (current security).centers
      have hr := readVector_work (defaultControl security).1 core.baselines index
      have he := color_work security (readVector (defaultControl security).1 core.baselines index).value
      change (lessCounter body.val (current security).centers).work + address.work + (readVector _ core.baselines index).work +
        (CurrentPublicShiftProgram.encode _).work + 4 ≤ _
      dsimp only [index, address] at hr he ⊢
      unfold readWork
      omega

end CurrentAFT.CurrentBinaryBaselineResources
