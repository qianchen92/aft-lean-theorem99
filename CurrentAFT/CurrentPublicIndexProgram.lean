import CurrentAFT.CurrentProposalDimensions

/-! The public primary/ordinary role address is selected by an actual counter
comparison and, on the ordinary branch, a counter subtraction. -/
namespace CurrentAFT.CurrentPublicIndexProgram
open AFT AFT.BinaryArithmetic AFT.RationalRejectionProgram CurrentProposalDimensions
set_option maxHeartbeats 500000
attribute [local irreducible] CurrentProposalDimensions.current

def decode (security : ℕ) (index : Fin (current security).controls) :
    CountedValue (PublicOutputExperiment.PublicIndex security) :=
  let below := lessCounter index.val (current security).legs
  if h : below.value then
    have hi : index.val < Parameters.legCount security := by
      have hh := (lessCounter_value _ _).mp h
      rwa [(current_values security).2.1] at hh
    ⟨.inl ⟨index.val, hi⟩, below.work + 2⟩
  else
    let offset := subtractCounter index.val (current security).legs
    have hi : offset.count < BackgroundRates.ordinaryPool security := by
      have hh : ¬index.val < (current security).legs := by simpa only [← lessCounter_value] using h
      have hb : index.val < Parameters.legCount security + BackgroundRates.ordinaryPool security := by
        simpa only [(current_values security).2.2.2.2.2] using index.isLt
      rw [subtractCounter_value, (current_values security).2.1]
      rw [(current_values security).2.1] at hh
      omega
    ⟨.inr ⟨offset.count, hi⟩, below.work + offset.work + 3⟩

theorem decode_value (security : ℕ) (index : Fin (current security).controls) :
    (decode security index).value = controlsEquiv security index := by
  apply finSumFinEquiv.injective
  have he : finSumFinEquiv (controlsEquiv security index) =
      (finCongr (current_values security).2.2.2.2.2) index := by
    simp only [controlsEquiv, Equiv.trans_apply, Equiv.apply_symm_apply]
  rw [he]
  apply Fin.ext
  dsimp only [decode]
  split_ifs with h
  · rfl
  · have hh : ¬index.val < (current security).legs := by simpa only [← lessCounter_value] using h
    rw [(current_values security).2.1] at hh
    simp only [subtractCounter_value, (current_values security).2.1, finSumFinEquiv, Equiv.coe_fn_mk,
      Sum.elim_inr, Fin.natAdd_mk, Fin.val_mk, finCongr_apply, Fin.val_cast]
    change Parameters.legCount security + (index.val - Parameters.legCount security) = index.val
    omega

def workBound (security : ℕ) : ℕ := 5 * (current security).controls + 5

theorem decode_work (security : ℕ) (index : Fin (current security).controls) :
    (decode security index).work ≤ workBound security := by
  have hl := lessCounter_work_left index.val (current security).legs
  have hs := subtractCounter_work_left index.val (current security).legs
  have hi := index.isLt
  dsimp only [decode, workBound]
  split_ifs <;> dsimp only <;> omega

end CurrentAFT.CurrentPublicIndexProgram
