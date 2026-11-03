import AFT.PendingProgramValidity

/-! # Exact decoding of executable pending states -/
namespace AFT.RationalNumerics
open RepresentedPolynomial V7Calibration GaussianSource
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
local instance pendingStateSemanticsFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

theorem pendingInput_ext_natural {Color : Type*} {first second : PendingInput Color}
    (hs : first.seed=second.seed)
    (hp : first.pending.image Fin.val=second.pending.image Fin.val) : first=second := by
  cases first with | mk seed pending =>
    cases second with | mk other rest =>
      dsimp only at hs
      subst other
      congr 1
      exact Finset.image_injective Fin.val_injective hp

variable {Leaf : Type*} {bound : ℕ} (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (decode : Leaf → InputSeed (Fin (Parameters.modulus n))) (leafShape : Leaf → KernelShape)
    (hshape : ∀ leaf,(decode leaf).primaryOrder=(leafShape leaf).primary ∧ (decode leaf).bodyOrder=(leafShape leaf).body)

include hshape in
 theorem PendingProgramState.denote_natural (state : PendingProgramState Leaf) (hs : state.Valid bound leafShape) :
    (state.denote C n beta operator charts decode).pending.image Fin.val=state.pending := by
  apply finitePending_image
  intro point hp
  change point<(state.kernel.denote C n beta operator charts decode).primaryOrder
  rw [state.kernel.denote_shape C n beta operator charts decode leafShape hshape |>.1]
  exact hs.2.1 point hp

include hshape in
 theorem PendingProgramState.denote_nonempty (state : PendingProgramState Leaf) (hs : state.Valid bound leafShape) :
    (state.denote C n beta operator charts decode).pending.Nonempty ↔ state.pending.Nonempty := by
  rw [←state.denote_natural C n beta operator charts decode leafShape hshape hs,Finset.image_nonempty]

include hshape in
 theorem PendingProgramState.denote_min (state : PendingProgramState Leaf) (hs : state.Valid bound leafShape)
    (hn : state.pending.Nonempty) (hf : (state.denote C n beta operator charts decode).pending.Nonempty) :
    ((state.denote C n beta operator charts decode).pending.min' hf).val=state.pending.min' hn := by
  apply finitePending_min
  intro point hp
  change point<(state.kernel.denote C n beta operator charts decode).primaryOrder
  rw [state.kernel.denote_shape C n beta operator charts decode leafShape hshape |>.1]
  exact hs.2.1 point hp

include hshape in
 theorem pendingProgramLinear_denote (state : PendingProgramState Leaf) (hs : state.Valid bound leafShape) :
    (pendingProgramLinear state).denote C n beta operator charts decode=
      pendingLinearState (state.denote C n beta operator charts decode) := by
  by_cases hn : state.pending.Nonempty
  · have hf := (state.denote_nonempty C n beta operator charts decode leafShape hshape hs).mpr hn
    apply pendingInput_ext_natural
    · rw [pendingLinearState_seed]
      simp only [pendingProgramLinear,dif_pos hn,PendingProgramState.denote]
    · rw [(pendingProgramLinear state).denote_natural C n beta operator charts decode leafShape hshape (pendingProgramLinear_valid hs)]
      rw [pendingLinearState,dif_pos hf]
      simp only [pendingProgramLinear,dif_pos hn,Finset.image_erase Fin.val_injective]
      rw [state.denote_natural C n beta operator charts decode leafShape hshape hs,
        state.denote_min C n beta operator charts decode leafShape hshape hs hn hf]
  · have hf := mt (state.denote_nonempty C n beta operator charts decode leafShape hshape hs).mp hn
    simp only [pendingProgramLinear,dif_neg hn,pendingLinearState,dif_neg hf]

include hshape in
 theorem pendingProgramChoices_denote (state : PendingProgramState Leaf) (hs : state.Valid bound leafShape) :
    ((pendingProgramChoices state).map pendingMask).Nodup ∧
    ((pendingProgramChoices state).map pendingMask).toFinset=pendingHigherChoices (state.denote C n beta operator charts decode) := by
  by_cases hn : state.pending.Nonempty
  · have hf := (state.denote_nonempty C n beta operator charts decode leafShape hshape hs).mpr hn
    simp only [pendingProgramChoices,if_pos hn,pendingHigherChoices]
    rw [if_pos hf]
    refine ⟨pendingHigherMasks_selected_nodup,?_⟩
    have hh := pendingHigherMasks_selected_set
    rw [show instDecidableEqFin 4=pendingStateSemanticsFinDecEq 4 from Subsingleton.elim _ _] at hh
    exact hh
  · have hf := mt (state.denote_nonempty C n beta operator charts decode leafShape hshape hs).mp hn
    simp only [pendingProgramChoices,if_neg hn,List.map_nil,List.nodup_nil,List.toFinset_nil,pendingHigherChoices,if_neg hf,and_self]

include hshape in
 theorem initialPendingProgramState_denote (code : PendingKernelCode Leaf) :
    (initialPendingProgramState leafShape code).denote C n beta operator charts decode=
      initialPendingInput (code.denote C n beta operator charts decode) := by
  have ho := (code.denote_shape C n beta operator charts decode leafShape hshape).1
  apply pendingInput_ext_natural
  · rfl
  change (finitePending (code.denote C n beta operator charts decode).primaryOrder (Finset.range (code.shape leafShape).primary)).image Fin.val=Finset.univ.image Fin.val
  rw [←ho,finitePending_range]
  rfl

end
end AFT.RationalNumerics
