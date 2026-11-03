import AFT.PendingHigherStateIndices

/-! # The executable higher branch is the literal independent response branch -/
namespace AFT.RationalNumerics
open RepresentedPolynomial V7Calibration GaussianSource
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
local instance pendingHigherSemanticsFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

theorem pendingProgramHigher_denote {Leaf : Type*} {bound : ℕ} (numbering : FixedOrderNumberingCode bound)
    (hnumbering : ∀ order point mask slot,numbering.primaryLookup order point mask slot=pendingNumberingMeaning order point mask slot)
    (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (decode : Leaf → InputSeed (Fin (Parameters.modulus n))) (leafShape : Leaf → KernelShape)
    (hshape : ∀ leaf,(decode leaf).primaryOrder=(leafShape leaf).primary ∧ (decode leaf).bodyOrder=(leafShape leaf).body)
    (state : PendingProgramState Leaf) (hs : state.Valid bound leafShape) (mask : Fin 16) :
    (pendingProgramHigher numbering leafShape state mask).denote C n beta operator charts decode=
      pendingNonlinearState C n beta operator charts (state.denote C n beta operator charts decode) (pendingMask mask) := by
  by_cases hn : state.pending.Nonempty
  · have hf := (state.denote_nonempty C n beta operator charts decode leafShape hshape hs).mpr hn
    have horder := (state.kernel.denote_shape C n beta operator charts decode leafShape hshape).1
    have hlt := hs.2.1 _ (Finset.min'_mem state.pending hn)
    have hlt' : state.pending.min' hn<(state.kernel.denote C n beta operator charts decode).primaryOrder := by
      rwa [horder]
    have hb : (state.kernel.shape leafShape).primary≤bound ∧ state.pending.min' hn<(state.kernel.shape leafShape).primary :=
      ⟨hs.1.shape_bound.1,hlt⟩
    have hmin := state.denote_min C n beta operator charts decode leafShape hshape hs hn hf
    have hpmin : (⟨state.pending.min' hn,hlt'⟩ : Fin (state.kernel.denote C n beta operator charts decode).primaryOrder)=
        (state.denote C n beta operator charts decode).pending.min' hf := Fin.ext hmin.symm
    apply pendingInput_ext_natural
    · simp only [pendingProgramHigher,dif_pos hn]
      rw [dif_pos hb]
      change (PendingKernelCode.higher state.kernel (state.pending.min' hn) mask).denote C n beta operator charts decode=_
      simp only [PendingKernelCode.denote,dif_pos hlt',pendingNonlinearState,dif_pos hf,pendingHigherState]
      rw [hpmin]
      rfl
    · rw [(pendingProgramHigher numbering leafShape state mask).denote_natural C n beta operator charts decode leafShape hshape
        (pendingProgramHigher_valid numbering hnumbering hs mask)]
      rw [pendingNonlinearState,dif_pos hf]
      rw [pendingHigherState_natural numbering hnumbering C n beta operator charts (state.denote C n beta operator charts decode)
        (by change (state.kernel.denote C n beta operator charts decode).primaryOrder≤bound;rw [horder];exact hs.1.shape_bound.1)]
      simp only [state.denote_natural C n beta operator charts decode leafShape hshape hs,hmin]
      simp only [pendingProgramHigher,dif_pos hn]
      rw [dif_pos hb]
      dsimp only
      apply congrArg (fun f : ℕ → ℕ => (state.pending.erase (state.pending.min' hn)).image f)
      funext other
      change _=(if ho : other<(state.kernel.denote C n beta operator charts decode).primaryOrder then _ else _)
      simp only [horder]
      split_ifs
      · congr 1
        apply Fin.ext
        exact horder.symm
      · rfl
  · have hf := mt (state.denote_nonempty C n beta operator charts decode leafShape hshape hs).mp hn
    simp only [pendingProgramHigher,dif_neg hn,pendingNonlinearState,dif_neg hf]

end
end AFT.RationalNumerics
