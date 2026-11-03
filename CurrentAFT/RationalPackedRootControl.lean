import CurrentAFT.RationalPackedRootSource

/-! # The weighted point column is evaluated on the actual joint controls -/
namespace CurrentAFT.RationalPackedRootProgram
open AFT TaggedSelection PairedRootPlacement CurrentGroupSourcePadding CurrentRootOrdering
  CurrentRectangleIndex RationalRootGroupProgram CycleRootExpansion ActualControls
open ActualBlockFock (BlockIndex)
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance packedControlFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance packedControlSafeDecidableEq (security : ℕ) : DecidableEq (SafePalette security) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount

theorem ordering_primary {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (index : Fin r) :
    ordering selection tagged (primaryGroup r s (keptIndices selection tagged).card index) = .inl (.inl index) := by
  apply (ordering selection tagged).apply_eq_iff_eq_symm_apply.mpr
  apply Fin.ext
  rfl

theorem ordering_ordinary {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (index : Fin s) :
    ordering selection tagged (ordinaryGroup r s (keptIndices selection tagged).card index) = .inl (.inr index) := by
  apply (ordering selection tagged).apply_eq_iff_eq_symm_apply.mpr
  apply Fin.ext
  rfl

theorem control_sourceIndex {security r s : ℕ} (bits : ℕ) (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (sourcePrimary : Fin r → Palette security) (sourceBody : Fin s → SafePalette security)
    (source : PairedRootInput.GroupInput selection tagged) :
    control security bits (actualMetadata selection tagged) (fun index => (sourcePrimary index).val)
      (fun index => (sourceBody index).val.val)
      (sourceWord security (groupCount selection tagged) (sourceIndex selection tagged source)) =
      WeightedPointKernelProgram.current security bits r s (fun index => (sourcePrimary index).val)
        (fun index => (sourceBody index).val.val)
        (fun index => (source (.inl (.inl index))).2.val) (fun index => (source (.inl (.inr index))).2.val.val) := by
  unfold control
  rw [sourceWord_sourceIndex]
  congr 1
  · funext index
    dsimp only
    rw [ordering_primary]
    rfl
  · funext index
    dsimp only
    rw [ordering_ordinary]
    rfl

theorem control_error {security r s : ℕ} (bits : ℕ) (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (sourcePrimary : Fin r → Palette security) (sourceBody : Fin s → SafePalette security)
    (source : PairedRootInput.GroupInput selection tagged)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) :
    |(control security bits (actualMetadata selection tagged) (fun index => (sourcePrimary index).val)
        (fun index => (sourceBody index).val.val)
        (sourceWord security (groupCount selection tagged) (sourceIndex selection tagged source)) : ℝ) -
      PairedRootInput.controlKernel selection tagged (WeightedPointKernelProgram.actualKernel security sourcePrimary sourceBody)
        (fun group => (source group).2)| ≤ WeightedPointKernelProgram.errorConstant security r s * (1 / (2 : ℝ)^bits) := by
  rw [control_sourceIndex]
  exact WeightedPointKernelProgram.current_error security bits r s sourcePrimary sourceBody hprecision hbudget _ _

theorem control_bound {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (sourcePrimary : Fin r → Palette security) (sourceBody : Fin s → SafePalette security)
    (source : PairedRootInput.GroupInput selection tagged) :
    |PairedRootInput.controlKernel selection tagged (WeightedPointKernelProgram.actualKernel security sourcePrimary sourceBody)
      (fun group => (source group).2)| ≤ 1 := by
  exact WeightedPointKernelProgram.actualKernel_bound security sourcePrimary sourceBody _ _

end
end CurrentAFT.RationalPackedRootProgram
