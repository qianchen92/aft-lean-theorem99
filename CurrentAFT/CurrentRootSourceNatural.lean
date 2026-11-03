import CurrentAFT.CurrentRootOrdering
import CurrentAFT.RationalRootGroupProgram

/-! The local evaluator reads exactly the three slots of the native
source enumeration, including the single control of a paired root. -/
namespace CurrentAFT.CurrentRootSourceNatural
open AFT ActualBlockFock TaggedSelection PairedRootPlacement
  CurrentGroupSourcePadding GroupSourcePadding CurrentRectangleIndex
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem root_val (security : ℕ) (color : Fin (colors security)) :
    (rootEquiv security color).val = color.val := by
  have h (q : ℕ) [NeZero q] (point : Fin q) : ((ZMod.finEquiv q) point).val = point.val := by
    cases q with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ q => rfl
  exact h (Parameters.modulus security) (paletteEquiv security color)

theorem sourceNatural_encode {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (group : ActiveGroup selection tagged)
    (input : Input (colors security) (safe security) (groupKind selection tagged group)) :
    RationalRootGroupProgram.sourceNatural selection tagged group (groupEquiv selection tagged group input) =
      fun slot => (encode (colors security) (colors_pos security) (safe security)
        (groupKind selection tagged group) input slot).val := by
  rcases group with (primary | ordinary) | kept
  · dsimp only [groupKind, GroupSourcePadding.Input] at input
    rcases input with ⟨roots, control⟩
    funext slot
    fin_cases slot
    · change (rootEquiv security (roots 0)).val = (roots 0).val
      exact root_val security _
    · change (rootEquiv security (roots 1)).val = (roots 1).val
      exact root_val security _
    · rfl
  · dsimp only [groupKind, GroupSourcePadding.Input] at input
    rcases input with ⟨roots, control⟩
    funext slot
    fin_cases slot
    · change (rootEquiv security (roots 0)).val = (roots 0).val
      exact root_val security _
    · rfl
    · rfl
  · dsimp only [groupKind, GroupSourcePadding.Input] at input
    rcases input with ⟨roots, control⟩
    funext slot
    fin_cases slot
    · change (rootEquiv security (roots 0)).val = (roots 0).val
      exact root_val security _
    · rfl
    · rfl

end CurrentAFT.CurrentRootSourceNatural
