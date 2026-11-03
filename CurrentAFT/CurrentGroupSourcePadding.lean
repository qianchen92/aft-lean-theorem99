import CurrentAFT.GroupSourcePadding
import CurrentAFT.CurrentRectangleIndex
import CurrentAFT.RootWeightedSynthesis

/-! The native three-slot source enumeration equals the actual grouped
root source sum. This transports the whole joint summand, without
factoring either a paired control or the common queue. -/
namespace CurrentAFT.CurrentGroupSourcePadding
open AFT ActualBlockFock TaggedSelection PairedRootPlacement PairedRootInput
  GroupSourcePadding CurrentRectangleIndex
open scoped BigOperators
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def groupKind {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) : ActiveGroup selection tagged → Kind
  | .inl (.inl _) => .primary
  | .inl (.inr _) => .ordinary
  | .inr _ => .kept

def rootEquiv (security : ℕ) : Fin (colors security) ≃ CycleRootExpansion.Root security :=
  (paletteEquiv security).trans (ZMod.finEquiv (Parameters.modulus security)).toEquiv

def groupEquiv {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (group : ActiveGroup selection tagged) :
    Input (colors security) (safe security) (groupKind selection tagged group) ≃
      ((groupRootSlots selection tagged group → CycleRootExpansion.Root security) ×
        ControlInput selection tagged group) := by
  rcases group with (primary | ordinary) | kept
  · exact Equiv.prodCongr (Equiv.piCongrRight (fun _ => rootEquiv security)) (paletteEquiv security)
  · exact Equiv.prodCongr (Equiv.piCongrRight (fun _ => rootEquiv security)) (safeEquiv security)
  · exact Equiv.prodCongr (Equiv.piCongrRight (fun _ => rootEquiv security)) (Equiv.refl Unit)

def sourceEquiv {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) :
    Source (colors security) (safe security) (groupKind selection tagged) ≃ GroupInput selection tagged :=
  Equiv.piCongrRight (groupEquiv selection tagged)

def groupOrdering {security r s k : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (keptOrdering : Fin k ≃ HitKept selection tagged) :
    Fin ((r+s)+k) ≃ ActiveGroup selection tagged :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr finSumFinEquiv.symm keptOrdering)

noncomputable section
open scoped Classical
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
local instance classicalSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} : DecidableEq (Sigma Slots) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount

def decode {security r s k : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (keptOrdering : Fin k ≃ HitKept selection tagged)
    (index : Fin ((colors security)^(((r+s)+k)*3))) : Option (GroupInput selection tagged) :=
  (indexDecode (colors security) (colors_pos security) (safe security) (groupKind selection tagged)
    ((r+s)+k) (groupOrdering selection tagged keptOrdering) index).map (sourceEquiv selection tagged)

theorem sum_decode {Scalar : Type*} [AddCommMonoid Scalar] {security r s k : ℕ}
    (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (keptOrdering : Fin k ≃ HitKept selection tagged) (summand : GroupInput selection tagged → Scalar) :
    (∑ index : Fin ((colors security)^(((r+s)+k)*3)),
      (decode selection tagged keptOrdering index).elim 0 summand) = ∑ source, summand source := by
  have h := sum_index (colors security) (colors_pos security) (safe security) (groupKind selection tagged)
    ((r+s)+k) (groupOrdering selection tagged keptOrdering) (summand ∘ sourceEquiv selection tagged)
  simpa only [decode, Option.elim_map, Function.comp_apply,
    Equiv.sum_comp (sourceEquiv selection tagged)] using h

theorem index_count_bound {security r s k : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (keptOrdering : Fin k ≃ HitKept selection tagged) :
    (colors security)^(((r+s)+k)*3) ≤ (colors security)^((r+s+tagged.card)*3) := by
  have hk : k ≤ tagged.card := by
    have he := Fintype.card_congr keptOrdering
    simp only [Fintype.card_fin] at he
    apply he.trans_le
    convert hitKept_card_le selection tagged using 1
    congr 1
    exact Subsingleton.elim _ _
  exact Nat.pow_le_pow_right (colors_pos security) (Nat.mul_le_mul_right 3 (Nat.add_le_add_left hk _))

theorem response_eq {security r s k : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (keptOrdering : Fin k ≃ HitKept selection tagged)
    (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (kernel : ControlCoordinates.canonicalKernels (ProposalPrimary.primaryLaw security)
      (ActualControls.bodyReference security) r s) :
    ActualRootResponse.response order horder queue selection tagged layout kernel =
      ∑ index : Fin ((colors security)^(((r+s)+k)*3)),
        (decode selection tagged keptOrdering index).elim 0 (fun source =>
          (controlKernel selection tagged kernel (fun group => (source group).2) *
            RootWeightedSynthesis.untaggedWeight selection tagged source *
            RootWeightedSynthesis.weightedCoefficient selection tagged layout source) •
            ∏ group, RootReferenceColumns.reducedColumn order horder queue selection tagged group (source group)) := by
  rw [sum_decode, RootWeightedSynthesis.response_eq]

end
end CurrentAFT.CurrentGroupSourcePadding
