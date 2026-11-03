import CurrentAFT.ActualBlockMean
import CurrentAFT.JointTaggedPhysicalFock
import CurrentAFT.OmittedBlockMean

/-! # Actual distinct primary/compensator/body selections and physical complements -/

namespace CurrentAFT.TaggedSelection

open AFT ActualBlockFock
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- Actual distinct public control positions. A selected primary uses one
triple and one separate compensator center. Ordinary selections are
disjoint from those compensators. -/
structure Selection (security r s : ℕ) where
  primary : Fin r ↪ Fin (Parameters.legCount security)
  compensator : Fin r ↪ Fin (centerCount security)
  body : Fin s ↪ Fin (centerCount security)
  separated : ∀ first second, compensator first ≠ body second

abbrev RemovedLabel (r s : ℕ) := Fin r ⊕ (Fin r ⊕ Fin s)

def Selection.removedEmbedding {security r s : ℕ} (selection : Selection security r s) :
    RemovedLabel r s ↪ BlockIndex security where
  toFun
    | .inl index => .inl (selection.primary index)
    | .inr (.inl index) => .inr (.inl (selection.compensator index))
    | .inr (.inr index) => .inr (.inl (selection.body index))
  inj' := by
    intro first second hequal
    rcases first with first | first
    · rcases second with second | second
      · exact congrArg Sum.inl (selection.primary.injective (Sum.inl.inj hequal))
      · cases second <;> cases hequal
    · rcases first with first | first
      · rcases second with second | second
        · cases hequal
        · rcases second with second | second
          · exact congrArg (Sum.inr ∘ Sum.inl) (selection.compensator.injective (Sum.inl.inj (Sum.inr.inj hequal)))
          · exact False.elim (selection.separated first second (Sum.inl.inj (Sum.inr.inj hequal)))
      · rcases second with second | second
        · cases hequal
        · rcases second with second | second
          · exact False.elim (selection.separated second first (Sum.inl.inj (Sum.inr.inj hequal)).symm)
          · exact congrArg (Sum.inr ∘ Sum.inr) (selection.body.injective (Sum.inl.inj (Sum.inr.inj hequal)))

def Selection.removed {security r s : ℕ} (selection : Selection security r s) : Finset (BlockIndex security) :=
  Finset.univ.map selection.removedEmbedding

def Selection.kept {security r s : ℕ} (selection : Selection security r s) : Finset (BlockIndex security) :=
  Finset.univ \ selection.removed

theorem Selection.removed_card {security r s : ℕ} (selection : Selection security r s) :
    selection.removed.card = 2 * r + s := by
  simp only [Selection.removed, Finset.card_map, Finset.card_univ, RemovedLabel,
    Fintype.card_sum, Fintype.card_fin]
  omega

theorem Selection.removed_complement {security r s : ℕ} (selection : Selection security r s) :
    OmittedBlockMean.removed selection.kept = selection.removed := by
  ext index
  simp [OmittedBlockMean.removed, Selection.kept]

theorem Selection.removed_outputs {security r s : ℕ} (selection : Selection security r s) :
    (∑ index ∈ selection.removed, Fintype.card (Slots security index)) = 4 * r + s := by
  simp only [Selection.removed, Finset.sum_map]
  change (∑ label : RemovedLabel r s, Fintype.card (Slots security (selection.removedEmbedding label))) = _
  simp [RemovedLabel, Fintype.sum_sum_type, Selection.removedEmbedding, Slots]
  omega

theorem Selection.kept_outputs {security r s : ℕ} (selection : Selection security r s) :
    Fintype.card (Sigma (fun index : selection.kept => Slots security index.val)) + (4 * r + s) =
      Parameters.dimension security := by
  have hkept : Fintype.card (Sigma (fun index : selection.kept => Slots security index.val)) =
      ∑ index ∈ selection.kept, Fintype.card (Slots security index) := by
    rw [Fintype.card_sigma, Finset.sum_subtype selection.kept (fun _ => Iff.rfl)]
  have hfull : (∑ index : BlockIndex security, Fintype.card (Slots security index)) =
      Parameters.dimension security := by rw [← Fintype.card_sigma]; exact physical_card security
  have hsplit := Finset.sum_sdiff (f := fun index : BlockIndex security => Fintype.card (Slots security index))
    (Finset.subset_univ selection.removed)
  rw [← Selection.kept, selection.removed_outputs, hfull] at hsplit
  rw [hkept]
  exact hsplit

/-- Replacing each selected triple plus compensator by its real four-output
channel, and each selected ordinary center by a singleton, keeps exactly
the original full output dimension. -/
theorem Selection.full_output_card {security r s : ℕ} (selection : Selection security r s) :
    Fintype.card ((Sigma (JointTaggedPhysicalFock.physicalSlots r s)) ⊕
      Sigma (fun index : selection.kept => Slots security index.val)) = Parameters.dimension security := by
  rw [Fintype.card_sum, JointTaggedPhysicalFock.physicalSlots_card]
  have h := selection.kept_outputs
  omega

end

end CurrentAFT.TaggedSelection
