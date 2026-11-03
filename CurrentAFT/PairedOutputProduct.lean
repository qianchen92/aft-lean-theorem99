import CurrentAFT.PairedOutputPlacement

/-! # Exact product regrouping at the actual selected endpoint placement -/
namespace CurrentAFT.PairedOutputProduct
open AFT ActualBlockFock TaggedSelection TaggedOutputFock PairedOutputPlacement
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

variable {Color Ring : Type*} [CommMonoid Ring]

def selectedPairs {security r s : ℕ} (selection : Selection security r s)
    (factor : (block : BlockIndex security) → (Slots security block → Color) → Ring)
    (word : OutputIndex selection → Color) : Ring :=
  ∏ index : Fin r,
    factor (.inr (.inl (selection.compensator index))) (fun _ => word (.inl (primaryIndex index 0))) *
      factor (.inl (selection.primary index)) (fun slot => word (.inl (primaryIndex index slot.succ)))

def selectedBodies {security r s : ℕ} (selection : Selection security r s)
    (factor : (block : BlockIndex security) → (Slots security block → Color) → Ring)
    (word : OutputIndex selection → Color) : Ring :=
  ∏ index : Fin s, factor (.inr (.inl (selection.body index)))
    (fun slot => word (.inl (ordinaryIndex index slot)))

def remaining {security r s : ℕ} (selection : Selection security r s)
    (factor : (block : BlockIndex security) → (Slots security block → Color) → Ring)
    (word : OutputIndex selection → Color) : Ring :=
  ∏ index : selection.kept, factor index.val (fun slot => word (.inr ⟨index, slot⟩))

/-- Every original block appears exactly once. Selected primary triples
and their assigned compensators are grouped into the real four slots. -/
theorem gather_product {security r s : ℕ} (selection : Selection security r s)
    (factor : (block : BlockIndex security) → (Slots security block → Color) → Ring)
    (word : Sigma (Slots security) → Color) :
    (∏ block, factor block (fun slot => word ⟨block, slot⟩)) =
      selectedPairs selection factor (word ∘ gather selection) *
        selectedBodies selection factor (word ∘ gather selection) * remaining selection factor (word ∘ gather selection) := by
  have hsplit := Equiv.prod_comp (blockEquiv selection)
    (fun block => factor block (fun slot => word ⟨block, slot⟩))
  rw [← hsplit]
  simp only [Fintype.prod_sum_type, blockEquiv_removed, blockEquiv_kept,
    RemovedLabel, Selection.removedEmbedding, Function.Embedding.coeFn_mk,
    selectedPairs, selectedBodies, remaining, Function.comp_apply,
    gather_compensator, gather_primary, gather_ordinary, gather_kept, Finset.prod_mul_distrib]
  have hsingle (index : Fin r) :
      factor (.inr (.inl (selection.compensator index)))
          (fun slot => word ⟨.inr (.inl (selection.compensator index)), slot⟩) =
        factor (.inr (.inl (selection.compensator index)))
          (fun _ => word ⟨.inr (.inl (selection.compensator index)), (0 : Fin 1)⟩) := by
    congr 1
    funext slot
    rw [Subsingleton.elim (α := Fin 1) slot 0]
  simp_rw [hsingle]
  ac_rfl

theorem gather_inverse_product {security r s : ℕ} (selection : Selection security r s)
    (factor : (block : BlockIndex security) → (Slots security block → Color) → Ring)
    (word : OutputIndex selection → Color) :
    (∏ block, factor block (fun slot => word ((gather selection).symm ⟨block, slot⟩))) =
      selectedPairs selection factor word * selectedBodies selection factor word * remaining selection factor word := by
  simpa only [Function.comp_def, Equiv.symm_apply_apply] using
    gather_product selection factor (word ∘ (gather selection).symm)

end
end CurrentAFT.PairedOutputProduct
