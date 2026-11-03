import CurrentAFT.TaggedOutputFock

/-! # Actual endpoint placement of selected paired groups and their complement -/
namespace CurrentAFT.PairedOutputPlacement
open AFT ActualBlockFock TaggedSelection TaggedOutputFock JointTaggedPhysicalFock
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

def blockEquiv {security r s : ℕ} (selection : Selection security r s) :
    RemovedLabel r s ⊕ selection.kept ≃ BlockIndex security :=
  Equiv.ofBijective (Sum.elim selection.removedEmbedding Subtype.val) (by
    constructor
    · intro first second hequal
      rcases first with first | first <;> rcases second with second | second
      · exact congrArg Sum.inl (selection.removedEmbedding.injective hequal)
      · have hnot := (Finset.mem_sdiff.mp second.property).2
        dsimp only [Sum.elim_inl, Sum.elim_inr] at hequal
        apply False.elim
        apply hnot
        rw [← hequal]
        exact Finset.mem_map.mpr ⟨first, Finset.mem_univ _, rfl⟩
      · have hnot := (Finset.mem_sdiff.mp first.property).2
        dsimp only [Sum.elim_inl, Sum.elim_inr] at hequal
        apply False.elim
        apply hnot
        rw [hequal]
        exact Finset.mem_map.mpr ⟨second, Finset.mem_univ _, rfl⟩
      · exact congrArg Sum.inr (Subtype.ext hequal)
    · intro index
      by_cases hremoved : index ∈ selection.removed
      · obtain ⟨label, _, hequal⟩ := Finset.mem_map.mp hremoved
        exact ⟨Sum.inl label, hequal⟩
      · exact ⟨Sum.inr ⟨index, by simp [Selection.kept, hremoved]⟩, rfl⟩)

@[simp] theorem blockEquiv_removed {security r s : ℕ} (selection : Selection security r s)
    (index : RemovedLabel r s) : blockEquiv selection (.inl index) = selection.removedEmbedding index := rfl

@[simp] theorem blockEquiv_kept {security r s : ℕ} (selection : Selection security r s)
    (index : selection.kept) : blockEquiv selection (.inr index) = index.val := rfl

/-- The compensator is output zero; the three leg outputs follow it. -/
def roleRemovedEquiv {security r s : ℕ} (selection : Selection security r s) :
    Sigma (roleSlots r s) ≃ Sigma (fun index : RemovedLabel r s => Slots security (selection.removedEmbedding index)) where
  toFun
    | ⟨.inl index, slot⟩ => Fin.cases ⟨.inr (.inl index), (0 : Fin 1)⟩ (fun slot => ⟨.inl index, slot⟩) slot
    | ⟨.inr index, slot⟩ => ⟨.inr (.inr index), slot⟩
  invFun
    | ⟨.inl index, slot⟩ => ⟨.inl index, slot.succ⟩
    | ⟨.inr (.inl index), _⟩ => ⟨.inl index, (0 : Fin 4)⟩
    | ⟨.inr (.inr index), slot⟩ => ⟨.inr index, slot⟩
  left_inv := by
    rintro ⟨index | index, slot⟩
    · change Fin 4 at slot
      fin_cases slot <;> rfl
    · rfl
  right_inv := by
    rintro ⟨index | (index | index), slot⟩
    · rfl
    · have hequal : slot = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
      subst slot
      rfl
    · rfl

def taggedRemovedEquiv {security r s : ℕ} (selection : Selection security r s) :
    Sigma (physicalSlots r s) ≃ Sigma (fun index : RemovedLabel r s => Slots security (selection.removedEmbedding index)) :=
  (Equiv.sigmaCongrLeft (β := roleSlots r s) finSumFinEquiv.symm).trans (roleRemovedEquiv selection)

def gather {security r s : ℕ} (selection : Selection security r s) :
    OutputIndex selection ≃ Sigma (Slots security) :=
  (Equiv.sumCongr (taggedRemovedEquiv selection) (Equiv.refl _)).trans
    ((Equiv.sumSigmaDistrib (fun index : RemovedLabel r s ⊕ selection.kept =>
      Slots security (blockEquiv selection index))).symm.trans
        (Equiv.sigmaCongrLeft (β := Slots security) (blockEquiv selection)))

@[simp] theorem gather_kept {security r s : ℕ} (selection : Selection security r s)
    (index : selection.kept) (slot : Slots security index.val) :
    gather selection (.inr ⟨index, slot⟩) = ⟨index.val, slot⟩ := rfl

def physicalRoleIndex (r s : ℕ) (index : Sigma (roleSlots r s)) : Sigma (physicalSlots r s) :=
  (Equiv.sigmaCongrLeft (β := roleSlots r s) finSumFinEquiv.symm).symm index

def primaryIndex {r s : ℕ} (index : Fin r) (slot : Fin 4) : Sigma (physicalSlots r s) :=
  physicalRoleIndex r s ⟨.inl index, slot⟩

def ordinaryIndex {r s : ℕ} (index : Fin s) (slot : Fin 1) : Sigma (physicalSlots r s) :=
  physicalRoleIndex r s ⟨.inr index, slot⟩

@[simp] theorem primaryIndex_fst {r s : ℕ} (index : Fin r) (slot : Fin 4) :
    (primaryIndex (s := s) index slot).fst = finSumFinEquiv (.inl index) := rfl

@[simp] theorem ordinaryIndex_fst {r s : ℕ} (index : Fin s) (slot : Fin 1) :
    (ordinaryIndex (r := r) index slot).fst = finSumFinEquiv (.inr index) := rfl

theorem gather_role {security r s : ℕ} (selection : Selection security r s)
    (index : Sigma (roleSlots r s)) :
    gather selection (.inl (physicalRoleIndex r s index)) =
      ⟨selection.removedEmbedding ((roleRemovedEquiv selection index).fst),
        (roleRemovedEquiv selection index).snd⟩ := by
  have hequal : taggedRemovedEquiv selection (physicalRoleIndex r s index) =
      roleRemovedEquiv selection index :=
    congrArg (roleRemovedEquiv selection)
      ((Equiv.sigmaCongrLeft (β := roleSlots r s) finSumFinEquiv.symm).apply_symm_apply index)
  exact congrArg (fun point : Sigma (fun label : RemovedLabel r s =>
      Slots security (selection.removedEmbedding label)) =>
        (⟨selection.removedEmbedding point.fst, point.snd⟩ : Sigma (Slots security))) hequal

@[simp] theorem gather_compensator {security r s : ℕ} (selection : Selection security r s) (index : Fin r) :
    gather selection (.inl (primaryIndex index 0)) =
      ⟨.inr (.inl (selection.compensator index)), (0 : Fin 1)⟩ := by
  rw [primaryIndex, gather_role]
  rfl

@[simp] theorem gather_primary {security r s : ℕ} (selection : Selection security r s)
    (index : Fin r) (slot : Fin 3) :
    gather selection (.inl (primaryIndex index slot.succ)) =
      ⟨.inl (selection.primary index), slot⟩ := by
  rw [primaryIndex, gather_role]
  rfl

@[simp] theorem gather_ordinary {security r s : ℕ} (selection : Selection security r s)
    (index : Fin s) (slot : Fin 1) :
    gather selection (.inl (ordinaryIndex index slot)) =
      ⟨.inr (.inl (selection.body index)), slot⟩ := by
  rw [ordinaryIndex, gather_role]
  rfl

end
end CurrentAFT.PairedOutputPlacement
