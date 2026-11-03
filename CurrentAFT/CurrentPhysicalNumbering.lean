import CurrentAFT.ActualBlockFock
import AFT.FiniteBlockNumbering

/-! Explicit physical endpoint numbering for the current construction.
Primary leg slots come first, in (leg,slot) order, followed by all singleton
centers and then queue slots. No chosen finite enumeration is executed. -/
namespace CurrentAFT.CurrentPhysicalNumbering
open AFT ActualBlockFock
set_option maxHeartbeats 700000
set_option maxRecDepth 4096
attribute [local irreducible] Parameters.bodySize Parameters.legCount Parameters.dimension


def split (security : ℕ) : Sigma (Slots security) ≃
    ((Fin (Parameters.legCount security) × Fin 3) ⊕
      (Fin (centerCount security) ⊕ Fin (Parameters.modulus security))) where
  toFun
    | ⟨.inl leg, slot⟩ => .inl (leg, slot)
    | ⟨.inr (.inl center), _⟩ => .inr (.inl center)
    | ⟨.inr (.inr queue), _⟩ => .inr (.inr queue)
  invFun
    | .inl (leg, slot) => ⟨.inl leg, slot⟩
    | .inr (.inl center) => ⟨.inr (.inl center), (0 : Fin 1)⟩
    | .inr (.inr queue) => ⟨.inr (.inr queue), (0 : Fin 1)⟩
  left_inv := by
    rintro ⟨leg | (center | queue), slot⟩
    · rfl
    · change Fin 1 at slot
      have he : slot = 0 := Subsingleton.elim _ _
      subst slot
      rfl
    · change Fin 1 at slot
      have he : slot = 0 := Subsingleton.elim _ _
      subst slot
      rfl
  right_inv := by
    intro point
    rcases point with pair | rest
    · rcases pair with ⟨leg, slot⟩; rfl
    · rcases rest with center | queue <;> rfl

 theorem dimension_eq (security : ℕ) :
    Parameters.legCount security * 3 + (centerCount security + Parameters.modulus security) = Parameters.dimension security := by
  have h := ProposalPrimary.population_room security
  unfold centerCount Parameters.dimension
  omega


def numbering (security : ℕ) : Sigma (Slots security) ≃ Fin (Parameters.dimension security) :=
  (split security).trans (((Equiv.sumCongr finProdFinEquiv finSumFinEquiv).trans finSumFinEquiv).trans
    (finCongr (dimension_eq security)))

 theorem numbering_primary (security : ℕ) (leg : Fin (Parameters.legCount security)) (slot : Fin 3) :
    (numbering security ⟨.inl leg, slot⟩).val = slot.val + 3 * leg.val := by
  rfl

 theorem numbering_center (security : ℕ) (center : Fin (centerCount security)) :
    (numbering security ⟨.inr (.inl center), (0 : Fin 1)⟩).val = Parameters.legCount security * 3 + center.val := by
  rfl

 theorem numbering_queue (security : ℕ) (queue : Fin (Parameters.modulus security)) :
    (numbering security ⟨.inr (.inr queue), (0 : Fin 1)⟩).val =
      Parameters.legCount security * 3 + (centerCount security + queue.val) := by
  rfl

/-- The generic three-plus-singleton block program uses precisely this explicit numbering. -/
def blocks (security : ℕ) : Sigma (Slots security) ≃
    Sigma (blockSlotsProgram (Parameters.legCount security) (centerCount security + Parameters.modulus security)) where
  toFun
    | ⟨.inl leg, slot⟩ => ⟨.inl leg, slot⟩
    | ⟨.inr (.inl center), slot⟩ => ⟨.inr (finSumFinEquiv (.inl center)), slot⟩
    | ⟨.inr (.inr queue), slot⟩ => ⟨.inr (finSumFinEquiv (.inr queue)), slot⟩
  invFun
    | ⟨.inl leg, slot⟩ => ⟨.inl leg, slot⟩
    | ⟨.inr body, slot⟩ => match finSumFinEquiv.symm body with
      | .inl center => ⟨.inr (.inl center), slot⟩
      | .inr queue => ⟨.inr (.inr queue), slot⟩
  left_inv := by
    rintro ⟨leg | (center | queue), slot⟩
    · rfl
    · simp only [Equiv.symm_apply_apply]
    · simp only [Equiv.symm_apply_apply]
  right_inv := by
    rintro ⟨leg | body, slot⟩
    · rfl
    · obtain ⟨center | queue, rfl⟩ := finSumFinEquiv.surjective body <;> simp only [Equiv.symm_apply_apply]

 theorem numbering_blocks (security : ℕ) : numbering security =
    (blocks security).trans ((blockVertexNumbering (Parameters.legCount security)
      (centerCount security + Parameters.modulus security)).trans
        (finCongr (by simpa only [Nat.mul_one, Nat.add_zero] using dimension_eq security))) := by
  apply Equiv.ext
  rintro ⟨leg | (center | queue), slot⟩ <;> apply Fin.ext
  · rfl
  · change Fin 1 at slot
    have he : slot = 0 := Subsingleton.elim _ _
    subst slot
    simp [numbering_center, blocks, Equiv.trans_apply, blockVertexNumbering, blockVertexSplit, finSumFinEquiv, finProdFinEquiv]
  · change Fin 1 at slot
    have he : slot = 0 := Subsingleton.elim _ _
    subst slot
    simp [numbering_queue, blocks, Equiv.trans_apply, blockVertexNumbering, blockVertexSplit, finSumFinEquiv, finProdFinEquiv]

end CurrentAFT.CurrentPhysicalNumbering
