import AFT.PendingPrimaryExpansion

/-! # Exact locations of unchanged old coordinates after a block replacement -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {New Primary Body : Type*} [Fintype New] [Fintype Primary] [Fintype Body]

def groupedInputEquiv : New ⊕ (Primary ⊕ Body) ≃ Fin (Fintype.card (New ⊕ Primary)+Fintype.card Body) :=
  (Equiv.sumAssoc New Primary Body).symm.trans mixedFiniteEquiv

theorem groupedInputEquiv_forms {Value : Type*}
    (first : Fin (Fintype.card (New ⊕ Primary)) → Value) (second : Fin (Fintype.card Body) → Value) :
    (fun slot => Fin.addCases first second (groupedInputEquiv slot))=
      Sum.elim (fun slot : New => first (Fintype.equivFin (New ⊕ Primary) (Sum.inl slot)))
        (Sum.elim (fun slot : Primary => first (Fintype.equivFin (New ⊕ Primary) (Sum.inr slot)))
          (fun slot : Body => second (Fintype.equivFin Body slot))) := by
  funext slot
  rcases slot with slot|(slot|slot) <;> simp [groupedInputEquiv,mixedFiniteEquiv]

variable {Color : Type*}

theorem splitPrimaryIndex_forms {Value : Type*} (seed : InputSeed Color) (point : Fin seed.primaryOrder)
    (first : Fin seed.primaryOrder → Value) (second : Fin seed.bodyOrder → Value) :
    (fun slot => Fin.addCases first second (splitPrimaryIndex seed point slot))=
      Sum.elim (fun _ : Unit => first point)
        (Sum.elim (fun slot : {other : Fin seed.primaryOrder // other ≠ point} => first slot.val) second) := by
  funext slot
  rcases slot with token|(slot|slot)
  · cases token; simp [splitPrimaryIndex,primarySplitEquiv]
  · simp [splitPrimaryIndex,primarySplitEquiv]
  · simp [splitPrimaryIndex,primarySplitEquiv]

variable [Fintype Color]

theorem groupedFiniteSeed_reference_reindex (primary body : FiniteDist Color)
    (kernel : (New ⊕ (Primary ⊕ Body) → Color) → ℝ) :
    (fun slot => inputReference primary body (groupedFiniteSeed kernel) (groupedInputEquiv slot))=
      Sum.elim (fun _ : New => primary)
        (Sum.elim (fun _ : Primary => primary) (fun _ : Body => body)) := by
  unfold groupedFiniteSeed
  rw [mixedFiniteSeed_reference]
  funext slot
  rcases slot with slot|(slot|slot) <;> simp [groupedInputEquiv]

omit [Fintype Color] in
theorem groupedFiniteSeed_kernel_reindex (kernel : (New ⊕ (Primary ⊕ Body) → Color) → ℝ)
    (word : New ⊕ (Primary ⊕ Body) → Color) :
    (groupedFiniteSeed kernel).kernel (word ∘ groupedInputEquiv.symm)=kernel word := by
  dsimp only [groupedFiniteSeed,mixedFiniteSeed]
  congr 1
  funext slot
  simp [groupedInputEquiv,Function.comp_apply]

end
end AFT.RepresentedPolynomial

namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance pendingGeometryFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
attribute [local instance] actualModulusNeZero

theorem pendingHigherState_mem_old (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (state : PendingInput (Fin (Parameters.modulus n))) (point : Fin state.seed.primaryOrder)
    (selected : Finset (Fin 4)) (old : {other : Fin state.seed.primaryOrder // other ≠ point}) :
    pendingHigherOldEmbedding C n beta operator charts state.seed point selected old ∈
      (pendingHigherState C n beta operator charts state point selected).pending ↔ old.val∈state.pending := by
  change _ ∈ (state.pending.erase point).attach.map _ ↔ _
  rw [Finset.mem_map]
  constructor
  · rintro ⟨source,_,he⟩
    have hh := (pendingHigherOldEmbedding C n beta operator charts state.seed point selected).injective he
    have heq : source.val=old.val := congrArg (fun slot : {other : Fin state.seed.primaryOrder // other≠point} => slot.val) hh
    rw [← heq]
    exact (Finset.mem_erase.mp source.property).2
  · intro ho
    refine ⟨⟨old.val,Finset.mem_erase.mpr ⟨old.property,ho⟩⟩,Finset.mem_attach _ _,?_⟩
    rfl

theorem pendingHigherState_not_mem_new (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (state : PendingInput (Fin (Parameters.modulus n))) (point : Fin state.seed.primaryOrder)
    (selected : Finset (Fin 4)) (new : selected) :
    Fintype.equivFin (selected ⊕ {other : Fin state.seed.primaryOrder // other ≠ point}) (Sum.inl new) ∉
      (pendingHigherState C n beta operator charts state point selected).pending := by
  change _ ∉ (state.pending.erase point).attach.map _
  rw [Finset.mem_map]
  rintro ⟨source,_,he⟩
  have hh := (Fintype.equivFin (selected ⊕ {other : Fin state.seed.primaryOrder // other ≠ point})).injective he
  exact Sum.inr_ne_inl hh

theorem pendingLinearState_card {Color : Type*} (state : PendingInput Color) (hn : state.pending.Nonempty) :
    (pendingLinearState state).pending.card+1=state.pending.card := by
  have he : pendingLinearState state=⟨state.seed,state.pending.erase (state.pending.min' hn)⟩ := by
    simp [pendingLinearState,hn]
  rw [he]
  exact Finset.card_erase_add_one (Finset.min'_mem state.pending hn)

end
end AFT.V7Calibration
