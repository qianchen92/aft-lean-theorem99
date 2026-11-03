import AFT.IndependentPhysicalForms
import AFT.PendingPrimaryGeometry

/-! # Physical polynomial channels under the original-coordinate bookkeeping -/
namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration RepresentedPolynomial MixedKernel
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance pendingPhysicalReindexFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance pendingPhysicalReindexUnitDecEq : DecidableEq Unit := Classical.decEq _
local instance pendingPhysicalReindexSelectedDecEq (s : Finset (Fin 4)) : DecidableEq s := Classical.decEq _
attribute [local instance] actualModulusNeZero

def pendingOtherForms (C : ℝ) (n : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (state : PendingInput (Fin (Parameters.modulus n))) (point : Fin state.seed.primaryOrder) :
    ({other : Fin state.seed.primaryOrder // other ≠ point} ⊕ Fin state.seed.bodyOrder) →
      Fin (Parameters.modulus n) → Table (Fin (Parameters.modulus n)) :=
  Sum.elim (fun old => if old.val∈state.pending then independentPairedForm C n beta charts
      else channelForm (actualPrimaryChannel C n)) (fun _ => channelForm (actualBodyChannel n))

theorem pendingPhysicalForms_split (C : ℝ) (n : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (state : PendingInput (Fin (Parameters.modulus n))) (point : Fin state.seed.primaryOrder) (hp : point∈state.pending) :
    (fun slot => pendingPhysicalForms C n beta charts state (splitPrimaryIndex state.seed point slot))=
      Sum.elim (fun _ : Unit => independentPairedForm C n beta charts) (pendingOtherForms C n beta charts state point) := by
  unfold pendingPhysicalForms
  rw [splitPrimaryIndex_forms]
  simp only [if_pos hp,pendingOtherForms]

theorem pendingErasedForms_split (C : ℝ) (n : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (state : PendingInput (Fin (Parameters.modulus n))) (point : Fin state.seed.primaryOrder) :
    (fun slot => pendingPhysicalForms C n beta charts ⟨state.seed,state.pending.erase point⟩
      (splitPrimaryIndex state.seed point slot))=
      Sum.elim (fun _ : Unit => channelForm (actualPrimaryChannel C n)) (pendingOtherForms C n beta charts state point) := by
  unfold pendingPhysicalForms
  rw [splitPrimaryIndex_forms]
  funext slot
  rcases slot with token|(old|old)
  · cases token; simp
  · have hne : old.val ≠ point := old.property
    by_cases ho : old.val∈state.pending <;> simp [pendingOtherForms,ho,hne]
  · rfl

theorem pendingHigherForms_reindex (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (state : PendingInput (Fin (Parameters.modulus n))) (point : Fin state.seed.primaryOrder) (selected : Finset (Fin 4)) :
    (fun slot => pendingPhysicalForms C n beta charts (pendingHigherState C n beta operator charts state point selected)
      (groupedInputEquiv (New := selected) (Primary := {other : Fin state.seed.primaryOrder // other ≠ point})
        (Body := Fin state.seed.bodyOrder) slot))=
      Sum.elim (fun _ : selected => channelForm (actualPrimaryChannel C n)) (pendingOtherForms C n beta charts state point) := by
  unfold pendingPhysicalForms
  rw [groupedInputEquiv_forms]
  funext slot
  rcases slot with new|(old|old)
  · simp only [Sum.elim_inl,if_neg (pendingHigherState_not_mem_new C n beta operator charts state point selected new)]
  · change (if pendingHigherOldEmbedding C n beta operator charts state.seed point selected old∈
      (pendingHigherState C n beta operator charts state point selected).pending then _ else _)=_
    have he := pendingHigherState_mem_old C n beta operator charts state point selected old
    by_cases ho : old.val∈state.pending
    · simp [pendingOtherForms,ho,he.mpr ho]
    · have hn : pendingHigherOldEmbedding C n beta operator charts state.seed point selected old∉
          (pendingHigherState C n beta operator charts state point selected).pending := fun h => ho (he.mp h)
      rw [if_neg hn]
      simp only [pendingOtherForms,Sum.elim_inr,Sum.elim_inl,if_neg ho]
  · rfl

theorem pendingPhysicalPolynomial_split (C : ℝ) (n : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (state : PendingInput (Fin (Parameters.modulus n))) (point : Fin state.seed.primaryOrder) (hp : point∈state.pending) :
    pendingPhysicalPolynomial C n beta charts state=
      jointChannelPolynomial (Sum.elim (fun _ : Unit => actualPrimaryLaw C n beta)
        (Sum.elim (fun _ : {other : Fin state.seed.primaryOrder // other ≠ point} => actualPrimaryLaw C n beta)
          (fun _ : Fin state.seed.bodyOrder => actualBodyLaw C n beta)))
        (Sum.elim (fun _ : Unit => independentPairedForm C n beta charts) (pendingOtherForms C n beta charts state point))
        (singletonJoin (splitPrimaryKernel state.seed point)) := by
  have he := jointChannelPolynomial_equiv (splitPrimaryIndex state.seed point).symm
    (inputReference (actualPrimaryLaw C n beta) (actualBodyLaw C n beta) state.seed)
    (pendingPhysicalForms C n beta charts state) state.seed.kernel
  simpa only [Equiv.symm_symm,splitPrimaryIndex_reference,pendingPhysicalForms_split C n beta charts state point hp,
    ← splitPrimaryKernel_join,pendingPhysicalPolynomial] using he.symm

theorem pendingErasedPolynomial_split (C : ℝ) (n : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (state : PendingInput (Fin (Parameters.modulus n))) (point : Fin state.seed.primaryOrder) :
    pendingPhysicalPolynomial C n beta charts ⟨state.seed,state.pending.erase point⟩=
      jointChannelPolynomial (Sum.elim (fun _ : Unit => actualPrimaryLaw C n beta)
        (Sum.elim (fun _ : {other : Fin state.seed.primaryOrder // other ≠ point} => actualPrimaryLaw C n beta)
          (fun _ : Fin state.seed.bodyOrder => actualBodyLaw C n beta)))
        (Sum.elim (fun _ : Unit => channelForm (actualPrimaryChannel C n)) (pendingOtherForms C n beta charts state point))
        (singletonJoin (splitPrimaryKernel state.seed point)) := by
  have he := jointChannelPolynomial_equiv (splitPrimaryIndex state.seed point).symm
    (inputReference (actualPrimaryLaw C n beta) (actualBodyLaw C n beta) state.seed)
    (pendingPhysicalForms C n beta charts ⟨state.seed,state.pending.erase point⟩) state.seed.kernel
  simpa only [Equiv.symm_symm,splitPrimaryIndex_reference,pendingErasedForms_split,
    ← splitPrimaryKernel_join,pendingPhysicalPolynomial] using he.symm

theorem pendingHigherPolynomial_reindex (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (state : PendingInput (Fin (Parameters.modulus n))) (point : Fin state.seed.primaryOrder) (selected : Finset (Fin 4)) :
    pendingPhysicalPolynomial C n beta charts (pendingHigherState C n beta operator charts state point selected)=
      jointChannelPolynomial (Sum.elim (fun _ : selected => actualPrimaryLaw C n beta)
        (Sum.elim (fun _ : {other : Fin state.seed.primaryOrder // other ≠ point} => actualPrimaryLaw C n beta)
          (fun _ : Fin state.seed.bodyOrder => actualBodyLaw C n beta)))
        (Sum.elim (fun _ : selected => channelForm (actualPrimaryChannel C n)) (pendingOtherForms C n beta charts state point))
        (independentJointInverse C n beta operator charts
          (Sum.elim (fun _ : {other : Fin state.seed.primaryOrder // other ≠ point} => actualPrimaryLaw C n beta)
            (fun _ : Fin state.seed.bodyOrder => actualBodyLaw C n beta)) selected (splitPrimaryKernel state.seed point)) := by
  let higher := pendingHigherState C n beta operator charts state point selected
  let equiv := groupedInputEquiv (New := selected) (Primary := {other : Fin state.seed.primaryOrder // other ≠ point})
    (Body := Fin state.seed.bodyOrder)
  have he := jointChannelPolynomial_equiv equiv.symm
    (inputReference (actualPrimaryLaw C n beta) (actualBodyLaw C n beta) higher.seed)
    (pendingPhysicalForms C n beta charts higher) higher.seed.kernel
  simp only [Equiv.symm_symm] at he
  have hr := groupedFiniteSeed_reference_reindex (actualPrimaryLaw C n beta) (actualBodyLaw C n beta)
    (independentJointInverse C n beta operator charts
      (Sum.elim (fun _ : {other : Fin state.seed.primaryOrder // other ≠ point} => actualPrimaryLaw C n beta)
        (fun _ : Fin state.seed.bodyOrder => actualBodyLaw C n beta)) selected (splitPrimaryKernel state.seed point))
  have hk : (fun word => higher.seed.kernel (word ∘ equiv.symm))=
      independentJointInverse C n beta operator charts
        (Sum.elim (fun _ : {other : Fin state.seed.primaryOrder // other ≠ point} => actualPrimaryLaw C n beta)
          (fun _ : Fin state.seed.bodyOrder => actualBodyLaw C n beta)) selected (splitPrimaryKernel state.seed point) := by
    funext word
    exact groupedFiniteSeed_kernel_reindex _ word
  change (fun slot => inputReference (actualPrimaryLaw C n beta) (actualBodyLaw C n beta) higher.seed (equiv slot))=_ at hr
  have hf : (fun slot => pendingPhysicalForms C n beta charts higher (equiv slot))=
      Sum.elim (fun _ : selected => channelForm (actualPrimaryChannel C n)) (pendingOtherForms C n beta charts state point) :=
    pendingHigherForms_reindex C n beta operator charts state point selected
  rw [hr,hf,hk] at he
  exact he.symm

end
end AFT.V7Calibration
