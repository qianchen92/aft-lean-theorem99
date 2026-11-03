import AFT.KernelPolynomial
import AFT.PendingHigherColumns

/-! # The pending expansion under arbitrary input polynomial forms -/
namespace AFT.V7Calibration
open GaussianSource RepresentedPolynomial
open MixedKernel
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance pendingKernelFormsFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance pendingKernelFormsUnitDecEq : DecidableEq Unit := Classical.decEq _
local instance pendingKernelFormsSelectedDecEq (s : Finset (Fin 4)) : DecidableEq s := Classical.decEq _
variable {Color Output : Type*} [Fintype Color]

def pendingKernelForms (primary body pendingForm : Color → Table Output) (state : PendingInput Color) :
    Fin (state.seed.primaryOrder+state.seed.bodyOrder) → Color → Table Output :=
  Fin.addCases (fun index => if index∈state.pending then pendingForm else primary) (fun _ => body)

def pendingKernelPolynomial (primary body pendingForm : Color → Table Output) (state : PendingInput Color) : Table Output :=
  kernelPolynomial (pendingKernelForms primary body pendingForm state) state.seed.kernel

def pendingOtherKernelForms (primary body pendingForm : Color → Table Output)
    (state : PendingInput Color) (point : Fin state.seed.primaryOrder) :
    ({other : Fin state.seed.primaryOrder // other≠point} ⊕ Fin state.seed.bodyOrder) → Color → Table Output :=
  Sum.elim (fun old => if old.val∈state.pending then pendingForm else primary) (fun _ => body)

theorem pendingKernelPolynomial_empty (primary body pendingForm : Color → Table Output)
    (state : PendingInput Color) (he : state.pending=∅) :
    pendingKernelPolynomial primary body pendingForm state=inputKernelPolynomial primary body state.seed := by
  unfold pendingKernelPolynomial inputKernelPolynomial
  congr 1
  funext slot
  cases slot using Fin.addCases <;> simp [pendingKernelForms,he]

omit [Fintype Color] in
theorem pendingKernelForms_split (primary body pendingForm : Color → Table Output)
    (state : PendingInput Color) (point : Fin state.seed.primaryOrder) (hp : point∈state.pending) :
    (fun slot => pendingKernelForms primary body pendingForm state (splitPrimaryIndex state.seed point slot))=
      Sum.elim (fun _ : Unit => pendingForm) (pendingOtherKernelForms primary body pendingForm state point) := by
  unfold pendingKernelForms
  rw [splitPrimaryIndex_forms]
  simp only [if_pos hp,pendingOtherKernelForms]

omit [Fintype Color] in
theorem pendingErasedKernelForms_split (primary body pendingForm : Color → Table Output)
    (state : PendingInput Color) (point : Fin state.seed.primaryOrder) :
    (fun slot => pendingKernelForms primary body pendingForm ⟨state.seed,state.pending.erase point⟩
      (splitPrimaryIndex state.seed point slot))=
      Sum.elim (fun _ : Unit => primary) (pendingOtherKernelForms primary body pendingForm state point) := by
  unfold pendingKernelForms
  rw [splitPrimaryIndex_forms]
  funext slot
  rcases slot with token|(old|old)
  · cases token; simp
  · have hne : old.val≠point := old.property
    by_cases ho : old.val∈state.pending <;> simp [pendingOtherKernelForms,ho,hne]
  · rfl

theorem pendingKernelPolynomial_split (primary body pendingForm : Color → Table Output)
    (state : PendingInput Color) (point : Fin state.seed.primaryOrder) (hp : point∈state.pending) :
    pendingKernelPolynomial primary body pendingForm state=
      kernelPolynomial (Sum.elim (fun _ : Unit => pendingForm) (pendingOtherKernelForms primary body pendingForm state point))
        (singletonJoin (splitPrimaryKernel state.seed point)) := by
  have he := kernelPolynomial_equiv (splitPrimaryIndex state.seed point).symm
    (pendingKernelForms primary body pendingForm state) state.seed.kernel
  simpa only [Equiv.symm_symm,pendingKernelForms_split primary body pendingForm state point hp,
    ←splitPrimaryKernel_join,pendingKernelPolynomial] using he.symm

theorem pendingErasedKernelPolynomial_split (primary body pendingForm : Color → Table Output)
    (state : PendingInput Color) (point : Fin state.seed.primaryOrder) :
    pendingKernelPolynomial primary body pendingForm ⟨state.seed,state.pending.erase point⟩=
      kernelPolynomial (Sum.elim (fun _ : Unit => primary) (pendingOtherKernelForms primary body pendingForm state point))
        (singletonJoin (splitPrimaryKernel state.seed point)) := by
  have he := kernelPolynomial_equiv (splitPrimaryIndex state.seed point).symm
    (pendingKernelForms primary body pendingForm ⟨state.seed,state.pending.erase point⟩) state.seed.kernel
  simpa only [Equiv.symm_symm,pendingErasedKernelForms_split,
    ←splitPrimaryKernel_join,pendingKernelPolynomial] using he.symm

variable (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)

theorem pendingHigherKernelForms_reindex
    (primary body pendingForm : Fin (Parameters.modulus n) → Table Output)
    (state : PendingInput (Fin (Parameters.modulus n))) (point : Fin state.seed.primaryOrder) (selected : Finset (Fin 4)) :
    (fun slot => pendingKernelForms primary body pendingForm (pendingHigherState C n beta operator charts state point selected)
      (groupedInputEquiv (New := selected) (Primary := {other : Fin state.seed.primaryOrder // other≠point})
        (Body := Fin state.seed.bodyOrder) slot))=
      Sum.elim (fun _ : selected => primary) (pendingOtherKernelForms primary body pendingForm state point) := by
  unfold pendingKernelForms
  rw [groupedInputEquiv_forms]
  funext slot
  rcases slot with new|(old|old)
  · simp only [Sum.elim_inl,if_neg (pendingHigherState_not_mem_new C n beta operator charts state point selected new)]
  · change (if pendingHigherOldEmbedding C n beta operator charts state.seed point selected old∈
      (pendingHigherState C n beta operator charts state point selected).pending then _ else _)=_
    have he := pendingHigherState_mem_old C n beta operator charts state point selected old
    by_cases ho : old.val∈state.pending
    · simp [pendingOtherKernelForms,ho,he.mpr ho]
    · have hn : pendingHigherOldEmbedding C n beta operator charts state.seed point selected old∉
          (pendingHigherState C n beta operator charts state point selected).pending := fun h => ho (he.mp h)
      rw [if_neg hn]
      simp only [pendingOtherKernelForms,Sum.elim_inr,Sum.elim_inl,if_neg ho]
  · rfl

theorem pendingHigherKernelPolynomial_reindex
    (primary body pendingForm : Fin (Parameters.modulus n) → Table Output)
    (state : PendingInput (Fin (Parameters.modulus n))) (point : Fin state.seed.primaryOrder) (selected : Finset (Fin 4)) :
    pendingKernelPolynomial primary body pendingForm (pendingHigherState C n beta operator charts state point selected)=
      kernelPolynomial (Sum.elim (fun _ : selected => primary) (pendingOtherKernelForms primary body pendingForm state point))
        (independentJointInverse C n beta operator charts
          (Sum.elim (fun _ : {other : Fin state.seed.primaryOrder // other≠point} => actualPrimaryLaw C n beta)
            (fun _ : Fin state.seed.bodyOrder => actualBodyLaw C n beta)) selected (splitPrimaryKernel state.seed point)) := by
  let higher := pendingHigherState C n beta operator charts state point selected
  let equiv := groupedInputEquiv (New := selected) (Primary := {other : Fin state.seed.primaryOrder // other≠point})
    (Body := Fin state.seed.bodyOrder)
  have he := kernelPolynomial_equiv equiv.symm (pendingKernelForms primary body pendingForm higher) higher.seed.kernel
  simp only [Equiv.symm_symm] at he
  have hk : (fun word => higher.seed.kernel (word ∘ equiv.symm))=
      independentJointInverse C n beta operator charts
        (Sum.elim (fun _ : {other : Fin state.seed.primaryOrder // other≠point} => actualPrimaryLaw C n beta)
          (fun _ : Fin state.seed.bodyOrder => actualBodyLaw C n beta)) selected (splitPrimaryKernel state.seed point) := by
    funext word
    exact groupedFiniteSeed_kernel_reindex _ word
  have hf : (fun slot => pendingKernelForms primary body pendingForm higher (equiv slot))=
      Sum.elim (fun _ : selected => primary) (pendingOtherKernelForms primary body pendingForm state point) :=
    pendingHigherKernelForms_reindex C n beta operator charts primary body pendingForm state point selected
  rw [hf,hk] at he
  exact he.symm

end
end AFT.V7Calibration
