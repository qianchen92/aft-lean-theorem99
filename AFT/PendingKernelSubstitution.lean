import AFT.PendingSubsetExpansion
import AFT.PendingKernelForms
import AFT.KernelPolynomialSubstitution

/-! # The actual independent numerator is an input-form substitution -/
namespace AFT.V7Calibration
open GaussianSource RepresentedPolynomial
open MixedKernel
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
local instance pendingKernelSubstitutionFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance pendingKernelSubstitutionUnitDecEq : DecidableEq Unit := Classical.decEq _
local instance pendingKernelSubstitutionSelectedDecEq (s : Finset (Fin 4)) : DecidableEq s := Classical.decEq _
variable {Output : Type*}
variable (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)

def independentInverseColumnForm (primary : Fin (Parameters.modulus n) → Table Output)
    (selected : Finset (Fin 4)) (color : Fin (Parameters.modulus n)) : Table Output :=
  kernelPolynomial (fun _ : selected => primary) (independentInverseColumn C n beta operator charts selected color)

def independentInputForm (primary : Fin (Parameters.modulus n) → Table Output)
    (color : Fin (Parameters.modulus n)) : Table Output :=
  primary color+∑ selected∈(Finset.univ : Finset (Finset (Fin 4))).filter (fun selected => 2≤selected.card),
    independentInverseColumnForm C n beta operator charts primary selected color

variable {Rest : Type} [Fintype Rest] [DecidableEq Rest]

theorem independentJointInverse_kernelPolynomial
    (primary : Fin (Parameters.modulus n) → Table Output)
    (other : Rest → FiniteDist (Fin (Parameters.modulus n)))
    (forms : Rest → Fin (Parameters.modulus n) → Table Output)
    (kernel : Fin (Parameters.modulus n) → (Rest → Fin (Parameters.modulus n)) → ℝ)
    (selected : Finset (Fin 4)) :
    kernelPolynomial (Sum.elim (fun _ : selected => primary) forms)
      (independentJointInverse C n beta operator charts other selected kernel)=
      kernelPolynomial (Sum.elim (fun _ : Unit => independentInverseColumnForm C n beta operator charts primary selected) forms)
        (singletonJoin kernel) := by
  have hk : independentJointInverse C n beta operator charts other selected kernel=
      fun word => ∑ color,kernel color (fun slot => word (Sum.inr slot))*
        independentInverseColumn C n beta operator charts selected color (fun slot => word (Sum.inl slot)) := by
    funext word
    have he : word=Sum.elim (fun slot => word (Sum.inl slot)) (fun slot => word (Sum.inr slot)) := by
      funext slot;cases slot <;> rfl
    conv_lhs => rw [he]
    exact independentJointInverse_columns C n beta operator charts other selected kernel _ _
  rw [hk]
  exact kernelPolynomial_column_substitution (fun _ : selected => primary) forms kernel
    (independentInverseColumn C n beta operator charts selected)

omit [Fintype Rest] [DecidableEq Rest] in
theorem pendingKernel_step
    (primary body : Fin (Parameters.modulus n) → Table Output)
    (state : PendingInput (Fin (Parameters.modulus n))) (point : Fin state.seed.primaryOrder) (hp : point∈state.pending) :
    pendingKernelPolynomial primary body (independentInputForm C n beta operator charts primary) ⟨state.seed,state.pending.erase point⟩+
      (∑ selected∈(Finset.univ : Finset (Finset (Fin 4))).filter (fun selected => 2≤selected.card),
        pendingKernelPolynomial primary body (independentInputForm C n beta operator charts primary)
          (pendingHigherState C n beta operator charts state point selected))=
      pendingKernelPolynomial primary body (independentInputForm C n beta operator charts primary) state := by
  rw [pendingErasedKernelPolynomial_split,pendingKernelPolynomial_split primary body _ state point hp]
  simp_rw [pendingHigherKernelPolynomial_reindex,independentJointInverse_kernelPolynomial]
  unfold independentInputForm
  rw [kernelPolynomial_singleton_add,kernelPolynomial_singleton_sum]

omit [Fintype Rest] [DecidableEq Rest] in
/-- This exact identity is valid for every input kernel, including arbitrary
joint primary/body fibers. The two roles may use different indeterminates. -/
theorem pendingNumeratorTable_kernelPolynomial
    (primary body : Fin (Parameters.modulus n) → Table Output)
    (state : PendingInput (Fin (Parameters.modulus n))) :
    inputKernelPolynomialHom primary body (pendingNumeratorTable C n beta operator charts state)=
      pendingKernelPolynomial primary body (independentInputForm C n beta operator charts primary) state := by
  have hrec (steps : ℕ) : ∀ state : PendingInput (Fin (Parameters.modulus n)),state.pending.card≤steps →
      inputKernelPolynomialHom primary body
        (seedExpansion PendingInput.seed pendingLinearState pendingHigherChoices
          (pendingNonlinearState C n beta operator charts) steps state)=
        pendingKernelPolynomial primary body (independentInputForm C n beta operator charts primary) state := by
    induction steps with
    | zero =>
      intro state hcard
      have he : state.pending=∅ := Finset.card_eq_zero.mp (by omega)
      exact (inputKernelPolynomialHom_X _ _ _).trans (pendingKernelPolynomial_empty _ _ _ state he).symm
    | succ steps ih =>
      intro state hcard
      by_cases hn : state.pending.Nonempty
      · have hp : state.pending.min' hn∈state.pending := Finset.min'_mem _ _
        rw [seedExpansion,map_add,map_sum]
        rw [ih (pendingLinearState state) (by have hh := pendingLinearState_card state hn;omega)]
        have hnon (selected) : pendingNonlinearState C n beta operator charts state selected=
            pendingHigherState C n beta operator charts state (state.pending.min' hn) selected := by
          unfold pendingNonlinearState
          exact dif_pos hn
        have hsum : (∑ selected∈pendingHigherChoices state,
            inputKernelPolynomialHom primary body
              (seedExpansion PendingInput.seed pendingLinearState pendingHigherChoices
                (pendingNonlinearState C n beta operator charts) steps
                  (pendingNonlinearState C n beta operator charts state selected)))=
            ∑ selected∈pendingHigherChoices state,
              pendingKernelPolynomial primary body (independentInputForm C n beta operator charts primary)
                (pendingNonlinearState C n beta operator charts state selected) := by
          apply Finset.sum_congr rfl
          intro selected _
          apply ih
          rw [hnon]
          have hh := pendingHigherState_card C n beta operator charts state (state.pending.min' hn) hp selected
          omega
        rw [hsum]
        simpa only [pendingLinearState,dif_pos hn,pendingHigherChoices,if_pos hn,pendingNonlinearState] using
          pendingKernel_step C n beta operator charts primary body state (state.pending.min' hn) hp
      · have he : state.pending=∅ := Finset.not_nonempty_iff_eq_empty.mp hn
        simp only [seedExpansion,pendingLinearState,dif_neg hn,pendingHigherChoices,if_neg hn,
          Finset.sum_empty,add_zero]
        exact ih state (by simp [he])
  exact hrec state.pending.card state le_rfl

omit [Fintype Rest] [DecidableEq Rest] in
theorem independentNumeratorTable_kernelPolynomial
    (primary body : Fin (Parameters.modulus n) → Table Output)
    (seed : InputSeed (Fin (Parameters.modulus n))) :
    inputKernelPolynomialHom primary body (independentNumeratorTable C n beta operator charts seed)=
      inputKernelPolynomial (independentInputForm C n beta operator charts primary) body seed := by
  have he := pendingNumeratorTable_kernelPolynomial C n beta operator charts primary body (initialPendingInput seed)
  have hf : pendingKernelForms primary body (independentInputForm C n beta operator charts primary)
      (initialPendingInput seed)=Fin.addCases (fun _ => independentInputForm C n beta operator charts primary) (fun _ => body) := by
    funext slot
    cases slot using Fin.addCases <;> simp [pendingKernelForms,initialPendingInput]
  unfold pendingKernelPolynomial at he
  rw [hf] at he
  simpa only [pendingNumeratorTable,initialPendingInput,Finset.card_univ,Fintype.card_fin,
    independentNumeratorTable,inputKernelPolynomial] using he

omit [Fintype Rest] [DecidableEq Rest] in
/-- Reordering primary/body inputs does not change the entire independent
numerator under any role-aware polynomial probe. -/
theorem independentNumeratorTable_role_equiv
    (primary body : Fin (Parameters.modulus n) → Table Output)
    {first second : InputSeed (Fin (Parameters.modulus n))} (equiv : SeedRoleEquiv first second) :
    inputKernelPolynomialHom primary body (independentNumeratorTable C n beta operator charts first)=
      inputKernelPolynomialHom primary body (independentNumeratorTable C n beta operator charts second) := by
  rw [independentNumeratorTable_kernelPolynomial,independentNumeratorTable_kernelPolynomial]
  exact equiv.inputKernelPolynomial _ _

end
end AFT.V7Calibration
