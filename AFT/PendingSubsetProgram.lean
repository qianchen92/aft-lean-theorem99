import AFT.IndependentNumeratorProgram
import AFT.PendingSubsetExpansion

/-! # Executable replacement of an arbitrary specified old-input subset -/
namespace AFT.RationalNumerics

def pendingSubsetFactors {Leaf : Type*} {bound : ℕ} (numbering : FixedOrderNumberingCode bound)
    (leafShape : Leaf → KernelShape) (state : PendingProgramState Leaf) : OrderedSeedTable (PendingKernelCode Leaf) :=
  orderedSeedExpansion PendingProgramState.kernel pendingProgramLinear pendingProgramChoices
    (pendingProgramHigher numbering leafShape) state.pending.card state

theorem pendingSubsetFactors_length {Leaf : Type*} {bound : ℕ} (numbering : FixedOrderNumberingCode bound)
    (leafShape : Leaf → KernelShape) (state : PendingProgramState Leaf) :
    (pendingSubsetFactors numbering leafShape state).length≤12^state.pending.card := by
  apply orderedSeedExpansion_length _ _ _ _ 11
  intro state
  unfold pendingProgramChoices
  split_ifs <;> simp only [pendingHigherMasks_length,List.length_nil,le_refl,Nat.zero_le]

noncomputable section
open RepresentedPolynomial V7Calibration GaussianSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false

/-- New coordinates may already be present in the initial joint kernel.
Only the explicitly stored pending subset is replaced. -/
theorem pendingSubsetFactors_interpret {Leaf : Type*} {bound : ℕ} (numbering : FixedOrderNumberingCode bound)
    (hnumbering : ∀ order point mask slot,numbering.primaryLookup order point mask slot=pendingNumberingMeaning order point mask slot)
    (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (decode : Leaf → InputSeed (Fin (Parameters.modulus n))) (leafShape : Leaf → KernelShape)
    (hshape : ∀ leaf,(decode leaf).primaryOrder=(leafShape leaf).primary ∧ (decode leaf).bodyOrder=(leafShape leaf).body)
    (state : PendingProgramState Leaf) (hs : state.Valid bound leafShape) :
    (pendingSubsetFactors numbering leafShape state).interpret
      (PendingKernelCode.denote C n beta operator charts decode)=
      pendingNumeratorTable C n beta operator charts (state.denote C n beta operator charts decode) := by
  unfold pendingSubsetFactors
  have hh := orderedSeedExpansion_simulation
    (PendingKernelCode.denote C n beta operator charts decode)
    (PendingProgramState.denote C n beta operator charts decode) pendingMask
    PendingProgramState.kernel pendingProgramLinear pendingProgramChoices
    (pendingProgramHigher numbering leafShape)
    PendingInput.seed pendingLinearState pendingHigherChoices
    (pendingNonlinearState C n beta operator charts)
    (PendingProgramState.Valid bound leafShape)
    (fun _ _ => rfl)
    (fun state hs => ⟨pendingProgramLinear_valid hs,
      pendingProgramLinear_denote C n beta operator charts decode leafShape hshape state hs⟩)
    (fun state hs => by
      have hc := pendingProgramChoices_denote C n beta operator charts decode leafShape hshape state hs
      rw [show (@Finset.decidableEq (Fin 4) (pendingStateSemanticsFinDecEq 4))=Classical.decEq (Finset (Fin 4)) from Subsingleton.elim _ _] at hc
      exact hc)
    (fun state hs mask _ => ⟨pendingProgramHigher_valid numbering hnumbering hs mask,
      pendingProgramHigher_denote numbering hnumbering C n beta operator charts decode leafShape hshape state hs mask⟩)
    state.pending.card state hs
  have hcard := congrArg Finset.card (state.denote_natural C n beta operator charts decode leafShape hshape hs)
  rw [Finset.card_image_of_injective _ Fin.val_injective] at hcard
  rw [pendingNumeratorTable,hcard]
  exact hh

end
end AFT.RationalNumerics
