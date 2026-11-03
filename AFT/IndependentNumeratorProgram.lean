import AFT.PendingHigherSemantics
import AFT.OrderedExpansionSimulation

/-! # The executable independent numerator denotes its exact literal table -/
namespace AFT.RationalNumerics
open RepresentedPolynomial V7Calibration GaussianSource
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance independentNumeratorProgramFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

/-- There is no comparison or enumeration of real kernels in this program.
The fixed stored numbering and eleven numeric output masks reproduce the
original old-coordinate-only numerator exactly. -/
theorem independentNumeratorFactors_interpret {Leaf : Type*} {bound : ℕ} (numbering : FixedOrderNumberingCode bound)
    (hnumbering : ∀ order point mask slot,numbering.primaryLookup order point mask slot=pendingNumberingMeaning order point mask slot)
    (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (decode : Leaf → InputSeed (Fin (Parameters.modulus n))) (leafShape : Leaf → KernelShape)
    (hshape : ∀ leaf,(decode leaf).primaryOrder=(leafShape leaf).primary ∧ (decode leaf).bodyOrder=(leafShape leaf).body)
    (code : PendingKernelCode Leaf) (hc : code.Valid bound leafShape)
    (hbound : 4*(code.shape leafShape).primary≤bound) :
    (independentNumeratorFactors numbering leafShape code).interpret
      (PendingKernelCode.denote C n beta operator charts decode)=
      independentNumeratorTable C n beta operator charts (code.denote C n beta operator charts decode) := by
  unfold independentNumeratorFactors
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
      have hh := pendingProgramChoices_denote C n beta operator charts decode leafShape hshape state hs
      rw [show (@Finset.decidableEq (Fin 4) (pendingStateSemanticsFinDecEq 4))=Classical.decEq (Finset (Fin 4)) from Subsingleton.elim _ _] at hh
      exact hh)
    (fun state hs mask _ => ⟨pendingProgramHigher_valid numbering hnumbering hs mask,
      pendingProgramHigher_denote numbering hnumbering C n beta operator charts decode leafShape hshape state hs mask⟩)
    (code.shape leafShape).primary (initialPendingProgramState leafShape code)
    (initialPendingProgramState_valid leafShape code hc hbound)
  rw [initialPendingProgramState_denote C n beta operator charts decode leafShape hshape] at hh
  rw [independentNumeratorTable,(code.denote_shape C n beta operator charts decode leafShape hshape).1]
  exact hh

end
end AFT.RationalNumerics
