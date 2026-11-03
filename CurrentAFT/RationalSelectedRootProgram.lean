import CurrentAFT.RationalCoefficientExtraction

/-! # Actual root-retained selected coefficient entries

The mass input is now the computed complete four-endpoint experiment,
including its common scalar. The entry error has no supplied physical
mass or operator estimate: it follows from the current proposal tables.
-/
namespace CurrentAFT.RationalSelectedRootProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def current (security bits : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (score : ℕ → ℚ) (selected : Finset (Fin 4)) (output : Fin selected.card → ℕ) : ℚ :=
  RationalCoefficientExtraction.selectedKernel security bits
    (RationalRootMassProgram.primaryMass security bits compensatorRoot attachmentRoot score) selected output

noncomputable section
open scoped Classical
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSubtypeDecidableEq {Index : Type*} (selected : Finset Index) : DecidableEq selected := Classical.decEq _
attribute [local irreducible] Parameters.base primaryLaw

theorem normalizedError_smul (security degree : ℕ) (massBound massError scalar : ℝ) :
    RationalCoefficientExtraction.normalizedError security degree (massBound * scalar) (massError * scalar) =
      RationalCoefficientExtraction.normalizedError security degree massBound massError * scalar := by
  unfold RationalCoefficientExtraction.normalizedError RationalCoefficientExtraction.extractionBound
    RationalCoefficientExtraction.extractionError
  ring

def errorConstant (security degree : ℕ) : ℝ :=
  RationalCoefficientExtraction.normalizedError security degree (2 * (Parameters.modulus security : ℝ)^2)
    (RationalRootMassProgram.primaryMassErrorConstant security)

theorem errorConstant_nonneg (security degree : ℕ) : 0 ≤ errorConstant security degree := by
  unfold errorConstant RationalCoefficientExtraction.normalizedError RationalCoefficientExtraction.extractionBound
    RationalCoefficientExtraction.extractionError RationalCoefficientExtraction.atomErrorConstant
    RationalRootMassProgram.primaryMassErrorConstant RationalRootMassProgram.fixedErrorConstant
    RationalRootMassProgram.weightedErrorConstant RationalRootMassProgram.primaryErrorConstant
    RationalTensorInverseProgram.tensorErrorConstant
  positivity [RationalTensorInverseProgram.actualBound_nonneg security,
    RationalTensorInverseProgram.errorConstant_nonneg security, RationalTensorInverseProgram.factorBound_one_le security]

/-- The literal rational algorithm computes the original local canonical
coefficient at every retained joint palette point. -/
theorem current_error (security bits : ℕ) (roots : RootTaggedSelected.RootPair security)
    (score : ℕ → ℚ) (selected : Finset (Fin 4)) (bound : ℝ) (hb : 0 ≤ bound)
    (hscore : ∀ color : Palette security, |(score color.val : ℝ)| ≤ bound)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (output : Fin selected.card → Palette security) (body : Fin 0 → SafePalette security) :
    |(current security bits roots.1.val roots.2.val score selected (fun index => (output index).val) : ℝ) -
      (LocalCoefficientFamily.selectedKernel security selected.card
        (RootMassColumns.primaryMassAt security roots (fun color => (score color.val : ℝ))) selected (by simp)).val output body| ≤
      errorConstant security selected.card * bound * (1 / (2 : ℝ)^bits) := by
  have hmassError : 0 ≤ RationalRootMassProgram.primaryMassErrorConstant security := by
    unfold RationalRootMassProgram.primaryMassErrorConstant RationalRootMassProgram.fixedErrorConstant
      RationalRootMassProgram.weightedErrorConstant RationalRootMassProgram.primaryErrorConstant
    positivity
  have h := RationalCoefficientExtraction.selectedKernel_error security bits
    (RationalRootMassProgram.primaryMass security bits roots.1.val roots.2.val score)
    (RootMassColumns.primaryMassAt security roots (fun color => (score color.val : ℝ))) selected
    ((2 * (Parameters.modulus security : ℝ)^2) * bound)
    (RationalRootMassProgram.primaryMassErrorConstant security * bound) (by positivity) (by positivity)
    (fun word => RationalRootMassProgram.primaryMassAt_bound security roots _ bound hb hscore word)
    (fun word => RationalRootMassProgram.primaryMass_error security bits roots score bound hb hscore hprecision hbudget word)
    hfirst hprecision hbudget output body
  rw [normalizedError_smul] at h
  exact h

end
end CurrentAFT.RationalSelectedRootProgram
