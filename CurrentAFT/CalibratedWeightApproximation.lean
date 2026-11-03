import CurrentAFT.NumericalWeightEvaluation
import CurrentAFT.CalibrationMatrixApproximation

/-! # From rational full-response iteration to the actual calibrated weight

The table error and the true coefficient bound are derived from the
established complete-response stability. The remaining matrix-entry premise
is explicitly a numerical evaluator obligation, not transport accuracy.
-/
namespace CurrentAFT.CalibratedWeightApproximation
open AFT ActualControls ProposalPrimary ControlCoordinates GradedControlAlgebra
  CalibrationPointCoordinates CalibrationTableNorm CalibrationMatrixApproximation
  ActualCompleteStability NumericalWeightEvaluation ControlProduct BackgroundRates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
local instance calibrationFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

def pointBudget (security order steps : ℕ) (entryError : ℝ) : ℝ :=
  (1 + encodeFactor security order) *
    (2 * (3 / 4 : ℝ)^steps + 8 * perturbationFactor security order * entryError)

def weightBudget (security bits order steps : ℕ) (entryError : ℝ) : ℝ :=
  pointBudget security order steps entryError + (Fintype.card (PositiveArity order) : ℝ) *
    (factor security^order * (pointBudget security order steps entryError +
      order * localError security bits * (2 * encodeFactor security order)))

theorem pointBudget_nonneg (security order steps : ℕ) (entryError : ℝ) (he : 0 ≤ entryError) :
    0 ≤ pointBudget security order steps entryError := by
  unfold pointBudget encodeFactor
  positivity [perturbationFactor_nonneg security order]

theorem iteration_point_error (security order : ℕ) (horder : 2 ≤ order)
    (hsecurity : threshold order horder ≤ security)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (matrix : Index security order → Index security order → ℚ)
    (entryError : ℝ) (he : 0 ≤ entryError)
    (hentries : ∀ output input, |(matrix output input : ℝ) -
      LinearMap.toMatrix' (exactDefect security order horder hsecurity layout) output input| ≤ entryError)
    (hsmall : perturbationFactor security order * entryError ≤ 1 / 4)
    (steps : ℕ) (point : Index security order) :
    |(RationalNumerics.linearIteration matrix (rhs security order) steps point : ℝ) -
      encodeCurrent security order (solution security order horder hsecurity layout) point| ≤
        pointBudget security order steps entryError := by
  let difference : Table security order :=
    (fun point => (RationalNumerics.linearIteration matrix (rhs security order) steps point : ℝ)) -
      encodeCurrent security order (solution security order horder hsecurity layout)
  have hi := rational_iteration_measure_error security order horder hsecurity layout matrix entryError he hentries hsmall steps
  have hc := coordinate_le_measure security order difference
  have hp : |difference point| ≤ ‖difference‖ := norm_le_pi_norm difference point
  apply hp.trans (hc.trans ?_)
  exact mul_le_mul_of_nonneg_left hi (by unfold encodeFactor; positivity)

theorem solution_point_bound (security order : ℕ) (horder : 2 ≤ order)
    (hsecurity : threshold order horder ≤ security)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (point : Index security order) :
    |encodeCurrent security order (solution security order horder hsecurity layout) point| ≤
      2 * encodeFactor security order := by
  have h := encode_norm security order (solution security order horder hsecurity layout)
  have hp : |encodeCurrent security order (solution security order horder hsecurity layout) point| ≤
      ‖encodeCurrent security order (solution security order horder hsecurity layout)‖ := by
    simpa only [Real.norm_eq_abs] using
      norm_le_pi_norm (encodeCurrent security order (solution security order horder hsecurity layout)) point
  have hn := mul_le_mul_of_nonneg_left (solution_norm security order horder hsecurity layout)
    (show 0 ≤ encodeFactor security order by unfold encodeFactor; positivity)
  exact hp.trans (h.trans (hn.trans_eq (mul_comm _ _)))

theorem iteration_weight_error (security bits order : ℕ) (horder : 2 ≤ order)
    (hsecurity : threshold order horder ≤ security)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (matrix : Index security order → Index security order → ℚ)
    (entryError : ℝ) (he : 0 ≤ entryError)
    (hentries : ∀ output input, |(matrix output input : ℝ) -
      LinearMap.toMatrix' (exactDefect security order horder hsecurity layout) output input| ≤ entryError)
    (hsmall : perturbationFactor security order * entryError ≤ 1 / 4) (steps : ℕ)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤
      1/(4*(Parameters.modulus security:ℝ)))
    (groups : Fin (Parameters.legCount security) → SafeControlGroups.SafeGroup security)
    (centers : Fin (ordinaryPool security) → SafePalette security) :
    |evaluate security bits order (Parameters.legCount security) (ordinaryPool security)
        (fun point => (RationalNumerics.linearIteration matrix (rhs security order) steps point : ℝ)) groups centers -
      publicWeight security order horder hsecurity layout
        (fun index => SafeControlGroups.unwrap security (groups index)) centers| ≤
      weightBudget security bits order steps entryError := by
  exact evaluate_error security bits order (Parameters.legCount security) (ordinaryPool security)
    (solution security order horder hsecurity layout) _
    (2 * encodeFactor security order) (pointBudget security order steps entryError)
    (by unfold encodeFactor; positivity) (pointBudget_nonneg security order steps entryError he)
    (solution_point_bound security order horder hsecurity layout)
    (iteration_point_error security order horder hsecurity layout matrix entryError he hentries hsmall steps)
    hprecision hbudget groups centers

end
end CurrentAFT.CalibratedWeightApproximation
