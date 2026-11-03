import CurrentAFT.CalibrationTableNorm

/-! # Stability of rational approximations to the actual calibration matrix

Entrywise approximation is measured against the concrete full response.
The required tolerance and all conversion factors are explicit functions of
the actual finite coordinates, rather than assumed operator norm bounds.
-/
namespace CurrentAFT.CalibrationMatrixApproximation
open AFT ActualControls ProposalPrimary LocalCoefficientFamily BackgroundRates
  CalibrationPointCoordinates CalibrationCoordinateError CalibrationTableNorm
  ActualCompleteStability
open GradedControlAlgebra ControlProduct
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
local instance matrixFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

theorem rational_matrix_difference_norm {State : Type*} [Fintype State] [DecidableEq State]
    (operator : Module.End ℝ (State → ℝ)) (matrix : State → State → ℚ)
    (error : ℝ) (herror : 0 ≤ error)
    (hentries : ∀ output input, |(matrix output input : ℝ) - LinearMap.toMatrix' operator output input| ≤ error)
    (table : State → ℝ) :
    ‖RationalNumerics.realMatrixOperator matrix table - operator table‖ ≤
      Fintype.card State * error * ‖table‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro output
  have he : (RationalNumerics.realMatrixOperator matrix table - operator table) output =
      ∑ input, ((matrix output input : ℝ) - LinearMap.toMatrix' operator output input) * table input := by
    rw [← LinearMap.toMatrix'_mulVec operator table]
    simp only [Pi.sub_apply, RationalNumerics.realMatrixOperator, LinearMap.coe_mk, AddHom.coe_mk,
      Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib]
  rw [he, Real.norm_eq_abs]
  calc
    _ ≤ ∑ input, |((matrix output input : ℝ) - LinearMap.toMatrix' operator output input) * table input| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _input : State, error * ‖table‖ := by
      apply Finset.sum_le_sum
      intro input _
      rw [abs_mul]
      exact mul_le_mul (hentries output input) (norm_le_pi_norm table input) (abs_nonneg _) herror
    _ = _ := by simp [mul_assoc]

def perturbationFactor (security order : ℕ) : ℝ :=
  comparisonFactor security order * Fintype.card (Index security order) * (1 + encodeFactor security order)

theorem comparisonFactor_nonneg (security order : ℕ) : 0 ≤ comparisonFactor security order := by
  unfold comparisonFactor encodeFactor decodeFactor
  positivity

theorem perturbationFactor_nonneg (security order : ℕ) : 0 ≤ perturbationFactor security order := by
  unfold perturbationFactor
  exact mul_nonneg (mul_nonneg (comparisonFactor_nonneg security order) (Nat.cast_nonneg _))
    (by unfold encodeFactor; positivity)

theorem perturbation_bound (security order : ℕ) (horder : 2 ≤ order)
    (hsecurity : threshold order horder ≤ security)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (matrix : Index security order → Index security order → ℚ)
    (error : ℝ) (herror : 0 ≤ error)
    (hentries : ∀ output input, |(matrix output input : ℝ) -
      LinearMap.toMatrix' (exactDefect security order horder hsecurity layout) output input| ≤ error)
    (table : Table security order) :
    measure security order (RationalNumerics.realMatrixOperator matrix table -
      exactDefect security order horder hsecurity layout table) ≤
        perturbationFactor security order * error * measure security order table := by
  have hc := measure_le_coordinate security order
    (RationalNumerics.realMatrixOperator matrix table - exactDefect security order horder hsecurity layout table)
  have hm := rational_matrix_difference_norm _ matrix error herror hentries table
  have he := coordinate_le_measure security order table
  calc
    _ ≤ comparisonFactor security order * ‖RationalNumerics.realMatrixOperator matrix table -
        exactDefect security order horder hsecurity layout table‖ := hc
    _ ≤ comparisonFactor security order * (Fintype.card (Index security order) * error * ‖table‖) :=
      mul_le_mul_of_nonneg_left hm (comparisonFactor_nonneg security order)
    _ ≤ comparisonFactor security order *
        (Fintype.card (Index security order) * error *
          ((1 + encodeFactor security order) * measure security order table)) := by
      apply mul_le_mul_of_nonneg_left _ (comparisonFactor_nonneg security order)
      exact mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by unfold perturbationFactor; ring

theorem rational_contracts (security order : ℕ) (horder : 2 ≤ order)
    (hsecurity : threshold order horder ≤ security)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (matrix : Index security order → Index security order → ℚ)
    (error : ℝ) (herror : 0 ≤ error)
    (hentries : ∀ output input, |(matrix output input : ℝ) -
      LinearMap.toMatrix' (exactDefect security order horder hsecurity layout) output input| ≤ error)
    (hsmall : perturbationFactor security order * error ≤ 1 / 4) (table : Table security order) :
    measure security order (RationalNumerics.realMatrixOperator matrix table) ≤
      (3 / 4 : ℝ) * measure security order table := by
  have htriangle := measure_add security order
    (exactDefect security order horder hsecurity layout table)
    (RationalNumerics.realMatrixOperator matrix table - exactDefect security order horder hsecurity layout table)
  have he : exactDefect security order horder hsecurity layout table +
      (RationalNumerics.realMatrixOperator matrix table - exactDefect security order horder hsecurity layout table) =
      RationalNumerics.realMatrixOperator matrix table := by abel
  rw [he] at htriangle
  have hp := perturbation_bound security order horder hsecurity layout matrix error herror hentries table
  have hc := exactDefect_contracts security order horder hsecurity layout table
  have hs := mul_le_mul_of_nonneg_right hsmall (measure_nonneg security order table)
  nlinarith only [htriangle, hp, hc, hs]

theorem iteration_error (security order : ℕ) (operator : Module.End ℝ (Table security order))
    (rhs target : Table security order) (error : ℝ) (herror : 0 ≤ error)
    (hcontract : ∀ table, measure security order (operator table) ≤ (3 / 4 : ℝ) * measure security order table)
    (hresidual : measure security order (rhs - operator target - target) ≤ error) (steps : ℕ) :
    measure security order (RationalNumerics.realLinearIteration operator rhs steps - target) ≤
      (3 / 4 : ℝ)^steps * measure security order target + 4 * error := by
  induction steps with
  | zero =>
      simp only [RationalNumerics.realLinearIteration, zero_sub, measure_neg, pow_zero, one_mul]
      linarith
  | succ steps ih =>
      have he : RationalNumerics.realLinearIteration operator rhs (steps + 1) - target =
          (rhs - operator target - target) + -(operator (RationalNumerics.realLinearIteration operator rhs steps - target)) := by
        simp only [RationalNumerics.realLinearIteration, map_sub]
        abel
      rw [he]
      apply (measure_add security order _ _).trans
      rw [measure_neg]
      apply (add_le_add hresidual (hcontract _)).trans
      have hi := mul_le_mul_of_nonneg_left ih (show (0 : ℝ) ≤ 3 / 4 by norm_num)
      rw [pow_succ]
      linarith

def rhs (security order : ℕ) (point : Index security order) : ℚ :=
  if point.1 = zeroArity order then 1 else 0

theorem rhs_cast (security order : ℕ) :
    (fun point => (rhs security order point : ℝ)) = encodeCurrent security order 1 := by
  funext point
  rcases point with ⟨arity, colors, centers⟩
  simp only [rhs, apply_ite, Rat.cast_one, Rat.cast_zero]
  change (if arity = zeroArity order then (1 : ℝ) else 0) =
    ((familyUnit (primaryLaw security) (bodyReference security) order) arity).val colors centers
  by_cases hequal : arity = zeroArity order
  · subst arity
    simp only [familyUnit, Pi.single_eq_same, if_true, scalarUnit]
  · simp only [hequal, if_false, familyUnit, Pi.single_eq_of_ne hequal, Submodule.coe_zero, Pi.zero_apply]

/-- The real cast of the genuine rational iteration converges to the
actual complete calibration solution, with explicit entry-error loss. -/
theorem rational_iteration_measure_error (security order : ℕ) (horder : 2 ≤ order)
    (hsecurity : threshold order horder ≤ security)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (matrix : Index security order → Index security order → ℚ)
    (error : ℝ) (herror : 0 ≤ error)
    (hentries : ∀ output input, |(matrix output input : ℝ) -
      LinearMap.toMatrix' (exactDefect security order horder hsecurity layout) output input| ≤ error)
    (hsmall : perturbationFactor security order * error ≤ 1 / 4) (steps : ℕ) :
    measure security order ((fun point =>
        (RationalNumerics.linearIteration matrix (rhs security order) steps point : ℝ)) -
          encodeCurrent security order (solution security order horder hsecurity layout)) ≤
      2 * (3 / 4 : ℝ)^steps + 8 * perturbationFactor security order * error := by
  let target := encodeCurrent security order (solution security order horder hsecurity layout)
  have ht : measure security order target ≤ 2 := by
    rw [measure_encode]
    exact solution_norm security order horder hsecurity layout
  have hresidual : measure security order (encodeCurrent security order 1 -
      RationalNumerics.realMatrixOperator matrix target - target) ≤
        2 * perturbationFactor security order * error := by
    have he : encodeCurrent security order 1 - RationalNumerics.realMatrixOperator matrix target - target =
        -(RationalNumerics.realMatrixOperator matrix target -
          exactDefect security order horder hsecurity layout target) := by
      have hh := target_fixed security order horder hsecurity layout
      dsimp only [target]
      linear_combination hh
    rw [he, measure_neg]
    apply (perturbation_bound security order horder hsecurity layout matrix error herror hentries target).trans
    have hh := mul_le_mul_of_nonneg_left ht
      (mul_nonneg (perturbationFactor_nonneg security order) herror)
    nlinarith only [hh]
  have hi := iteration_error security order (RationalNumerics.realMatrixOperator matrix)
    (encodeCurrent security order 1) target (2 * perturbationFactor security order * error)
    (by positivity [perturbationFactor_nonneg security order])
    (rational_contracts security order horder hsecurity layout matrix error herror hentries hsmall) hresidual steps
  rw [← rhs_cast, ← RationalNumerics.linearIteration_cast] at hi
  have hm := mul_le_mul_of_nonneg_left ht (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4) steps)
  linarith

theorem rational_iteration_error (security order : ℕ) (horder : 2 ≤ order)
    (hsecurity : threshold order horder ≤ security)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (matrix : Index security order → Index security order → ℚ)
    (error : ℝ) (herror : 0 ≤ error)
    (hentries : ∀ output input, |(matrix output input : ℝ) -
      LinearMap.toMatrix' (exactDefect security order horder hsecurity layout) output input| ≤ error)
    (hsmall : perturbationFactor security order * error ≤ 1 / 4) (steps : ℕ) :
    LocalRaisingBounds.coefficientNorm security order
      (decodeCurrent security order (fun point =>
        (RationalNumerics.linearIteration matrix (rhs security order) steps point : ℝ)) -
          solution security order horder hsecurity layout) ≤
      2 * (3 / 4 : ℝ)^steps + 8 * perturbationFactor security order * error := by
  have h := rational_iteration_measure_error security order horder hsecurity layout matrix error herror hentries hsmall steps
  have hd := decode_encode_current security order (solution security order horder hsecurity layout)
  have hlower : LocalRaisingBounds.coefficientNorm security order
      (decodeCurrent security order (fun point =>
        (RationalNumerics.linearIteration matrix (rhs security order) steps point : ℝ)) -
          solution security order horder hsecurity layout) ≤
      measure security order ((fun point =>
        (RationalNumerics.linearIteration matrix (rhs security order) steps point : ℝ)) -
          encodeCurrent security order (solution security order horder hsecurity layout)) := by
    unfold CalibrationTableNorm.measure
    rw [map_sub, hd]
    exact le_add_of_nonneg_right (norm_nonneg _)
  exact hlower.trans h


end
end CurrentAFT.CalibrationMatrixApproximation
