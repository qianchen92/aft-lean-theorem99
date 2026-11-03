import AFT.MarkedOutput

/-! # The uncompromised integer root channel of a reserved compensator -/

namespace AFT.V7Calibration

open GaussianSource
open scoped BigOperators Classical

noncomputable section

/-- A reserved compensator receives the actual root marginal, without an
attachment or queue shift. Its output is an integer translate. -/
def rootCompensatorChannel (parameter : ℕ) (center output : Fin (Parameters.modulus parameter)) : ℝ :=
  ∑ root : Window (v7RootCutoff parameter),
    (rootMarginal (v7RootWidth parameter) (v7RootCutoff parameter) (Parameters.bodies parameter)
      (Parameters.bodies_positive parameter)).weight root *
      if (output.val : ℤ) = (center.val : ℤ) + root then 1 else 0

theorem rootCompensatorChannel_profile (parameter : ℕ)
    (profile : Fin (Parameters.modulus parameter) → ℝ) (output : Fin (Parameters.modulus parameter)) :
    (∑ center, profile center * rootCompensatorChannel parameter center output) =
      rootProfileOperator parameter profile output := by
  change (∑ center, profile center * ∑ root : Window (v7RootCutoff parameter),
    (rootMarginal (v7RootWidth parameter) (v7RootCutoff parameter) (Parameters.bodies parameter)
      (Parameters.bodies_positive parameter)).weight root *
      if (output.val : ℤ) = (center.val : ℤ) + root then 1 else 0) = _
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  change (∑ root : Window (v7RootCutoff parameter), ∑ center, _) =
    ∑ root : Window (v7RootCutoff parameter),
      (rootMarginal (v7RootWidth parameter) (v7RootCutoff parameter) (Parameters.bodies parameter)
        (Parameters.bodies_positive parameter)).weight root * integerShiftProfile parameter profile root output
  simp only [integerShiftProfile, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro root _
  apply Finset.sum_congr rfl
  intro center _
  split_ifs <;> ring

/-- The actual compensation of a public anchor is its root-only blur. -/
theorem rootCompensatorChannel_anchor (parameter : ℕ) (color output : Fin (Parameters.modulus parameter)) :
    (∑ center, publicAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter) color center.val *
      rootCompensatorChannel parameter center output) =
    blurredAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
      (fun root : Window (v7RootCutoff parameter) => (root : ℤ))
      (rootMarginal (v7RootWidth parameter) (v7RootCutoff parameter) (Parameters.bodies parameter)
        (Parameters.bodies_positive parameter)) color output.val := by
  rw [rootCompensatorChannel_profile]
  apply rootProfileOperator_function
  intro z hz
  have hw : Parameters.anchorWidth parameter ≠ 0 := by
    unfold Parameters.anchorWidth
    exact pow_ne_zero _ (by have := Parameters.security_ge_two parameter; omega)
  have hh := (publicAnchorKernel_safe_mass (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
    (Parameters.safeMargin parameter) 0 hw (Parameters.anchor_clearance parameter) (by positivity)
    (by simpa only [abs_zero, add_zero] using (show (Parameters.safeMargin parameter : ℤ) ≤ Parameters.anchorWidth parameter by exact_mod_cast safeMargin_le_anchor parameter)) color).2 z (by omega)
  convert hh using 1
  congr 1
  omega

theorem rootCompensatorChannel_anchorProfile (parameter : ℕ)
    (profile : Fin (Parameters.modulus parameter) → ℝ) (output : Fin (Parameters.modulus parameter)) :
    (∑ center, applyAnchor (fun color position => publicAnchorKernel (Parameters.modulus parameter)
        (Parameters.anchorWidth parameter) color position.val) profile center *
      rootCompensatorChannel parameter center output) =
    blurredAnchorMean (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
      (fun root : Window (v7RootCutoff parameter) => (root : ℤ))
      (rootMarginal (v7RootWidth parameter) (v7RootCutoff parameter) (Parameters.bodies parameter)
        (Parameters.bodies_positive parameter)) profile output.val := by
  simp only [applyAnchor, Finset.sum_mul]
  rw [Finset.sum_comm]
  unfold blurredAnchorMean
  apply Finset.sum_congr rfl
  intro color _
  rw [← rootCompensatorChannel_anchor]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro center _
  ring

end
end AFT.V7Calibration
