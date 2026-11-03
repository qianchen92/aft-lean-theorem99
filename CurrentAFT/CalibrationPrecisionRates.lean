import CurrentAFT.CalibrationMatrixRates
import AFT.BetaTypical

/-! # Linear bit precision and iteration counts suffice at every fixed order

Polynomial losses in the true coordinate condition number are dominated by
precision `bits = security`. The calibration order is kept fixed throughout;
only the numerical precision and iteration count grow with security.
-/
namespace CurrentAFT.CalibrationPrecisionRates
open AFT CalibrationTableNorm CalibrationMatrixApproximation CalibrationMatrixRates
open Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base

theorem polynomial_geometric_negligible (constant : ℝ) (degree : ℕ) (ratio : ℝ)
    (hc : 0 ≤ constant) (hr : 0 < ratio) (hr1 : ratio < 1) :
    Negligible (fun security => constant * (Parameters.base security : ℝ)^degree * ratio^security) := by
  have hmain := (BetaReference.negligible_geometric_population (constant * 3^degree) ratio
    (by positivity) hr hr1 (fun security => security) (by filter_upwards [] with security; rfl)).mul_polynomial degree
  apply hmain.of_eventually_le
  filter_upwards [eventually_ge_atTop 1] with security hsecurity
  have hb : (Parameters.base security : ℝ) ≤ 3 * security := by
    exact_mod_cast (show Parameters.base security ≤ 3 * security by unfold Parameters.base; omega)
  have hp := pow_le_pow_left₀ (show (0 : ℝ) ≤ Parameters.base security by positivity) hb degree
  have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hc) (pow_nonneg hr.le security)
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  simpa only [mul_pow, mul_assoc, mul_comm, mul_left_comm] using hm

def entryBudget (constant : ℝ) (degree security : ℕ) : ℝ :=
  constant * (Parameters.base security : ℝ)^degree * (1 / 2 : ℝ)^security

theorem entryBudget_nonneg (constant : ℝ) (degree security : ℕ) (hc : 0 ≤ constant) :
    0 ≤ entryBudget constant degree security := by unfold entryBudget; positivity

theorem amplified_negligible (order : ℕ) (constant : ℝ) (degree : ℕ) (hc : 0 ≤ constant) :
    Negligible (fun security => perturbationFactor security order * entryBudget constant degree security) := by
  have hconstant : 0 ≤ perturbationConstant order := by
    unfold perturbationConstant comparisonConstant countConstant encodeConstant decodeConstant
    positivity
  have hmain := polynomial_geometric_negligible (perturbationConstant order * constant)
    (576 * order + degree) (1 / 2) (mul_nonneg hconstant hc) (by norm_num) (by norm_num)
  apply hmain.of_eventually_le
  filter_upwards [] with security
  have hp := perturbationFactor_bound security order
  have hb := entryBudget_nonneg constant degree security hc
  rw [abs_of_nonneg (mul_nonneg (perturbationFactor_nonneg security order) hb), abs_of_nonneg (by positivity)]
  apply (mul_le_mul_of_nonneg_right hp hb).trans_eq
  unfold entryBudget
  rw [pow_add]
  ring

def iterationBudget (order : ℕ) (constant : ℝ) (degree security : ℕ) : ℝ :=
  2 * (3 / 4 : ℝ)^security +
    8 * perturbationFactor security order * entryBudget constant degree security

theorem iterationBudget_negligible (order : ℕ) (constant : ℝ) (degree : ℕ) (hc : 0 ≤ constant) :
    Negligible (iterationBudget order constant degree) := by
  have hfirst := BetaReference.negligible_geometric_population 2 (3 / 4) (by norm_num)
    (by norm_num) (by norm_num) (fun security => security) (by filter_upwards [] with security; rfl)
  have hsecond := amplified_negligible order (8 * constant) degree (by positivity)
  apply (hfirst.add hsecond).of_eventually_le
  filter_upwards [] with security
  apply le_of_eq
  congr 1
  unfold iterationBudget entryBudget
  ring

theorem small_entries_eventually (order : ℕ) (constant : ℝ) (degree : ℕ) (hc : 0 ≤ constant) :
    ∀ᶠ security : ℕ in atTop,
      perturbationFactor security order * entryBudget constant degree security ≤ 1 / 4 := by
  filter_upwards [amplified_negligible order constant degree hc 1, eventually_ge_atTop 4]
    with security hsmall hsecurity
  have hs : (4 : ℝ) ≤ security := by exact_mod_cast hsecurity
  have h := (le_abs_self _).trans hsmall
  simp only [pow_one] at h
  exact h.trans (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) hs)

end
end CurrentAFT.CalibrationPrecisionRates
