import CurrentAFT.CalibratedWeightApproximation
import CurrentAFT.CalibrationPrecisionRates
import CurrentAFT.NumericReferenceBudgets

/-! # Negligible public-weight numerical error at linear precision

The order is fixed. Precision and iteration counts both grow with security;
all true coordinate and paired-operator losses are bounded explicitly.
-/
namespace CurrentAFT.NumericalWeightRates
open AFT CalibrationTableNorm CalibrationMatrixApproximation CalibrationMatrixRates
  CalibrationPrecisionRates CalibratedWeightApproximation NumericalWeightEvaluation
open Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base

theorem negligible_const_mul {error : ℕ → ℝ} (h : Negligible error) (constant : ℝ) :
    Negligible (fun security => constant * error security) := by
  apply (h.mul_polynomial 1).of_eventually_le
  filter_upwards [eventually_ge_atTop ⌈|constant|⌉₊] with security hs
  have hc : |constant| ≤ (security : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hs)
  rw [abs_mul, abs_mul, pow_one, abs_of_nonneg (show (0 : ℝ) ≤ security by positivity)]
  exact mul_le_mul_of_nonneg_right hc (abs_nonneg _)

theorem negligible_bounded_factor {error factor : ℕ → ℝ} (h : Negligible error)
    (constant : ℝ) (degree : ℕ)
    (hbound : ∀ security, |factor security| ≤ constant * (Parameters.base security : ℝ)^degree) :
    Negligible (fun security => factor security * error security) := by
  have hc : 0 ≤ constant := by
    have hb := (abs_nonneg _).trans (hbound 0)
    exact nonneg_of_mul_nonneg_left hb (pow_pos (FirstResponse.base_pos 0) degree)
  apply (negligible_const_mul (h.mul_polynomial degree) (constant * 3^degree)).of_eventually_le
  filter_upwards [eventually_ge_atTop 1] with security hs
  have hb : (Parameters.base security : ℝ) ≤ 3 * security := by
    exact_mod_cast (show Parameters.base security ≤ 3 * security by unfold Parameters.base; omega)
  rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ constant * 3^degree),
    abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (security : ℝ)^degree by positivity)]
  have hm := mul_le_mul_of_nonneg_right
    ((hbound security).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Nat.cast_nonneg _) hb degree) hc)) (abs_nonneg (error security))
  simpa only [mul_pow, mul_assoc] using hm

theorem pointBudget_negligible (order : ℕ) (constant : ℝ) (degree : ℕ) (hc : 0 ≤ constant) :
    Negligible (fun security => pointBudget security order security (entryBudget constant degree security)) := by
  exact negligible_bounded_factor (iterationBudget_negligible order constant degree hc)
    (1 + encodeConstant order) (224*order) (fun security => by
      rw [abs_of_nonneg (show 0 ≤ 1 + encodeFactor security order by unfold encodeFactor; positivity)]
      exact one_add_encodeFactor_bound security order)

theorem localError_negligible : Negligible (fun security => localError security security) := by
  have h := polynomial_geometric_negligible NumericReferenceBudgets.pairedConstant 353 (1/2)
    NumericReferenceBudgets.pairedConstant_nonneg (by norm_num) (by norm_num)
  apply h.of_eventually_le
  filter_upwards [] with security
  rw [abs_of_nonneg (localError_nonneg security security), abs_of_nonneg (by positivity [NumericReferenceBudgets.pairedConstant_nonneg])]
  have hb := div_le_div_of_nonneg_right (NumericReferenceBudgets.paired_errorConstant_le security)
    (show (0:ℝ) ≤ (2:ℝ)^security by positivity)
  simpa only [localError, one_div_pow, div_eq_mul_inv, one_mul, inv_pow] using hb

theorem factor_power_bound (security order : ℕ) :
    factor security^order ≤ (3*131072 : ℝ)^order * (Parameters.base security : ℝ)^(64*order) := by
  have hq : (Parameters.modulus security : ℝ) ≤ 131072*(Parameters.base security : ℝ)^64 := by
    exact_mod_cast (Parameters.modulus_bounds security).2
  have hq1 : (1:ℝ) ≤ Parameters.modulus security := by exact_mod_cast (Parameters.modulus_spec security).2.one_le
  have h := pow_le_pow_left₀ (by unfold factor; positivity : 0 ≤ factor security)
    (show factor security ≤ 3*131072*(Parameters.base security : ℝ)^64 by unfold factor; linarith) order
  simpa only [mul_pow, ← pow_mul] using h

theorem weightBudget_negligible (order : ℕ) (constant : ℝ) (degree : ℕ) (hc : 0 ≤ constant) :
    Negligible (fun security => weightBudget security security order security (entryBudget constant degree security)) := by
  have hp := pointBudget_negligible order constant degree hc
  have he := negligible_bounded_factor localError_negligible (encodeConstant order) (224*order)
    (fun security => by
      rw [abs_of_nonneg (show 0 ≤ encodeFactor security order by unfold encodeFactor; positivity)]
      exact encodeFactor_bound security order)
  have hi := hp.add (negligible_const_mul he (2 * order))
  have hf := negligible_bounded_factor hi ((3*131072:ℝ)^order) (64*order)
    (fun security => by
      rw [abs_of_nonneg (show 0 ≤ factor security^order by unfold factor; positivity)]
      exact factor_power_bound security order)
  have h := hp.add (negligible_const_mul hf (Fintype.card (ControlCoordinates.PositiveArity order)))
  apply h.of_eventually_le
  filter_upwards [] with security
  apply le_of_eq
  congr 1
  unfold weightBudget
  ring

end
end CurrentAFT.NumericalWeightRates
