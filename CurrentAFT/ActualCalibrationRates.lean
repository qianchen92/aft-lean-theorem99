import CurrentAFT.ActualCalibrationFourier
import CurrentAFT.ActualCalibrationClipping

/-! # The actual Fourier budget has the manuscript's fixed-order decay -/
namespace CurrentAFT.ActualCalibrationRates
open ActualCalibrationFourier ActualCalibrationClipping
open Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

def fourierError (security order : ℕ) : ℝ :=
  Real.sqrt (energyBudget order / ActualPhysicalTail.analysisRadius security^(2 * (order + 1)))

def fourierConstant (order : ℕ) : ℝ :=
  2 * CoefficientOutputFock.normConstant order 1 * Real.sqrt (Real.exp 1)^(order + 1)

theorem fourierConstant_nonneg (order : ℕ) : 0 ≤ fourierConstant order :=
  mul_nonneg (mul_nonneg (by norm_num) (CoefficientOutputFock.normConstant_nonneg order 1))
    (pow_nonneg (Real.sqrt_nonneg _) _)

theorem analysisRadius_positive (security : ℕ) : 0 < ActualPhysicalTail.analysisRadius security := by
  unfold ActualPhysicalTail.analysisRadius BackgroundRates.radius
  exact div_pos (Real.rpow_pos_of_pos (FirstResponse.base_pos security) _) (Real.sqrt_pos.mpr (Real.exp_pos 1))

theorem fourierError_eq (security order : ℕ) :
    fourierError security order = fourierConstant order * (Parameters.base security : ℝ)^(-((order + 1 : ℕ) : ℝ) / 4) := by
  have hb := FirstResponse.base_pos security
  have hr := analysisRadius_positive security
  have hc : 0 ≤ 2 * CoefficientOutputFock.normConstant order 1 :=
    mul_nonneg (by norm_num) (CoefficientOutputFock.normConstant_nonneg order 1)
  have hpower : ActualPhysicalTail.analysisRadius security^(2 * (order + 1)) =
      (ActualPhysicalTail.analysisRadius security^(order + 1))^2 := by rw [← pow_mul, Nat.mul_comm]
  unfold fourierError energyBudget
  rw [hpower, Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq hc, Real.sqrt_sq (pow_nonneg hr.le _)]
  have hradius : BackgroundRates.radius security^(order + 1) =
      (Parameters.base security : ℝ)^(((order + 1 : ℕ) : ℝ) / 4) := by
    unfold BackgroundRates.radius
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb.le]
    congr 1
    ring
  rw [ActualPhysicalTail.analysisRadius, div_pow, hradius, div_div_eq_mul_div]
  rw [show -((order + 1 : ℕ) : ℝ) / 4 = -(((order + 1 : ℕ) : ℝ) / 4) by ring, Real.rpow_neg hb.le]
  unfold fourierConstant
  rw [div_eq_mul_inv]

theorem charged_fourier_eventually (accuracyOrder : ℕ) :
    ∀ᶠ security : ℕ in atTop,
      (Parameters.modulus security : ℝ) * fourierError security (Parameters.calibrationOrder accuracyOrder) ≤
        inversePower security (accuracyOrder + 2) := by
  filter_upwards [fourier_error_le_inversePower_eventually accuracyOrder
    (fourierConstant (Parameters.calibrationOrder accuracyOrder)) (fourierConstant_nonneg _)] with security hbound
  rw [fourierError_eq]
  simpa only [Nat.cast_add, Nat.cast_one, neg_div, mul_assoc, mul_comm, mul_left_comm] using hbound

theorem calibrationOrder_at_least_two (accuracyOrder : ℕ) : 2 ≤ Parameters.calibrationOrder accuracyOrder := by
  unfold Parameters.calibrationOrder
  omega

/-- Both actual error budgets are small enough for public charge
conditioning. No small-error premise is supplied by the caller. -/
theorem conditioning_small_eventually (accuracyOrder : ℕ) :
    ∃ cutoff : ℕ, ∀ security ≥ cutoff,
      ∀ hsecurity : ActualCompleteStability.threshold (Parameters.calibrationOrder accuracyOrder)
        (calibrationOrder_at_least_two accuracyOrder) ≤ security,
      ∀ layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security,
      fourierError security (Parameters.calibrationOrder accuracyOrder) +
        loss security (Parameters.calibrationOrder accuracyOrder) (calibrationOrder_at_least_two accuracyOrder) hsecurity layout ≤
          1 / (2 * (Parameters.modulus security : ℝ)) := by
  obtain ⟨fourierCutoff, hfourier⟩ := Filter.eventually_atTop.mp (charged_fourier_eventually accuracyOrder)
  obtain ⟨clipCutoff, hclip⟩ := charged_loss_negligible (Parameters.calibrationOrder accuracyOrder)
    (calibrationOrder_at_least_two accuracyOrder) 2
  refine ⟨max fourierCutoff clipCutoff, ?_⟩
  intro security hlarge hsecurity layout
  have hb := FirstResponse.base_pos security
  have hb2 : (2 : ℝ) ≤ Parameters.base security := by exact_mod_cast Parameters.base_ge_two security
  have hq := FirstResponse.modulus_pos security
  have hf := hfourier security ((le_max_left _ _).trans hlarge)
  have hc := hclip security ((le_max_right _ _).trans hlarge) hsecurity layout
  have hpower : inversePower security (accuracyOrder + 2) ≤ inversePower security 2 := by
    unfold inversePower
    apply one_div_le_one_div_of_le (pow_pos hb _)
    exact pow_le_pow_right₀ (by linarith) (by omega)
  have hsmall : inversePower security 2 ≤ (1 / 4 : ℝ) := by
    unfold inversePower
    apply (div_le_iff₀ (pow_pos hb _)).mpr
    nlinarith [sq_nonneg ((Parameters.base security : ℝ) - 2)]
  have hsum : (Parameters.modulus security : ℝ) *
      (fourierError security (Parameters.calibrationOrder accuracyOrder) +
        loss security (Parameters.calibrationOrder accuracyOrder) (calibrationOrder_at_least_two accuracyOrder) hsecurity layout) ≤ 1 / 2 := by
    rw [mul_add]
    linarith [hf.trans hpower]
  apply (le_div_iff₀ (mul_pos (by norm_num) hq)).mpr
  nlinarith only [hsum]

end
end CurrentAFT.ActualCalibrationRates
