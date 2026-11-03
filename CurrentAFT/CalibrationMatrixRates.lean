import CurrentAFT.CalibrationMatrixApproximation

/-! # Polynomial conditioning of the actual stored calibration matrix -/
namespace CurrentAFT.CalibrationMatrixRates
open CalibrationTableNorm CalibrationMatrixApproximation CalibrationPointCoordinates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
local instance ratesFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

def encodeConstant (order : ℕ) : ℝ := (2 * 131072 * 131074 : ℝ)^order
def decodeConstant (order : ℕ) : ℝ := ((order + 1 : ℕ)^2 : ℝ) * (3 * 131072)^order
def countConstant (order : ℕ) : ℝ := ((order + 1 : ℕ)^2 : ℝ) * 131072^order
def comparisonConstant (order : ℕ) : ℝ := 1 + (1 + encodeConstant order) * decodeConstant order
def perturbationConstant (order : ℕ) : ℝ :=
  comparisonConstant order * countConstant order * (1 + encodeConstant order)

theorem base_pow_one_le (security power : ℕ) : (1 : ℝ) ≤ (Parameters.base security : ℝ)^power :=
  one_le_pow₀ (by exact_mod_cast (show 1 ≤ Parameters.base security by
    have := Parameters.base_ge_two security; omega))

theorem encodeFactor_bound (security order : ℕ) :
    encodeFactor security order ≤ encodeConstant order * (Parameters.base security : ℝ)^(224 * order) :=
  ActualCoordinateBounds.coordinate_factor_polynomial security order

theorem decodeFactor_bound (security order : ℕ) :
    decodeFactor security order ≤ decodeConstant order * (Parameters.base security : ℝ)^(64 * order) := by
  have hq1 : (1 : ℝ) ≤ Parameters.modulus security := by
    exact_mod_cast (Parameters.modulus_spec security).2.one_le
  have hq : (Parameters.modulus security : ℝ) ≤ 131072 * (Parameters.base security : ℝ)^64 := by
    exact_mod_cast (Parameters.modulus_bounds security).2
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * (Parameters.modulus security : ℝ) + 1)
    (by linarith : 2 * (Parameters.modulus security : ℝ) + 1 ≤ 3 * 131072 * (Parameters.base security : ℝ)^64) order
  have hm := mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ (order + 1 : ℕ)^2 by positivity)
  simpa only [decodeFactor, decodeConstant, mul_pow, ← pow_mul, mul_assoc] using hm

theorem count_bound (security order : ℕ) :
    (Fintype.card (Index security order) : ℝ) ≤
      countConstant order * (Parameters.base security : ℝ)^(64 * order) := by
  unfold countConstant
  exact_mod_cast current_card_polynomial security order

theorem one_add_encodeFactor_bound (security order : ℕ) :
    1 + encodeFactor security order ≤ (1 + encodeConstant order) * (Parameters.base security : ℝ)^(224 * order) := by
  nlinarith only [encodeFactor_bound security order, base_pow_one_le security (224 * order)]

theorem comparisonFactor_bound (security order : ℕ) :
    comparisonFactor security order ≤ comparisonConstant order * (Parameters.base security : ℝ)^(288 * order) := by
  have he := one_add_encodeFactor_bound security order
  have hd := decodeFactor_bound security order
  have hm := mul_le_mul he hd (by unfold decodeFactor; positivity : 0 ≤ decodeFactor security order)
    (by unfold encodeConstant; positivity : 0 ≤ (1 + encodeConstant order) * (Parameters.base security : ℝ)^(224 * order))
  have heq : ((1 + encodeConstant order) * (Parameters.base security : ℝ)^(224 * order)) *
      (decodeConstant order * (Parameters.base security : ℝ)^(64 * order)) =
      (1 + encodeConstant order) * decodeConstant order * (Parameters.base security : ℝ)^(288 * order) := by
    rw [show 288 * order = 224 * order + 64 * order by omega, pow_add]
    ring
  rw [heq] at hm
  unfold comparisonFactor comparisonConstant
  nlinarith only [hm, base_pow_one_le security (288 * order)]

theorem perturbationFactor_bound (security order : ℕ) :
    perturbationFactor security order ≤ perturbationConstant order * (Parameters.base security : ℝ)^(576 * order) := by
  have hh := comparisonFactor_bound security order
  have hn := count_bound security order
  have he := one_add_encodeFactor_bound security order
  have hfirst := mul_le_mul hh hn (Nat.cast_nonneg _)
    (by unfold comparisonConstant encodeConstant decodeConstant; positivity :
      0 ≤ comparisonConstant order * (Parameters.base security : ℝ)^(288 * order))
  have hfinal := mul_le_mul hfirst he (by unfold encodeFactor; positivity : 0 ≤ 1 + encodeFactor security order)
    (by unfold comparisonConstant countConstant encodeConstant decodeConstant; positivity :
      0 ≤ (comparisonConstant order * (Parameters.base security : ℝ)^(288 * order)) *
        (countConstant order * (Parameters.base security : ℝ)^(64 * order)))
  apply hfinal.trans_eq
  unfold perturbationConstant
  rw [show 576 * order = (288 * order + 64 * order) + 224 * order by omega, pow_add, pow_add]
  ring

end
end CurrentAFT.CalibrationMatrixRates
