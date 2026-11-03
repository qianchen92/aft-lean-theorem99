import AFT.RepresentedRing

/-! # The exact rational formal logarithm used by finite log certificates -/

namespace AFT.FormalLogarithm

open scoped BigOperators Classical PowerSeries

noncomputable section

set_option backward.isDefEq.respectTransparency false

def logarithm : PowerSeries ℚ := PowerSeries.mk fun order =>
  match order with
  | 0 => 0
  | index + 1 => (-1 : ℚ) ^ index / (index + 1)

@[simp] theorem logarithm_constant : PowerSeries.constantCoeff logarithm = 0 := rfl

theorem logarithm_coeff_succ (index : ℕ) : PowerSeries.coeff (index + 1) logarithm =
    (-1 : ℚ) ^ index / (index + 1) := by
  simp [logarithm, PowerSeries.coeff_mk]

theorem logarithm_derivative_coeff (index : ℕ) :
    PowerSeries.coeff index (PowerSeries.derivative ℚ logarithm) = (-1 : ℚ) ^ index := by
  rw [PowerSeries.coeff_derivative, logarithm_coeff_succ]
  field_simp

theorem logarithm_derivative_inverse :
    (1 + PowerSeries.X) * PowerSeries.derivative ℚ logarithm = (1 : PowerSeries ℚ) := by
  ext index
  rw [add_mul, one_mul, map_add]
  cases index with
  | zero => simp [logarithm_derivative_coeff]
  | succ index =>
    rw [PowerSeries.coeff_succ_X_mul, logarithm_derivative_coeff, logarithm_derivative_coeff]
    simp [pow_succ, PowerSeries.coeff_one]

theorem zero_substitution_constant (inner outer : PowerSeries ℚ)
    (hinner : PowerSeries.constantCoeff inner = 0) :
    PowerSeries.constantCoeff (outer.subst inner) = PowerSeries.constantCoeff outer := by
  change MvPowerSeries.constantCoeff (outer.subst inner) = _
  rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hinner)]
  have hfun : (fun index : ℕ => PowerSeries.coeff index outer • PowerSeries.constantCoeff (inner ^ index)) =
      Pi.single 0 (PowerSeries.constantCoeff outer) := by
    funext index
    by_cases hi : index = 0
    · subst index; simp
    · simp [hi, hinner]
  change (∑ᶠ index : ℕ, PowerSeries.coeff index outer • PowerSeries.constantCoeff (inner ^ index)) = _
  rw [hfun, finsum_eq_single _ 0 (by intro index hi; simp [hi])]
  simp

/-- The formal identity is proved by differentiating twice and comparing
constant coefficients; no logarithm identity is assumed for input tables. -/
theorem exp_logarithm : (PowerSeries.exp ℚ).subst logarithm = 1 + PowerSeries.X := by
  let output := (PowerSeries.exp ℚ).subst logarithm
  let slope := PowerSeries.derivative ℚ logarithm
  have hsubst := PowerSeries.HasSubst.of_constantCoeff_zero logarithm_constant
  have houtput : PowerSeries.derivative ℚ output = output * slope := by
    change PowerSeries.derivative ℚ ((PowerSeries.exp ℚ).subst logarithm) = _
    rw [PowerSeries.derivative_subst ℚ hsubst, PowerSeries.derivative_exp]
  have hslope : PowerSeries.derivative ℚ slope = -slope ^ 2 := by
    have hinv : slope * (1 + PowerSeries.X) = 1 := by
      simpa only [mul_comm] using logarithm_derivative_inverse
    have hh := (PowerSeries.derivative ℚ).leibniz_of_mul_eq_one hinv
    simpa only [map_add, Derivation.map_one_eq_zero, PowerSeries.derivative_X, zero_add, smul_eq_mul, mul_one] using hh
  have hsecond : PowerSeries.derivative ℚ (PowerSeries.derivative ℚ output) = 0 := by
    rw [houtput, (PowerSeries.derivative ℚ).leibniz, houtput, hslope]
    simp only [smul_eq_mul]
    ring
  have hc : PowerSeries.constantCoeff output = 1 := by
    rw [zero_substitution_constant logarithm (PowerSeries.exp ℚ) logarithm_constant,
      PowerSeries.constantCoeff_exp]
  have hcs : PowerSeries.constantCoeff slope = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]
    change PowerSeries.coeff 0 (PowerSeries.derivative ℚ logarithm) = 1
    rw [logarithm_derivative_coeff, pow_zero]
  have hfirst : PowerSeries.derivative ℚ output = 1 := by
    apply PowerSeries.derivative.ext
    · simpa only [Derivation.map_one_eq_zero] using hsecond
    · rw [houtput, map_mul, hc, hcs, mul_one, map_one]
  change output = _
  apply PowerSeries.derivative.ext
  · simpa only [map_add, Derivation.map_one_eq_zero, PowerSeries.derivative_X, zero_add] using hfirst
  · simpa using hc

end

end AFT.FormalLogarithm
