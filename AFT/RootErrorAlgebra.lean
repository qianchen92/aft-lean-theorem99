import AFT.Negligible
import AFT.GaussianRatio

namespace AFT

open Filter
open scoped Topology

theorem Negligible.const_mul {error : ℕ → ℝ} (h : Negligible error) (constant : ℝ) :
    Negligible (fun parameter => constant * error parameter) := by
  intro order
  have hc : ∀ᶠ parameter : ℕ in atTop, |constant| ≤ (parameter : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop |constant|)
  filter_upwards [h (order + 1), hc, eventually_ge_atTop 1] with parameter he hc hp
  have hp0 : (0 : ℝ) < parameter := by exact_mod_cast (by omega : 0 < parameter)
  rw [abs_mul]
  calc
    _ ≤ (parameter : ℝ) * (1 / (parameter : ℝ) ^ (order + 1)) :=
      mul_le_mul hc he (abs_nonneg _) (Nat.cast_nonneg parameter)
    _ = _ := by rw [pow_succ]; field_simp

theorem Negligible.tendsto_zero {error : ℕ → ℝ} (h : Negligible error) :
    Tendsto error atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro epsilon hepsilon
  have hl : ∀ᶠ parameter : ℕ in atTop, 1 / epsilon < (parameter : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (1 / epsilon))
  filter_upwards [h 1, hl, eventually_ge_atTop 1] with parameter he hl hp
  have hp0 : (0 : ℝ) < parameter := by exact_mod_cast (by omega : 0 < parameter)
  rw [Real.dist_eq, sub_zero]
  apply he.trans_lt
  simp only [pow_one]
  apply (div_lt_iff₀ hp0).mpr
  have hh := (div_lt_iff₀ hepsilon).mp hl
  nlinarith

/-- A negligible error is eventually below every fixed inverse power of
any positive population bounded by the V7 polynomial upper envelope. -/
theorem Negligible.inverse_population_bound {error : ℕ → ℝ} (h : Negligible error)
    (population : ℕ → ℕ)
    (hpositive : ∀ parameter, 0 < population parameter)
    (hupper : ∀ᶠ parameter : ℕ in atTop, population parameter ≤ 2 * parameter ^ 60)
    (power : ℕ) :
    ∀ᶠ parameter : ℕ in atTop, |error parameter| ≤ 1 / (population parameter : ℝ) ^ power := by
  filter_upwards [h (60 * power + 1), hupper, eventually_ge_atTop (2 ^ power)]
    with parameter he hu hp
  have hp0 : (0 : ℝ) < parameter := by
    exact_mod_cast (lt_of_lt_of_le (pow_pos (by decide : 0 < 2) power) hp)
  have hn0 : (0 : ℝ) < population parameter := by exact_mod_cast hpositive parameter
  have hu' : (population parameter : ℝ) ≤ 2 * (parameter : ℝ) ^ 60 := by exact_mod_cast hu
  have hp' : (2 : ℝ) ^ power ≤ parameter := by exact_mod_cast hp
  have hden : (population parameter : ℝ) ^ power ≤ (parameter : ℝ) ^ (60 * power + 1) := by
    calc
      _ ≤ (2 * (parameter : ℝ) ^ 60) ^ power := pow_le_pow_left₀ hn0.le hu' power
      _ = 2 ^ power * (parameter : ℝ) ^ (60 * power) := by rw [mul_pow, pow_mul]
      _ ≤ (parameter : ℝ) * (parameter : ℝ) ^ (60 * power) :=
        mul_le_mul_of_nonneg_right hp' (by positivity)
      _ = _ := by rw [pow_succ]; ring
  exact he.trans (one_div_le_one_div_of_le (pow_pos hn0 power) hden)

namespace GaussianSource

/-- The fixed-order multiplicative error is Lipschitz at zero, with an
explicit constant. Thus the polynomially tiny scalar errors survive all
the finite products and quotients in the root marginal. -/
theorem ratioError_le_linear (error : ℝ) (order : ℕ)
    (he0 : 0 ≤ error) (he1 : error ≤ 1 / 2) :
    |ratioError error order| ≤ (6 * (order : ℝ) * 3 ^ order) * error := by
  have hminus : 0 < 1 - error := by linarith
  have hplus : 0 < 1 + error := by linarith
  let upper := (1 + error) / (1 - error)
  let lower := (1 - error) / (1 + error)
  have hu0 : 0 ≤ upper := div_nonneg hplus.le hminus.le
  have hl0 : 0 ≤ lower := div_nonneg hminus.le hplus.le
  have hu1 : 1 ≤ upper := (le_div_iff₀ hminus).mpr (by linarith)
  have hu3 : upper ≤ 3 := (div_le_iff₀ hminus).mpr (by linarith)
  have hl1 : lower ≤ 1 := (div_le_one hplus).mpr (by linarith)
  have hdu : |upper - 1| ≤ 4 * error := by
    rw [abs_of_nonneg (by linarith)]
    have hu : upper ≤ 1 + 4 * error := (div_le_iff₀ hminus).mpr (by
      nlinarith [mul_nonneg he0 (show 0 ≤ 1 / 2 - error by linarith)])
    linarith
  have hdl : |lower - 1| ≤ 2 * error := by
    rw [abs_of_nonpos (by linarith)]
    have hl : 1 - 2 * error ≤ lower := (le_div_iff₀ hplus).mpr (by nlinarith [sq_nonneg error])
    linarith
  have hup : |upper ^ order - 1| ≤ 4 * error * order * 3 ^ order := by
    have hh := abs_pow_sub_pow_le (a := upper) (b := (1 : ℝ)) (n := order)
    simp only [one_pow, abs_of_nonneg hu0, abs_one, max_eq_left hu1] at hh
    apply hh.trans
    have hp : upper ^ (order - 1) ≤ (3 : ℝ) ^ order :=
      (pow_le_pow_left₀ hu0 hu3 _).trans (pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _))
    exact mul_le_mul (mul_le_mul_of_nonneg_right hdu (Nat.cast_nonneg order)) hp
      (pow_nonneg hu0 _) (by positivity)
  have hlo : |lower ^ order - 1| ≤ 2 * error * order := by
    have hh := abs_pow_sub_pow_le (a := lower) (b := (1 : ℝ)) (n := order)
    simp only [one_pow, abs_of_nonneg hl0, abs_one, max_eq_right hl1, mul_one] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hdl (Nat.cast_nonneg order))
  have hp1 : (1 : ℝ) ≤ 3 ^ order := one_le_pow₀ (by norm_num)
  have heq : ratioError error order = (upper ^ order - 1) - (lower ^ order - 1) := by
    simp only [ratioError, upper, lower, div_pow]
    ring
  rw [heq]
  apply (abs_sub _ _).trans
  apply (add_le_add hup hlo).trans
  nlinarith [mul_le_mul_of_nonneg_left hp1 (by positivity : 0 ≤ 2 * error * order)]

theorem negligible_ratioError {error : ℕ → ℝ} (h : Negligible error)
    (he0 : ∀ᶠ parameter in atTop, 0 ≤ error parameter) (order : ℕ) :
    Negligible (fun parameter => ratioError (error parameter) order) := by
  apply (h.const_mul (6 * (order : ℝ) * 3 ^ order)).of_eventually_le
  filter_upwards [he0, h.tendsto_zero.eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))] with parameter he0 he1
  have hh := ratioError_le_linear (error parameter) order he0 he1.le
  simpa only [abs_mul, abs_of_nonneg he0,
    abs_of_nonneg (by positivity : 0 ≤ 6 * (order : ℝ) * 3 ^ order)] using hh

end GaussianSource

end AFT
