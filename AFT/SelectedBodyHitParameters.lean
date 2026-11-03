import AFT.ActivationSharp
import AFT.PrimaryParameterBounds

/-! # The actual root-hit normalization has exponent -23/4 -/

namespace AFT.GaussianSource

open Filter
open scoped Topology

noncomputable def selectedBodyHitCost (cutoffScale : ℝ) (parameter pool : ℕ) : ℝ :=
  (2 / v7Activation cutoffScale parameter) *
    (4 * (1 / Real.sqrt (pool : ℝ)) +
      8 * Real.sqrt (Parameters.modulus parameter : ℝ) * (1 / Real.sqrt (pool : ℝ)) ^ 2)

/-- The bound includes the actual primary inverse factor two, the actual
activation loss, and both integrated and fixed-output channel costs. -/
theorem selectedBodyHitCost_le (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (parameter pool : ℕ) (hp : 2 ≤ parameter) (hpool : Parameters.legs parameter ≤ 2 * pool) :
    selectedBodyHitCost cutoffScale parameter pool ≤
      (144 * activationConstant cutoffScale) / (parameter : ℝ) ^ (23 / 4 : ℝ) := by
  have hp0 : (0 : ℝ) < parameter := by exact_mod_cast (by omega : 0 < parameter)
  have hp1 : (1 : ℝ) ≤ parameter := by exact_mod_cast (by omega : 1 ≤ parameter)
  have hr := v7_primary_pool_rate_bound parameter pool hpool
  have hrate : 1 / Real.sqrt (pool : ℝ) ≤ 2 / (parameter : ℝ) ^ 15 := by
    simpa only [Parameters.security_eq parameter hp] using hr.2
  have hq : (Parameters.modulus parameter : ℝ) ≤ 2 * (parameter : ℝ) ^ 40 := by
    exact_mod_cast (by simpa only [Parameters.security_eq parameter hp] using (Parameters.modulus_bounds parameter).2)
  have hroot : Real.sqrt (Parameters.modulus parameter : ℝ) ≤ 2 * (parameter : ℝ) ^ 20 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · have hh : 2 * (parameter : ℝ) ^ 40 ≤ (2 * (parameter : ℝ) ^ 20) ^ 2 := by nlinarith [pow_nonneg hp0.le 40]
      exact hq.trans hh
  have hsmall : 1 / (parameter : ℝ) ^ 15 ≤ 1 / (parameter : ℝ) ^ 10 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ hp1 (by decide))
  have hbase : 4 * (1 / Real.sqrt (pool : ℝ)) +
      8 * Real.sqrt (Parameters.modulus parameter : ℝ) * (1 / Real.sqrt (pool : ℝ)) ^ 2 ≤
      72 / (parameter : ℝ) ^ 10 := by
    calc
      _ ≤ 4 * (2 / (parameter : ℝ) ^ 15) +
        8 * (2 * (parameter : ℝ) ^ 20) * (2 / (parameter : ℝ) ^ 15) ^ 2 := by gcongr
      _ = 8 * (1 / (parameter : ℝ) ^ 15) + 64 / (parameter : ℝ) ^ 10 := by field_simp; ring
      _ ≤ 8 * (1 / (parameter : ℝ) ^ 10) + 64 / (parameter : ℝ) ^ 10 := by gcongr
      _ = _ := by ring
  have hactivation := v7Activation_inverse_upper cutoffScale parameter hscale (by omega)
  have ha := activationConstant_pos cutoffScale hscale
  have hrho : 0 < v7Activation cutoffScale parameter := lt_of_lt_of_le (by positivity)
    (v7Activation_lower_rpow cutoffScale parameter hscale (by omega))
  have hpowers : (parameter : ℝ) ^ 10 = (parameter : ℝ) ^ (17 / 4 : ℝ) * (parameter : ℝ) ^ (23 / 4 : ℝ) := by
    rw [← Real.rpow_add hp0]
    norm_num
    exact (Real.rpow_natCast _ 10).symm
  unfold selectedBodyHitCost
  calc
    _ ≤ (2 * (activationConstant cutoffScale * (parameter : ℝ) ^ (17 / 4 : ℝ))) * (72 / (parameter : ℝ) ^ 10) := by
      apply mul_le_mul _ hbase (by positivity) (by positivity)
      simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hactivation (by norm_num : (0 : ℝ) ≤ 2)
    _ = _ := by rw [hpowers]; field_simp; ring

end AFT.GaussianSource
