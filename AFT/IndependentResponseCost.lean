import AFT.PairedRootCost

/-! # Sharp independent-root nonlinear normalization -/

namespace AFT.GaussianSource
open Filter
open scoped Topology
noncomputable section

/-- Only the actual inverse and pool rate are charged to each new output.
Fixed-fiber losses are accounted for in the local sharp channel estimate. -/
def independentCoordinateCost (cutoffScale : ℝ) (parameter pool : ℕ) : ℝ :=
  (4 / v7Activation cutoffScale parameter) * (1 / Real.sqrt (pool : ℝ))

theorem independentCoordinateCost_le (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (parameter pool : ℕ) (hp : 2 ≤ parameter) (hpool : Parameters.legs parameter ≤ 2 * pool) :
    independentCoordinateCost cutoffScale parameter pool ≤
      (8 * activationConstant cutoffScale) / (parameter : ℝ) ^ (43 / 4 : ℝ) := by
  have hp0 : (0 : ℝ) < parameter := by exact_mod_cast (by omega : 0 < parameter)
  have ha := activationConstant_pos cutoffScale hscale
  have hrho : 0 < v7Activation cutoffScale parameter := lt_of_lt_of_le (by positivity)
    (v7Activation_lower_rpow cutoffScale parameter hscale (by omega))
  have hrate : 1 / Real.sqrt (pool : ℝ) ≤ 2 / (parameter : ℝ) ^ 15 := by
    simpa only [Parameters.security_eq parameter hp] using (v7_primary_pool_rate_bound parameter pool hpool).2
  have hactivation := v7Activation_inverse_upper cutoffScale parameter hscale (by omega)
  have hpow : (parameter : ℝ) ^ 15 =
      (parameter : ℝ) ^ (17 / 4 : ℝ) * (parameter : ℝ) ^ (43 / 4 : ℝ) := by
    rw [← Real.rpow_add hp0]
    norm_num
    exact (Real.rpow_natCast _ 15).symm
  unfold independentCoordinateCost
  calc
    _ ≤ (4 * (activationConstant cutoffScale * (parameter : ℝ) ^ (17 / 4 : ℝ))) *
        (2 / (parameter : ℝ) ^ 15) := by
      apply mul_le_mul _ hrate (by positivity) (by positivity)
      simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hactivation (by norm_num : (0 : ℝ) ≤ 4)
    _ = _ := by rw [hpow]; field_simp; ring


theorem independent_primary_rate_small (parameter pool : ℕ) (hp : 2 ≤ parameter)
    (hpool : Parameters.legs parameter ≤ 2*pool) :
    0 < 1/Real.sqrt (pool : ℝ) ∧ 1/Real.sqrt (pool : ℝ) ≤ 1 ∧
      (1/Real.sqrt (pool : ℝ))*(parameter : ℝ)^4 ≤ 1 := by
  have hx : (0 : ℝ) < parameter := by exact_mod_cast (by omega : 0 < parameter)
  have hx1 : (1 : ℝ) ≤ parameter := by exact_mod_cast (by omega : 1 ≤ parameter)
  have hx2 : (2 : ℝ) ≤ parameter := by exact_mod_cast hp
  have hb : 1/Real.sqrt (pool : ℝ) ≤ 2/(parameter : ℝ)^15 := by
    simpa only [Parameters.security_eq parameter hp] using (v7_primary_pool_rate_bound parameter pool hpool).2
  have hpow (power : ℕ) (hpower : 1 ≤ power) : (2 : ℝ) ≤ (parameter : ℝ)^power :=
    hx2.trans (by simpa only [pow_one] using pow_le_pow_right₀ hx1 hpower)
  refine ⟨(v7_primary_pool_rate_bound parameter pool hpool).1,
    hb.trans ((div_le_one (pow_pos hx 15)).mpr (hpow 15 (by omega))),?_⟩
  calc
    _ ≤ (2/(parameter : ℝ)^15)*(parameter : ℝ)^4 := mul_le_mul_of_nonneg_right hb (by positivity)
    _ = 2/(parameter : ℝ)^11 := by field_simp
    _ ≤ 1 := (div_le_one (pow_pos hx 11)).mpr (hpow 11 (by omega))

/-- The square density cost of every nonlinear positive coefficient is
smaller than the new-coordinate linear cost, uniformly after degree two. -/
theorem independent_positive_cost_bound (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (parameter pool : ℕ) (hp : 2 ≤ parameter) (hpool : Parameters.legs parameter ≤ 2*pool)
    (hlarge : 8*activationConstant cutoffScale ≤ (parameter : ℝ)) :
    independentCoordinateCost cutoffScale parameter pool ≤ 1 ∧
      independentCoordinateCost cutoffScale parameter pool ^ 2 * (parameter : ℝ)^4 ≤
        (8*activationConstant cutoffScale)^2/(parameter : ℝ)^(43/4 : ℝ) := by
  have hx : (0 : ℝ) < parameter := by exact_mod_cast (by omega : 0 < parameter)
  have hx1 : (1 : ℝ) ≤ parameter := by exact_mod_cast (by omega : 1 ≤ parameter)
  have ha := activationConstant_pos cutoffScale hscale
  have hden : 0 < (parameter : ℝ)^(43/4 : ℝ) := Real.rpow_pos_of_pos hx _
  have hp1 : (parameter : ℝ) ≤ (parameter : ℝ)^(43/4 : ℝ) := by
    have hh := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (1 : ℝ) ≤ 43/4)
    simpa only [Real.rpow_one] using hh
  have hp4 : (parameter : ℝ)^4 ≤ (parameter : ℝ)^(43/4 : ℝ) := by
    have hh := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (4 : ℝ) ≤ 43/4)
    change (parameter : ℝ)^((4 : ℕ) : ℝ) ≤ _ at hh
    simpa only [Real.rpow_natCast] using hh
  have hb := independentCoordinateCost_le cutoffScale hscale parameter pool hp hpool
  have hz : 0 ≤ independentCoordinateCost cutoffScale parameter pool := by
    unfold independentCoordinateCost
    have hrho : 0 < v7Activation cutoffScale parameter := activation_positive _ _ _ _
      (legFeatureCount_positive cutoffScale parameter hscale (by omega))
    positivity
  refine ⟨hb.trans ((div_le_one hden).mpr (hlarge.trans hp1)),?_⟩
  apply (mul_le_mul_of_nonneg_right ((sq_le_sq₀ hz (by positivity)).mpr hb) (by positivity : 0 ≤ (parameter : ℝ)^4)).trans
  have hh := mul_le_mul_of_nonneg_left hp4
    (show 0 ≤ (8*activationConstant cutoffScale)^2/((parameter : ℝ)^(43/4 : ℝ))^2 by positivity)
  convert hh using 1 <;> field_simp

/-- A degree-k quotient contains at most floor(k/2) nonlinear factors. -/
def independentNonlinearCost (cutoffScale : ℝ) (parameter pool degree : ℕ) : ℝ :=
  Real.sqrt (pool : ℝ) * independentCoordinateCost cutoffScale parameter pool ^ degree *
    (parameter : ℝ) ^ (4 * (degree / 2))

/-- The actual V7 parameters give the desired uniform lambda^(-5/2)
loss already in degree two. No connected-root allocation is used. -/
theorem independentNonlinearCost_le (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (parameter pool degree : ℕ) (hp : 2 ≤ parameter)
    (hpool : Parameters.legs parameter ≤ 2 * pool) (hpoolUpper : pool ≤ Parameters.legs parameter)
    (hdegree : 2 ≤ degree) :
    independentNonlinearCost cutoffScale parameter pool degree ≤
      (8 * activationConstant cutoffScale) ^ degree / (parameter : ℝ) ^ (5 / 2 : ℝ) := by
  have hp0 : (0 : ℝ) < parameter := by exact_mod_cast (by omega : 0 < parameter)
  have hp1 : (1 : ℝ) ≤ parameter := by exact_mod_cast (by omega : 1 ≤ parameter)
  have ha := activationConstant_pos cutoffScale hscale
  have hpoolreal : (pool : ℝ) ≤ (parameter : ℝ) ^ 30 := by
    exact_mod_cast (show pool ≤ parameter ^ 30 by simpa only [Parameters.legs,Parameters.security_eq parameter hp] using hpoolUpper)
  have hpoolroot : Real.sqrt (pool : ℝ) ≤ (parameter : ℝ) ^ 15 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    convert hpoolreal using 1
    ring
  have hlocal : (parameter : ℝ) ^ (4 * (degree / 2)) ≤ ((parameter : ℝ) ^ 2) ^ degree := by
    rw [← pow_mul]
    apply pow_le_pow_right₀ hp1
    omega
  have hcost := independentCoordinateCost_le cutoffScale hscale parameter pool hp hpool
  have hcost0 : 0 ≤ independentCoordinateCost cutoffScale parameter pool := by
    unfold independentCoordinateCost
    have hrho : 0 < v7Activation cutoffScale parameter := lt_of_lt_of_le (by positivity)
      (v7Activation_lower_rpow cutoffScale parameter hscale (by omega))
    positivity
  have hcombine : ((8 * activationConstant cutoffScale) / (parameter : ℝ) ^ (43 / 4 : ℝ)) *
      (parameter : ℝ) ^ 2 = (8 * activationConstant cutoffScale) / (parameter : ℝ) ^ (35 / 4 : ℝ) := by
    have hh : (parameter : ℝ) ^ (43 / 4 : ℝ) =
        (parameter : ℝ) ^ 2 * (parameter : ℝ) ^ (35 / 4 : ℝ) := by
      rw [← Real.rpow_natCast,← Real.rpow_add hp0]
      congr 1
      norm_num
    rw [hh]
    field_simp
  have hexp : (15 : ℝ) + 5 / 2 ≤ (35 / 4 : ℝ) * degree := by
    have hd : (2 : ℝ) ≤ degree := by exact_mod_cast hdegree
    nlinarith
  have hpower : (parameter : ℝ)^15 * (parameter : ℝ)^(5/2 : ℝ) ≤
      ((parameter : ℝ)^(35/4 : ℝ))^degree := by
    rw [← Real.rpow_natCast,← Real.rpow_add hp0,← Real.rpow_mul_natCast hp0.le]
    exact Real.rpow_le_rpow_of_exponent_le hp1 hexp
  unfold independentNonlinearCost
  calc
    _ ≤ (parameter : ℝ)^15 *
        ((8 * activationConstant cutoffScale)/(parameter : ℝ)^(43/4 : ℝ))^degree *
        ((parameter : ℝ)^2)^degree := by gcongr
    _ = (parameter : ℝ)^15 *
        ((8 * activationConstant cutoffScale)/(parameter : ℝ)^(35/4 : ℝ))^degree := by
      rw [mul_assoc,← mul_pow,hcombine]
    _ ≤ (8 * activationConstant cutoffScale)^degree / (parameter : ℝ)^(5/2 : ℝ) := by
      rw [div_pow]
      have hh := mul_le_mul_of_nonneg_left hpower
        (pow_nonneg (by positivity : 0 ≤ 8 * activationConstant cutoffScale) degree)
      have hden : 0 < ((parameter : ℝ)^(35/4 : ℝ))^degree :=
        pow_pos (Real.rpow_pos_of_pos hp0 _) degree
      apply (le_div_iff₀ (Real.rpow_pos_of_pos hp0 _)).mpr
      rw [← mul_div_assoc,div_mul_eq_mul_div]
      apply (div_le_iff₀ hden).mpr
      convert hh using 1
      ring

end
end AFT.GaussianSource
