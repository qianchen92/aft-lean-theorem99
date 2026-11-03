import AFT.SelectedBodyHitParameters
import AFT.RootErrorParameters

/-! # Actual parameter costs for connected paired numerator coefficients -/

namespace AFT.GaussianSource
open Filter
open scoped Topology
noncomputable section

/-- Each newly emitted coordinate includes the primary inverse, activation,
its pool normalization, and every newly fixed-output penalty. -/
def pairedOutputCoordinateCost (cutoffScale : ℝ) (parameter pool : ℕ) : ℝ :=
  (4 / v7Activation cutoffScale parameter) * (1 / Real.sqrt (pool : ℝ)) *
    (1 + 2 * (1 / Real.sqrt (pool : ℝ)) * Real.sqrt (Parameters.modulus parameter : ℝ))

theorem pairedOutputCoordinateCost_le (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (parameter pool : ℕ) (hp : 2 ≤ parameter) (hpool : Parameters.legs parameter ≤ 2 * pool) :
    pairedOutputCoordinateCost cutoffScale parameter pool ≤
      (144 * activationConstant cutoffScale) / (parameter : ℝ) ^ (23 / 4 : ℝ) := by
  have hconst := activationConstant_pos cutoffScale hscale
  have hp0 : (0 : ℝ) < parameter := by exact_mod_cast (by omega : 0 < parameter)
  have hrho : 0 < v7Activation cutoffScale parameter := lt_of_lt_of_le (by positivity)
    (v7Activation_lower_rpow cutoffScale parameter hscale (by omega))
  have hnonneg : 0 ≤ pairedOutputCoordinateCost cutoffScale parameter pool := by
    unfold pairedOutputCoordinateCost
    positivity
  calc
    _ ≤ 2 * pairedOutputCoordinateCost cutoffScale parameter pool := by linarith
    _ = selectedBodyHitCost cutoffScale parameter pool := by
      unfold pairedOutputCoordinateCost selectedBodyHitCost
      ring
    _ ≤ _ := selectedBodyHitCost_le cutoffScale hscale parameter pool hp hpool

/-- The actual population provides the per-root allocation. -/
theorem root_allocation_le_eventually :
    ∀ᶠ parameter : ℕ in atTop,
      1 / Real.sqrt (Parameters.bodies parameter : ℝ) ≤ 2 / (parameter : ℝ)^30 := by
  filter_upwards [eventually_ge_atTop 2] with parameter hp
  have hN : parameter^60 ≤ 2 * Parameters.bodies parameter := by
    have hdim := (Parameters.dimension_bounds parameter).1
    rw [Parameters.security_eq parameter hp] at hdim
    have hpop := Parameters.population_identity parameter
    have hh := Parameters.legs_le_half_bodies parameter
    omega
  have hp0 : (0 : ℝ) < parameter := by exact_mod_cast (by omega : 0 < parameter)
  have hN0 : (0 : ℝ) < Parameters.bodies parameter := Nat.cast_pos.mpr (Parameters.bodies_positive parameter)
  have hN' : (parameter : ℝ)^60 ≤ 2 * Parameters.bodies parameter := by exact_mod_cast hN
  have hroot : (parameter : ℝ)^30 / 2 ≤ Real.sqrt (Parameters.bodies parameter : ℝ) := by
    apply (Real.le_sqrt (by positivity) (by positivity)).mpr
    have hpow : ((parameter : ℝ)^30)^2 = (parameter : ℝ)^60 := by ring
    nlinarith
  calc
    _ ≤ 1 / ((parameter : ℝ)^30 / 2) := one_div_le_one_div_of_le (by positivity) hroot
    _ = _ := by field_simp

/-- This is the raw higher-degree budget relative to the old primary input,
including the allocated norm of each selected root. -/
def pairedRootCost (cutoffScale : ℝ) (parameter pool roots degree : ℕ) : ℝ :=
  (1 / Real.sqrt (Parameters.bodies parameter : ℝ))^roots * Real.sqrt (pool : ℝ) *
    (pairedOutputCoordinateCost cutoffScale parameter pool)^degree *
    Real.sqrt (26912768 * (parameter : ℝ)^8)

/-- The bound retains the root count and output degree separately. In
particular one root and degrees two, three, four give the claimed exponents. -/
theorem pairedRootCost_le_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (pool : ℕ → ℕ)
    (hpool : ∀ᶠ parameter in atTop,
      Parameters.legs parameter ≤ 2 * pool parameter ∧ pool parameter ≤ Parameters.legs parameter) :
    ∀ᶠ parameter in atTop, ∀ roots degree : ℕ,
      pairedRootCost cutoffScale parameter (pool parameter) roots degree ≤
        (2 / (parameter : ℝ)^30)^roots * (parameter : ℝ)^15 *
        ((144 * activationConstant cutoffScale) / (parameter : ℝ)^(23/4 : ℝ))^degree *
        (Real.sqrt 26912768 * (parameter : ℝ)^4) := by
  filter_upwards [root_allocation_le_eventually,hpool,eventually_ge_atTop 2] with parameter hroot hp hparameter roots degree
  have hpoolreal : (pool parameter : ℝ) ≤ (parameter : ℝ)^30 := by
    exact_mod_cast (show pool parameter ≤ parameter^30 by simpa [Parameters.legs,Parameters.security_eq parameter hparameter] using hp.2)
  have hpoolroot : Real.sqrt (pool parameter : ℝ) ≤ (parameter : ℝ)^15 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · convert hpoolreal using 1; ring
  have hraw : Real.sqrt (26912768 * (parameter : ℝ)^8) = Real.sqrt 26912768 * (parameter : ℝ)^4 := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 26912768)]
    congr 1
    rw [show (parameter : ℝ)^8 = ((parameter : ℝ)^4)^2 by ring,Real.sqrt_sq (by positivity)]
  have hconst := activationConstant_pos cutoffScale hscale
  have hp0 : (0 : ℝ) < parameter := by exact_mod_cast (by omega : 0 < parameter)
  have hrho : 0 < v7Activation cutoffScale parameter := lt_of_lt_of_le (by positivity)
    (v7Activation_lower_rpow cutoffScale parameter hscale (by omega))
  have hcost0 : 0 ≤ pairedOutputCoordinateCost cutoffScale parameter (pool parameter) := by
    unfold pairedOutputCoordinateCost
    positivity
  unfold pairedRootCost
  rw [hraw]
  gcongr
  exact pairedOutputCoordinateCost_le cutoffScale hscale parameter (pool parameter) hparameter hp.1

/-- Collapsing the actual powers gives the single-root exponents exactly. -/
theorem pairedRootCost_one_le_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (pool : ℕ → ℕ)
    (hpool : ∀ᶠ parameter in atTop,
      Parameters.legs parameter ≤ 2 * pool parameter ∧ pool parameter ≤ Parameters.legs parameter) :
    ∀ᶠ parameter in atTop, ∀ degree : ℕ,
      pairedRootCost cutoffScale parameter (pool parameter) 1 degree ≤
        (2 * Real.sqrt 26912768 * (144 * activationConstant cutoffScale)^degree) /
          (parameter : ℝ)^(11 + (23/4 : ℝ)*degree) := by
  filter_upwards [pairedRootCost_le_eventually cutoffScale hscale pool hpool,eventually_ge_atTop 2]
    with parameter hbound hp degree
  apply (hbound 1 degree).trans_eq
  have hp0 : (0 : ℝ) < parameter := by exact_mod_cast (by omega : 0 < parameter)
  have hpowers : (parameter : ℝ)^(11 + (23/4 : ℝ)*degree) =
      (parameter : ℝ)^11 * ((parameter : ℝ)^(23/4 : ℝ))^degree := by
    rw [Real.rpow_add hp0,Real.rpow_mul_natCast hp0.le]
    congr 1
    norm_num
  rw [hpowers,pow_one,div_pow]
  field_simp

/-- A joint two-root tag uses its root norm once, then receives two
allocations. It does not apply two response operators to the same input. -/
theorem pairedRootCost_two_le_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (pool : ℕ → ℕ)
    (hpool : ∀ᶠ parameter in atTop,
      Parameters.legs parameter ≤ 2 * pool parameter ∧ pool parameter ≤ Parameters.legs parameter) :
    ∀ᶠ parameter in atTop, ∀ degree : ℕ,
      pairedRootCost cutoffScale parameter (pool parameter) 2 degree ≤
        (4 * Real.sqrt 26912768 * (144 * activationConstant cutoffScale)^degree) /
          (parameter : ℝ)^(41 + (23/4 : ℝ)*degree) := by
  filter_upwards [pairedRootCost_le_eventually cutoffScale hscale pool hpool,eventually_ge_atTop 2]
    with parameter hbound hp degree
  apply (hbound 2 degree).trans_eq
  have hp0 : (0 : ℝ) < parameter := by exact_mod_cast (by omega : 0 < parameter)
  have hpowers : (parameter : ℝ)^(41 + (23/4 : ℝ)*degree) =
      (parameter : ℝ)^41 * ((parameter : ℝ)^(23/4 : ℝ))^degree := by
    rw [Real.rpow_add hp0,Real.rpow_mul_natCast hp0.le]
    congr 1
    norm_num
  rw [hpowers,div_pow,div_pow]
  field_simp
  ring

/-- The activation has canceled in the actual centered linear response.
Only the root allocation and the integrated/fixed anchor costs remain. -/
def rootLinearActivityRatio (parameter pool : ℕ) : ℝ :=
  (2 / Real.sqrt (Parameters.bodies parameter : ℝ)) *
    (Real.sqrt 48 / (parameter : ℝ)^11 + 8 * (1 / Real.sqrt (pool : ℝ)) * (parameter : ℝ)^8)

theorem rootLinearActivityRatio_le_eventually (pool : ℕ → ℕ)
    (hpool : ∀ᶠ parameter in atTop, Parameters.legs parameter ≤ 2*pool parameter) :
    ∀ᶠ parameter in atTop,
      rootLinearActivityRatio parameter (pool parameter) ≤
        (4 * (Real.sqrt 48 + 16)) / (parameter : ℝ)^37 := by
  filter_upwards [root_allocation_le_eventually,hpool,eventually_ge_atTop 2] with parameter hroot hp hparameter
  have hx : (0 : ℝ) < parameter := by exact_mod_cast (by omega : 0 < parameter)
  have hx1 : (1 : ℝ) ≤ parameter := by exact_mod_cast (by omega : 1 ≤ parameter)
  have hrate : 1 / Real.sqrt (pool parameter : ℝ) ≤ 2 / (parameter : ℝ)^15 := by
    simpa only [Parameters.security_eq parameter hparameter] using (v7_primary_pool_rate_bound parameter (pool parameter) hp).2
  have hdecay : 1/(parameter : ℝ)^41 ≤ 1/(parameter : ℝ)^37 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ hx1 (by decide))
  unfold rootLinearActivityRatio
  calc
    _ ≤ (2 * (2 / (parameter : ℝ)^30)) *
        (Real.sqrt 48 / (parameter : ℝ)^11 + 8 * (2 / (parameter : ℝ)^15) * (parameter : ℝ)^8) := by
      have hroot' : 2 / Real.sqrt (Parameters.bodies parameter : ℝ) ≤ 2*(2/(parameter : ℝ)^30) := by
        simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hroot (by norm_num : (0 : ℝ) ≤ 2)
      gcongr
    _ = 4 * Real.sqrt 48 * (1/(parameter : ℝ)^41) + 64/(parameter : ℝ)^37 := by field_simp; ring
    _ ≤ 4 * Real.sqrt 48 * (1/(parameter : ℝ)^37) + 64/(parameter : ℝ)^37 := by gcongr
    _ = _ := by ring

end
end AFT.GaussianSource
