import AFT.RootANOVAParameters

/-!
# The actual V7 root conditioning probability
-/

namespace AFT.GaussianSource

open Filter
open scoped BigOperators Classical Topology

theorem sumModel_center_upper (width : ℝ) (population : ℕ) (hw : 0 < width) (hn : 0 < population) :
    sumModel width (realNormalizer width) population 0 ≤
      1 / (Real.sqrt (population : ℝ) * width) := by
  have hz : 0 < realNormalizer width := zero_lt_one.trans_le (realNormalizer_ge_one width hw)
  have hzw : width ≤ realNormalizer width := by
    rw [realNormalizer_duality width hw]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (realNormalizer_ge_one (1 / width) (by positivity)) hw.le
  have hratio : width / realNormalizer width ≤ 1 := (div_le_one hz).mpr hzw
  have hpow : (width / realNormalizer width) ^ population ≤ 1 :=
    pow_le_one₀ (by positivity) hratio
  unfold sumModel
  simp only [Int.cast_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_div, Real.exp_zero, mul_one]
  exact div_le_div_of_nonneg_right hpow (by positivity)

/-- Both sides of the root-probability comparison, with explicit finite
Poisson/clipping budgets. -/
theorem rootProbability_bounds (width thetaBound : ℝ) (cutoff population : ℕ)
    (hw : 0 < width) (hn : 0 < population) (ht0 : 0 ≤ thetaBound)
    (ht : thetaError (width / Real.sqrt 2) ≤ thetaBound)
    (hsmall : (population : ℝ) * thetaBound ≤ 1)
    (herr : rootSumError width thetaBound cutoff (population - 1) 0 ≤ 1 / 2) :
    (rootProbability width cutoff population 0)⁻¹ ≤
        2 * Real.exp 2 * powerWidth width (population - 1) ∧
      rootProbability width cutoff population 0 ≤ 2 / powerWidth width (population - 1) := by
  have hn1 : (1 : ℝ) ≤ population := by exact_mod_cast hn
  have ht1 : thetaBound ≤ 1 := by nlinarith
  have hz : 0 < realNormalizer width := zero_lt_one.trans_le (realNormalizer_ge_one width hw)
  have hmodel := sumModel_pos width (realNormalizer width) population hw hz hn 0
  have herror := abs_le.mp ((rootProbability_model_error width thetaBound cutoff population hw hn
    ht0 ht1 ht 0).trans herr)
  have hlow : (1 / 2) * sumModel width (realNormalizer width) population 0 ≤
      rootProbability width cutoff population 0 := (le_div_iff₀ hmodel).mp (by linarith [herror.1])
  have hupp : rootProbability width cutoff population 0 ≤
      2 * sumModel width (realNormalizer width) population 0 :=
    (div_le_iff₀ hmodel).mp (by linarith [herror.2])
  have hmodelInv := gaussianSumApprox_inv_le width thetaBound (population - 1) 0 hw ht0 ht
    (by simpa only [Nat.sub_add_cancel hn] using hsmall) (by simp [sq_nonneg])
  unfold gaussianSumApprox at hmodelInv
  rw [gaussianSumApprox_model width hw, Nat.sub_add_cancel hn] at hmodelInv
  have hwidth : powerWidth width (population - 1) = Real.sqrt (population : ℝ) * width := by
    rw [powerWidth_eq width hw, Nat.sub_add_cancel hn]
  constructor
  · have hh := one_div_le_one_div_of_le (by positivity : 0 < (1 / 2 : ℝ) *
        sumModel width (realNormalizer width) population 0) hlow
    have heq : 1 / ((1 / 2 : ℝ) * sumModel width (realNormalizer width) population 0) =
        2 * (sumModel width (realNormalizer width) population 0)⁻¹ := by ring
    calc
      _ = 1 / rootProbability width cutoff population 0 := (one_div _).symm
      _ ≤ 1 / ((1 / 2 : ℝ) * sumModel width (realNormalizer width) population 0) := hh
      _ = 2 * (sumModel width (realNormalizer width) population 0)⁻¹ := heq
      _ ≤ _ := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hmodelInv (by norm_num : (0 : ℝ) ≤ 2)
  · rw [hwidth]
    exact hupp.trans (by
      have hh := mul_le_mul_of_nonneg_left (sumModel_center_upper width population hw hn)
        (by norm_num : (0 : ℝ) ≤ 2)
      simpa only [mul_one_div] using hh)

theorem v7_body_powerWidth_bounds (parameter : ℕ) (hp : 2 ≤ parameter) :
    2 * (parameter : ℝ) ^ 31 ≤ powerWidth (v7RootWidth parameter) (Parameters.bodies parameter - 1) ∧
      powerWidth (v7RootWidth parameter) (Parameters.bodies parameter - 1) ≤ 4 * (parameter : ℝ) ^ 31 := by
  have hw : 0 < v7RootWidth parameter := zero_lt_one.trans_le (v7RootWidth_ge_one parameter (by omega))
  have hNp := Parameters.bodies_positive parameter
  have hNlower : parameter ^ 60 ≤ 2 * Parameters.bodies parameter := by
    have hdim := (Parameters.dimension_bounds parameter).1
    rw [Parameters.security_eq parameter hp] at hdim
    have hpop := Parameters.population_identity parameter
    have hh := Parameters.legs_le_half_bodies parameter
    omega
  have hNupper : Parameters.bodies parameter ≤ 2 * parameter ^ 60 := by
    have hdim := (Parameters.dimension_bounds parameter).2
    rw [Parameters.security_eq parameter hp] at hdim
    exact (Nat.sub_le _ _).trans hdim
  have hNlower' : (parameter : ℝ) ^ 60 ≤ 2 * Parameters.bodies parameter := by exact_mod_cast hNlower
  have hNupper' : (Parameters.bodies parameter : ℝ) ≤ 2 * (parameter : ℝ) ^ 60 := by exact_mod_cast hNupper
  have heq : powerWidth (v7RootWidth parameter) (Parameters.bodies parameter - 1) ^ 2 =
      (Parameters.bodies parameter : ℝ) * (8 * (parameter : ℝ) ^ 2) := by
    rw [powerWidth_sq, Nat.sub_add_cancel hNp, v7RootWidth_sq]
  constructor
  · apply (sq_le_sq₀ (by positivity) (powerWidth_pos _ hw _).le).mp
    rw [heq]
    have hh := mul_le_mul_of_nonneg_right hNlower' (by positivity : 0 ≤ 4 * (parameter : ℝ) ^ 2)
    convert hh using 1 <;> ring
  · apply (sq_le_sq₀ (powerWidth_pos _ hw _).le (by positivity)).mp
    rw [heq]
    have hh := mul_le_mul_of_nonneg_right hNupper' (by positivity : 0 ≤ 8 * (parameter : ℝ) ^ 2)
    convert hh using 1
    ring

/-- Explicit `Theta(lambda^(-31))` bounds for the exact clipped integer
zero-sum probability. -/
theorem v7_rootProbability_order :
    ∀ᶠ parameter : ℕ in atTop,
      1 / (8 * Real.exp 2 * (parameter : ℝ) ^ 31) ≤
          rootProbability (v7RootWidth parameter) (v7RootCutoff parameter) (Parameters.bodies parameter) 0 ∧
        rootProbability (v7RootWidth parameter) (v7RootCutoff parameter) (Parameters.bodies parameter) 0 ≤
          1 / (parameter : ℝ) ^ 31 := by
  have hsmall := v7RootThetaBound_negligible.inverse_population_bound Parameters.bodies
    Parameters.bodies_positive (by simpa only [Nat.sub_zero] using bodies_sub_fixed_upper_eventually 0) 1
  have herr := v7RootErrorBound_negligible.tendsto_zero.eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  filter_upwards [hsmall, herr, v7_bodies_rootSumError_envelope_eventually 0 0,
    eventually_ge_atTop 2] with parameter ht he hr hp
  have hw : 0 < v7RootWidth parameter := zero_lt_one.trans_le (v7RootWidth_ge_one parameter (by omega))
  have hNp : (0 : ℝ) < Parameters.bodies parameter := by exact_mod_cast Parameters.bodies_positive parameter
  have ht0 : 0 ≤ v7RootThetaBound parameter := by unfold v7RootThetaBound; positivity
  have hh := rootProbability_bounds (v7RootWidth parameter) (v7RootThetaBound parameter)
    (v7RootCutoff parameter) (Parameters.bodies parameter) hw (Parameters.bodies_positive parameter)
    ht0 (v7RootThetaBound_valid parameter (by omega))
    (by rw [abs_of_nonneg ht0, pow_one] at ht
        have hmul := (le_div_iff₀ hNp).mp ht
        nlinarith)
    (by have hh := (hr 0 (by simp)).trans he.le
        simpa only [Nat.sub_zero] using hh)
  have hwid := v7_body_powerWidth_bounds parameter hp
  have hp0 : (0 : ℝ) < parameter := by exact_mod_cast (by omega : 0 < parameter)
  have hprob := window_root_probability_positive (v7RootWidth parameter) (v7RootCutoff parameter)
    (Parameters.bodies parameter)
  constructor
  · have hinv : (rootProbability (v7RootWidth parameter) (v7RootCutoff parameter)
        (Parameters.bodies parameter) 0)⁻¹ ≤ 8 * Real.exp 2 * (parameter : ℝ) ^ 31 :=
      hh.1.trans (by
        have hscale := mul_le_mul_of_nonneg_left hwid.2 (by positivity : 0 ≤ 2 * Real.exp 2)
        nlinarith)
    have hbound := one_div_le_one_div_of_le (inv_pos.mpr hprob) hinv
    simpa only [one_div, inv_inv] using hbound
  · apply hh.2.trans
    have hl : 0 < 2 * (parameter : ℝ) ^ 31 := by positivity
    have hbound := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) hl hwid.1
    convert hbound using 1
    field_simp

end AFT.GaussianSource
