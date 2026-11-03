import AFT.ActivationParameters
import AFT.GaussianMoments

/-! # The sharp upper activation bound for the actual clipped sources -/

namespace AFT.GaussianSource

open Filter
open scoped Topology

noncomputable section

theorem legFeatureCount_lower (cutoffScale : ℝ) (parameter : ℕ)
    (hscale : 1 ≤ cutoffScale) (hp : 1 ≤ parameter) :
    (parameter : ℝ) ^ (9 / 4 : ℝ) ≤ legFeatureCount cutoffScale parameter := by
  have hp0 : (0 : ℝ) < parameter := by exact_mod_cast (by omega : 0 < parameter)
  have hc0 := legCutoff_positive cutoffScale parameter hscale hp
  have hc : (parameter : ℝ) ^ (9 / 8 : ℝ) ≤ legCutoff cutoffScale parameter := by
    calc
      _ ≤ cutoffScale * (parameter : ℝ) ^ (9 / 8 : ℝ) := by nlinarith [Real.rpow_nonneg hp0.le (9 / 8 : ℝ)]
      _ ≤ _ := Nat.le_ceil _
  have htwice : (legCutoff cutoffScale parameter : ℝ) ≤ (2 * legCutoff cutoffScale parameter - 1 : ℕ) := by
    exact_mod_cast (by omega : legCutoff cutoffScale parameter ≤ 2 * legCutoff cutoffScale parameter - 1)
  have hpow := pow_le_pow_left₀ (Real.rpow_nonneg hp0.le _) (hc.trans htwice) 2
  have heq : ((parameter : ℝ) ^ (9 / 8 : ℝ)) ^ 2 = (parameter : ℝ) ^ (9 / 4 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
    norm_num
  simpa only [heq, legFeatureCount, Nat.cast_pow] using hpow

theorem legCutoff_contains_sources_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) :
    ∀ᶠ parameter : ℕ in atTop,
      ⌊(parameter : ℝ)⌋₊ ≤ legCutoff cutoffScale parameter - 1 ∧
      ⌊10 * (parameter : ℝ)⌋₊ ≤ legCutoff cutoffScale parameter - 1 := by
  have hlarge := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).comp
    tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (11 : ℝ))
  filter_upwards [hlarge, eventually_ge_atTop 1] with parameter hlarge hp
  dsimp only [Function.comp_apply] at hlarge
  have hp' : (1 : ℝ) ≤ parameter := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < parameter := by positivity
  have hpower : (parameter : ℝ) ^ (9 / 8 : ℝ) = (parameter : ℝ) ^ (1 / 8 : ℝ) * parameter := by
    calc
      _ = (parameter : ℝ) ^ ((1 / 8 : ℝ) + 1) := by norm_num
      _ = (parameter : ℝ) ^ (1 / 8 : ℝ) * (parameter : ℝ) ^ (1 : ℝ) := Real.rpow_add hp0 _ _
      _ = _ := by rw [Real.rpow_one]
  have hc : 11 * (parameter : ℝ) ≤ legCutoff cutoffScale parameter := by
    calc
      _ ≤ (parameter : ℝ) ^ (9 / 8 : ℝ) := by rw [hpower]; nlinarith
      _ ≤ cutoffScale * (parameter : ℝ) ^ (9 / 8 : ℝ) := by
        nlinarith [Real.rpow_nonneg hp0.le (9 / 8 : ℝ)]
      _ ≤ _ := Nat.le_ceil _
  have hc' : 11 * parameter ≤ legCutoff cutoffScale parameter := by exact_mod_cast hc
  have hfloor : ⌊10 * (parameter : ℝ)⌋₊ = 10 * parameter := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using Nat.floor_natCast (10 * parameter)
  simp only [Nat.floor_natCast, hfloor]
  constructor <;> omega

/-- This is an estimate on the genuine mark event and two clipped Gaussian
atoms, including the exact quadratic feature count. -/
theorem v7Activation_upper_rpow_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) :
    ∀ᶠ parameter : ℕ in atTop,
      v7Activation cutoffScale parameter ≤
        (Real.exp (2 * Real.pi) / 1000) / (parameter : ℝ) ^ (17 / 4 : ℝ) := by
  filter_upwards [legCutoff_contains_sources_eventually cutoffScale hscale, eventually_ge_atTop 1]
    with parameter hcut hp
  have hp0 : (0 : ℝ) < parameter := by exact_mod_cast (by omega : 0 < parameter)
  have hfirst := windowGaussian_zero_upper (parameter : ℝ) (legCutoff cutoffScale parameter - 1) hp0 hcut.1
  have hsecond := windowGaussian_zero_upper (10 * parameter) (legCutoff cutoffScale parameter - 1)
    (by positivity) hcut.2
  have hf := legFeatureCount_lower cutoffScale parameter hscale hp
  have hfpos : (0 : ℝ) < legFeatureCount cutoffScale parameter :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hp0 _) hf
  have hprod := mul_le_mul hfirst hsecond (windowGaussian_positive _ _ _).le (by positivity)
  have hmark : 1 / (100 * (legFeatureCount cutoffScale parameter : ℝ)) ≤
      1 / (100 * (parameter : ℝ) ^ (9 / 4 : ℝ)) := by
    exact one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hf (by norm_num))
  have hh := mul_le_mul hmark hprod (mul_nonneg (windowGaussian_positive _ _ _).le (windowGaussian_positive _ _ _).le) (by positivity)
  have heq : (parameter : ℝ) ^ (9 / 4 : ℝ) * (parameter : ℝ) ^ 2 =
      (parameter : ℝ) ^ (17 / 4 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hp0]
    norm_num
  change v7Activation cutoffScale parameter ≤ _ at hh
  apply hh.trans_eq
  have hexp : Real.exp (2 * Real.pi) = Real.exp Real.pi ^ 2 := by
    rw [two_mul, Real.exp_add, pow_two]
  rw [hexp, ← heq]
  ring

end

end AFT.GaussianSource
