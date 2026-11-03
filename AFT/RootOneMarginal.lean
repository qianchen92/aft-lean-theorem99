import AFT.RootErrorParameters

/-!
# Uniform source comparison for the actual one-coordinate root marginal
-/

namespace AFT.GaussianSource

open scoped BigOperators Classical

/-- The ratio of consecutive continuum comparisons, including the exact
integer-lattice normalizer. -/
theorem sumModel_adjacent_ratio (width normalization : ℝ) (population : ℕ)
    (hw : 0 < width) (hz : 0 < normalization) (hn : 2 ≤ population) (target : ℤ) :
    sumModel width normalization (population - 1) target / sumModel width normalization population 0 =
      (normalization / width) *
        (Real.sqrt (population : ℝ) / Real.sqrt ((population - 1 : ℕ) : ℝ)) *
          Real.exp (-Real.pi * (target : ℝ) ^ 2 / (((population - 1 : ℕ) : ℝ) * width ^ 2)) := by
  have hNp : 0 < Real.sqrt (population : ℝ) := by positivity
  have hN1p : 0 < Real.sqrt ((population - 1 : ℕ) : ℝ) := by
    apply Real.sqrt_pos.mpr
    exact_mod_cast (by omega : 0 < population - 1)
  have hrate : width / normalization ≠ 0 := (div_pos hw hz).ne'
  have hpow : (width / normalization) ^ population =
      (width / normalization) ^ (population - 1) * (width / normalization) := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ population)]
  unfold sumModel
  simp only [Int.cast_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_div, Real.exp_zero, mul_one]
  rw [hpow]
  field_simp

/-- A uniform bound for every output center. -/
theorem sumModel_adjacent_le_two (width normalization : ℝ) (population : ℕ)
    (hw : 0 < width) (hz : 0 < normalization) (hn : 2 ≤ population)
    (hnorm : normalization / width ≤ 5 / 4) (target : ℤ) :
    sumModel width normalization (population - 1) target ≤
      2 * sumModel width normalization population 0 := by
  have ha := sumModel_pos width normalization population hw hz (by omega) 0
  apply (div_le_iff₀ ha).mp
  rw [sumModel_adjacent_ratio width normalization population hw hz hn]
  have hN1 : 0 < ((population - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < population - 1)
  have hsqrtratio : Real.sqrt (population : ℝ) / Real.sqrt ((population - 1 : ℕ) : ℝ) ≤ 3 / 2 := by
    apply (div_le_iff₀ (Real.sqrt_pos.mpr hN1)).mpr
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (by positivity), mul_pow, Real.sq_sqrt hN1.le]
    have hpop : (population : ℝ) ≤ 2 * ((population - 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : population ≤ 2 * (population - 1))
    nlinarith
  have hexp : Real.exp (-Real.pi * (target : ℝ) ^ 2 / (((population - 1 : ℕ) : ℝ) * width ^ 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr Real.pi_pos.le) (sq_nonneg _)) (by positivity))
  have hrat0 : 0 ≤ Real.sqrt (population : ℝ) / Real.sqrt ((population - 1 : ℕ) : ℝ) := by positivity
  have hprod := mul_le_mul hnorm hsqrtratio hrat0 (by norm_num : (0 : ℝ) ≤ 5 / 4)
  have hprod0 : 0 ≤ normalization / width *
      (Real.sqrt (population : ℝ) / Real.sqrt ((population - 1 : ℕ) : ℝ)) := by positivity
  have hh := mul_le_mul_of_nonneg_left hexp hprod0
  nlinarith

/-- The actual finite clipped remaining-sum ratio is bounded by four.
Only explicit scalar error budgets are used. -/
theorem rootProbability_adjacent_le_four (width thetaBound : ℝ) (cutoff population : ℕ)
    (hw : 0 < width) (hn : 2 ≤ population)
    (ht0 : 0 ≤ thetaBound) (ht1 : thetaBound ≤ 1 / 4)
    (ht : thetaError (width / Real.sqrt 2) ≤ thetaBound) (target : ℤ)
    (hroot : rootSumError width thetaBound cutoff (population - 1) 0 ≤ 1 / 4)
    (hmarginal : rootSumError width thetaBound cutoff (population - 1 - 1) target ≤ 1 / 4) :
    rootProbability width cutoff (population - 1) target ≤
      4 * rootProbability width cutoff population 0 ∧
    rootProbability width cutoff (population - 1) target /
      rootProbability width cutoff population 0 ≤ 4 := by
  have hz : 0 < realNormalizer width := zero_lt_one.trans_le (realNormalizer_ge_one width hw)
  have hmodel := sumModel_adjacent_le_two width (realNormalizer width) population hw hz hn
    (by linarith [normalizer_div_width_le width thetaBound hw ht]) target
  have h0 := abs_le.mp ((rootProbability_model_error width thetaBound cutoff population hw
    (by omega) ht0 (by linarith) ht 0).trans hroot)
  have h1 := abs_le.mp ((rootProbability_model_error width thetaBound cutoff (population - 1) hw
    (by omega) ht0 (by linarith) ht target).trans hmarginal)
  have ha0 := sumModel_pos width (realNormalizer width) population hw hz (by omega) 0
  have ha1 := sumModel_pos width (realNormalizer width) (population - 1) hw hz (by omega) target
  have hlower : (3 / 4) * sumModel width (realNormalizer width) population 0 ≤
      rootProbability width cutoff population 0 := by
    apply (le_div_iff₀ ha0).mp
    linarith [h0.1]
  have hupper : rootProbability width cutoff (population - 1) target ≤
      (5 / 4) * sumModel width (realNormalizer width) (population - 1) target := by
    apply (div_le_iff₀ ha1).mp
    linarith [h1.2]
  have hroot0 : 0 < rootProbability width cutoff population 0 :=
    (mul_pos (by norm_num) ha0).trans_le hlower
  have hh : rootProbability width cutoff (population - 1) target ≤
      4 * rootProbability width cutoff population 0 := by nlinarith
  exact ⟨hh, (div_le_iff₀ hroot0).mpr hh⟩

end AFT.GaussianSource
