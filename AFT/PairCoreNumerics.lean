import AFT.PairErrorAssembly

/-! # Numerical cost of the true core reference and deleted edges -/

namespace AFT.SafePair

open scoped BigOperators

/-- The change from the core uniform law to the full uniform law has
squared normalized cost proportional to the deleted fraction. -/
theorem core_reference_scaled_square_le (modulus size depth : ℝ)
    (hq : 0 < modulus) (hd : 0 ≤ depth) (hk : modulus / 2 ≤ size)
    (hsize : size = modulus - 2 * depth) :
    (modulus * (Real.sqrt (1 / size - 1 / modulus) *
      (2 * Real.sqrt (2 / modulus) + Real.sqrt (1 / size) + Real.sqrt (1 / modulus)))) ^ 2 ≤
      128 * depth / modulus := by
  have hk0 : 0 < size := lt_of_lt_of_le (half_pos hq) hk
  have hdiff : 0 ≤ 1 / size - 1 / modulus := by
    apply sub_nonneg.mpr
    exact one_div_le_one_div_of_le hk0 (by linarith)
  have hsmall : 1 / size ≤ 2 / modulus := by
    apply (div_le_div_iff₀ hk0 hq).mpr
    linarith
  have hone : 1 / modulus ≤ 2 / modulus := by gcongr; norm_num
  have hroot := Real.sqrt_le_sqrt hsmall
  have honeRoot := Real.sqrt_le_sqrt hone
  have hs : 0 ≤ 2 * Real.sqrt (2 / modulus) + Real.sqrt (1 / size) + Real.sqrt (1 / modulus) := by positivity
  have hsum : 2 * Real.sqrt (2 / modulus) + Real.sqrt (1 / size) + Real.sqrt (1 / modulus) ≤
      4 * Real.sqrt (2 / modulus) := by linarith
  have hsum2 := (sq_le_sq₀ hs (by positivity : 0 ≤ 4 * Real.sqrt (2 / modulus))).mpr hsum
  rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 / modulus)] at hsum2
  have hdiffEq : 1 / size - 1 / modulus = 2 * depth / (size * modulus) := by
    field_simp
    nlinarith
  have hdiffBound : 1 / size - 1 / modulus ≤ 4 * depth / modulus ^ 2 := by
    rw [hdiffEq]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hk (by positivity : 0 ≤ 2 * depth * modulus)]
  rw [mul_pow, mul_pow, Real.sq_sqrt hdiff]
  calc
    _ ≤ modulus ^ 2 * ((4 * depth / modulus ^ 2) * (16 * (2 / modulus))) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg modulus)
      exact mul_le_mul hdiffBound (by norm_num at hsum2 ⊢; exact hsum2) (sq_nonneg _) (by positivity)
    _ = _ := by field_simp; ring

end AFT.SafePair
