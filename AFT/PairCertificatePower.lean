import AFT.V7PairCertificateBounds
import AFT.ActivationSharp

/-! # The complete finite pair certificate has the V7 error exponent -/

namespace AFT.GaussianSource

open scoped BigOperators

noncomputable def pairCertificateConstant : ℝ := 4 * (4 * 12 ^ 30 + 144 * 77 + 93600)

theorem pair_certificate_scalar_square (parameter modulus denominator size depth : ℝ)
    (hp : 1 ≤ parameter) (hq : parameter ^ 40 ≤ modulus) (hq' : modulus ≤ 2 * parameter ^ 40)
    (hd : modulus / 2 ≤ denominator) (hdepth : 0 ≤ depth) (hdepth' : depth ≤ 77 * parameter ^ 3)
    (hk : modulus / 2 ≤ size) (hsize : size = modulus - 2 * depth) :
    (modulus * (12 / parameter) ^ 15 * Real.sqrt (1 / (parameter ^ 32 * denominator)) +
      modulus * Real.sqrt (1 / size - 1 / modulus) *
        (2 * Real.sqrt (1 / denominator) + Real.sqrt (1 / size) + Real.sqrt (1 / modulus)) +
      15 * Real.sqrt (416 / parameter ^ 21) +
      modulus * Real.sqrt (4 * depth / (parameter ^ 32 * denominator ^ 2))) ^ 2 ≤
      pairCertificateConstant / parameter ^ 21 := by
  have hp0 : 0 < parameter := by linarith
  have hq0 : 0 < modulus := lt_of_lt_of_le (by positivity) hq
  have hd0 : 0 < denominator := lt_of_lt_of_le (half_pos hq0) hd
  have hk0 : 0 < size := lt_of_lt_of_le (half_pos hq0) hk
  have hdiff : 0 ≤ 1 / size - 1 / modulus := by
    apply sub_nonneg.mpr
    exact one_div_le_one_div_of_le hk0 (by linarith)
  have hpow (exponent : ℕ) (he : 21 ≤ exponent) : (1 : ℝ) / parameter ^ exponent ≤ 1 / parameter ^ 21 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ hp he)
  have hfirst : (modulus * (12 / parameter) ^ 15 * Real.sqrt (1 / (parameter ^ 32 * denominator))) ^ 2 ≤
      (4 * 12 ^ 30) / parameter ^ 21 := by
    rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 1 / (parameter ^ 32 * denominator))]
    calc
      _ ≤ (modulus * (12 / parameter) ^ 15) ^ 2 * (1 / (parameter ^ 32 * (modulus / 2))) := by gcongr
      _ = (2 * 12 ^ 30) * modulus / parameter ^ 62 := by field_simp
      _ ≤ (2 * 12 ^ 30) * (2 * parameter ^ 40) / parameter ^ 62 := by gcongr
      _ = (4 * 12 ^ 30) * (1 / parameter ^ 22) := by field_simp; ring
      _ ≤ (4 * 12 ^ 30) * (1 / parameter ^ 21) := mul_le_mul_of_nonneg_left (hpow 22 (by decide)) (by positivity)
      _ = _ := by ring
  have href : (modulus * Real.sqrt (1 / size - 1 / modulus) *
      (2 * Real.sqrt (1 / denominator) + Real.sqrt (1 / size) + Real.sqrt (1 / modulus))) ^ 2 ≤
      (128 * 77) / parameter ^ 21 := by
    have hdrec : 1 / denominator ≤ 2 / modulus := by
      apply (div_le_div_iff₀ hd0 hq0).mpr
      linarith
    calc
      _ ≤ (modulus * (Real.sqrt (1 / size - 1 / modulus) *
        (2 * Real.sqrt (2 / modulus) + Real.sqrt (1 / size) + Real.sqrt (1 / modulus)))) ^ 2 := by
          rw [← mul_assoc]
          gcongr
      _ ≤ 128 * depth / modulus := SafePair.core_reference_scaled_square_le modulus size depth hq0 hdepth hk hsize
      _ ≤ 128 * (77 * parameter ^ 3) / parameter ^ 40 := by gcongr
      _ = (128 * 77) * (1 / parameter ^ 37) := by field_simp
      _ ≤ (128 * 77) * (1 / parameter ^ 21) := mul_le_mul_of_nonneg_left (hpow 37 (by decide)) (by norm_num)
      _ = _ := by ring
  have hsmooth : (15 * Real.sqrt (416 / parameter ^ 21)) ^ 2 = 93600 / parameter ^ 21 := by
    rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 416 / parameter ^ 21)]
    ring
  have hedge : (modulus * Real.sqrt (4 * depth / (parameter ^ 32 * denominator ^ 2))) ^ 2 ≤
      (16 * 77) / parameter ^ 21 := by
    rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 4 * depth / (parameter ^ 32 * denominator ^ 2))]
    calc
      _ ≤ modulus ^ 2 * (4 * depth / (parameter ^ 32 * (modulus / 2) ^ 2)) := by gcongr
      _ = 16 * depth / parameter ^ 32 := by field_simp; ring
      _ ≤ 16 * (77 * parameter ^ 3) / parameter ^ 32 := by gcongr
      _ = (16 * 77) * (1 / parameter ^ 29) := by field_simp
      _ ≤ (16 * 77) * (1 / parameter ^ 21) := mul_le_mul_of_nonneg_left (hpow 29 (by decide)) (by norm_num)
      _ = _ := by ring
  have hfour (a b c d : ℝ) : (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d),
      sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]
  apply (hfour _ _ _ _).trans
  have hh := add_le_add (add_le_add (add_le_add hfirst href) hsmooth.le) hedge
  exact (mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 4)).trans_eq (by unfold pairCertificateConstant; ring)

/-- The exact clipped activation cost preserves the claimed lambda^-2
Hilbert budget; its square is lambda^-4. -/
theorem pair_certificate_activation_square (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (parameter : ℕ) (hp : 1 ≤ parameter) (error : ℝ)
    (herror : error ^ 2 ≤ pairCertificateConstant / (parameter : ℝ) ^ 21) :
    ((v7Activation cutoffScale parameter ^ 2)⁻¹ * error) ^ 2 ≤
      (activationConstant cutoffScale ^ 4 * pairCertificateConstant) / (parameter : ℝ) ^ 4 := by
  have hp0 : (0 : ℝ) < parameter := by exact_mod_cast (by omega : 0 < parameter)
  have ha := activationConstant_pos cutoffScale hscale
  have hrho : 0 < v7Activation cutoffScale parameter :=
    lt_of_lt_of_le (by positivity) (v7Activation_lower_rpow cutoffScale parameter hscale hp)
  have hinv := pow_le_pow_left₀ (inv_nonneg.mpr hrho.le)
    (v7Activation_inverse_upper cutoffScale parameter hscale hp) 4
  have hpowers : ((parameter : ℝ) ^ (17 / 4 : ℝ)) ^ 4 = (parameter : ℝ) ^ 17 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
    norm_num
    exact Real.rpow_natCast _ 17
  calc
    _ = (v7Activation cutoffScale parameter)⁻¹ ^ 4 * error ^ 2 := by rw [mul_pow, inv_pow]; ring
    _ ≤ (activationConstant cutoffScale * (parameter : ℝ) ^ (17 / 4 : ℝ)) ^ 4 *
        (pairCertificateConstant / (parameter : ℝ) ^ 21) :=
      mul_le_mul hinv herror (sq_nonneg _) (by positivity)
    _ = _ := by rw [mul_pow, hpowers]; field_simp

end AFT.GaussianSource
