import AFT.RationalGaussianProgram
import AFT.RationalWindowGaussian

/-! # Polynomial iteration lengths for the actual root Gaussian program

These bounds describe the finite series lengths and integer exponents of the
executable rational program. They do not identify rational arithmetic with
constant-cost machine operations.
-/

namespace AFT.RationalNumerics

open scoped BigOperators

def gaussianPiPrecision (squaredWidth : ℚ) (point : ℤ) (bits : ℕ) : ℕ :=
  bits + gaussianGuard squaredWidth point + 1

def gaussianExpScale (squaredWidth : ℚ) (point : ℤ) (bits : ℕ) : ℕ :=
  expScale (piApprox (gaussianPiPrecision squaredWidth point bits) *
    gaussianRatio squaredWidth point)

def gaussianTaylorTerms (squaredWidth : ℚ) (point : ℤ) (bits : ℕ) : ℕ :=
  bits + gaussianExpScale squaredWidth point bits + 2

theorem gaussianApprox_eq_series (squaredWidth : ℚ) (point : ℤ) (bits : ℕ) :
    gaussianApprox squaredWidth point bits =
      (expSum
        (max (piApprox (gaussianPiPrecision squaredWidth point bits) *
          gaussianRatio squaredWidth point) 0 /
          (gaussianExpScale squaredWidth point bits : ℚ))
        (gaussianTaylorTerms squaredWidth point bits))⁻¹ ^
          gaussianExpScale squaredWidth point bits := by
  have hterms : bits + 1 + gaussianExpScale squaredWidth point bits + 1 =
      gaussianTaylorTerms squaredWidth point bits := by unfold gaussianTaylorTerms; omega
  change (expSum _ (bits + 1 + gaussianExpScale squaredWidth point bits + 1))⁻¹ ^
    gaussianExpScale squaredWidth point bits = _
  rw [hterms]
  rfl

noncomputable section

theorem piApprox_le_five (bits : ℕ) : piApprox bits ≤ 5 := by
  have hp := (abs_le.mp (piApprox_error bits)).2
  have hden : (1 : ℝ) ≤ 2 ^ bits := one_le_pow₀ (by norm_num)
  have he : 1 / (2 : ℝ)^bits ≤ 1 := (div_le_one (by positivity)).mpr hden
  have hh : (piApprox bits : ℝ) ≤ 5 := by linarith [Real.pi_lt_four]
  exact_mod_cast hh

theorem actual_root_gaussianRatio_bounds (parameter : ℕ) (hn : 2 ≤ parameter)
    (point : GaussianSource.Window (3 * parameter ^ 2 - 1)) :
    0 ≤ gaussianRatio (8 * (parameter : ℚ)^2) point ∧
      gaussianRatio (8 * (parameter : ℚ)^2) point ≤ 2 * (parameter : ℚ)^2 := by
  have hn0 : (0 : ℚ) < parameter := by exact_mod_cast (show 0 < parameter by omega)
  have hwidth : (0 : ℚ) < 8 * (parameter : ℚ)^2 := by positivity
  refine ⟨div_nonneg (sq_nonneg _) hwidth.le, ?_⟩
  have hp := Finset.mem_Icc.mp point.property
  have hcut : ((3 * parameter ^ 2 - 1 : ℕ) : ℚ) ≤ 3 * (parameter : ℚ)^2 := by
    exact_mod_cast (Nat.sub_le (3 * parameter ^ 2) 1)
  have hlo : -((3 * parameter ^ 2 - 1 : ℕ) : ℚ) ≤ (point.val : ℚ) := by
    exact_mod_cast hp.1
  have hhi : (point.val : ℚ) ≤ ((3 * parameter ^ 2 - 1 : ℕ) : ℚ) := by
    exact_mod_cast hp.2
  have hprod := mul_nonneg (show 0 ≤ (point.val : ℚ) + 3 * (parameter : ℚ)^2 by linarith)
    (show 0 ≤ 3 * (parameter : ℚ)^2 - (point.val : ℚ) by linarith)
  unfold gaussianRatio
  apply (div_le_iff₀ hwidth).mpr
  nlinarith [sq_nonneg ((parameter : ℚ)^2)]

theorem actual_root_gaussianGuard_le (parameter : ℕ) (hn : 2 ≤ parameter)
    (point : GaussianSource.Window (3 * parameter ^ 2 - 1)) :
    gaussianGuard (8 * (parameter : ℚ)^2) point ≤ 2 * parameter ^ 2 := by
  apply Nat.ceil_le.mpr
  simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using
    (actual_root_gaussianRatio_bounds parameter hn point).2

theorem actual_root_gaussianExpScale_le (parameter : ℕ) (hn : 2 ≤ parameter)
    (point : GaussianSource.Window (3 * parameter ^ 2 - 1)) (bits : ℕ) :
    gaussianExpScale (8 * (parameter : ℚ)^2) point bits ≤ 21 * parameter ^ 2 := by
  have hratio := actual_root_gaussianRatio_bounds parameter hn point
  have harg : piApprox (gaussianPiPrecision (8 * (parameter : ℚ)^2) point bits) *
      gaussianRatio (8 * (parameter : ℚ)^2) point ≤ 10 * (parameter : ℚ)^2 := by
    have hh := mul_le_mul_of_nonneg_right
      (piApprox_le_five (gaussianPiPrecision (8 * (parameter : ℚ)^2) point bits)) hratio.1
    nlinarith [hratio.2]
  have hmax : max (piApprox (gaussianPiPrecision (8 * (parameter : ℚ)^2) point bits) *
      gaussianRatio (8 * (parameter : ℚ)^2) point) 0 ≤ 10 * (parameter : ℚ)^2 :=
    max_le harg (by positivity)
  have hceil : ⌈max (piApprox (gaussianPiPrecision (8 * (parameter : ℚ)^2) point bits) *
      gaussianRatio (8 * (parameter : ℚ)^2) point) 0⌉₊ ≤ 10 * parameter ^ 2 := by
    apply Nat.ceil_le.mpr
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using hmax
  have hn2 : 1 ≤ parameter ^ 2 := by nlinarith
  unfold gaussianExpScale expScale
  omega

/-- Each of the two pi series has at most `14 n²` terms, the exponential
Taylor series has at most `32 n²` terms, and its final exponent is at most
`21 n²`. These are the lengths used by the actual root-window program. -/
theorem actual_root_gaussian_resources (parameter : ℕ) (hn : 2 ≤ parameter)
    (point : GaussianSource.Window (3 * parameter ^ 2 - 1))
    (bits : ℕ) (hbits : bits ≤ 10 * parameter ^ 2) :
    gaussianGuard (8 * (parameter : ℚ)^2) point ≤ 2 * parameter ^ 2 ∧
    gaussianPiPrecision (8 * (parameter : ℚ)^2) point bits ≤ 13 * parameter ^ 2 ∧
    gaussianPiPrecision (8 * (parameter : ℚ)^2) point bits + 3 ≤ 14 * parameter ^ 2 ∧
    gaussianExpScale (8 * (parameter : ℚ)^2) point bits ≤ 21 * parameter ^ 2 ∧
    gaussianTaylorTerms (8 * (parameter : ℚ)^2) point bits ≤ 32 * parameter ^ 2 := by
  have hg := actual_root_gaussianGuard_le parameter hn point
  have hs := actual_root_gaussianExpScale_le parameter hn point bits
  have hn2 : 4 ≤ parameter ^ 2 := by nlinarith
  refine ⟨hg, ?_, ?_, hs, ?_⟩
  · unfold gaussianPiPrecision
    omega
  · unfold gaussianPiPrecision
    omega
  · unfold gaussianTaylorTerms
    omega

theorem actual_root_windowApproxPrecision_le (parameter : ℕ) (hn : 2 ≤ parameter)
    (bits : ℕ) (hbits : bits ≤ 3 * parameter ^ 2) :
    windowApproxPrecision (3 * parameter ^ 2 - 1) bits ≤ 10 * parameter ^ 2 := by
  have hn2 : 4 ≤ parameter ^ 2 := by nlinarith
  unfold windowApproxPrecision
  omega

/-- Normalization's guard digits still fit the preceding quadratic bounds. -/
theorem actual_root_window_gaussian_resources (parameter : ℕ) (hn : 2 ≤ parameter)
    (point : GaussianSource.Window (3 * parameter ^ 2 - 1))
    (bits : ℕ) (hbits : bits ≤ 3 * parameter ^ 2) :
    gaussianGuard (8 * (parameter : ℚ)^2) point ≤ 2 * parameter ^ 2 ∧
    gaussianPiPrecision (8 * (parameter : ℚ)^2) point
      (windowApproxPrecision (3 * parameter ^ 2 - 1) bits) ≤ 13 * parameter ^ 2 ∧
    gaussianPiPrecision (8 * (parameter : ℚ)^2) point
      (windowApproxPrecision (3 * parameter ^ 2 - 1) bits) + 3 ≤ 14 * parameter ^ 2 ∧
    gaussianExpScale (8 * (parameter : ℚ)^2) point
      (windowApproxPrecision (3 * parameter ^ 2 - 1) bits) ≤ 21 * parameter ^ 2 ∧
    gaussianTaylorTerms (8 * (parameter : ℚ)^2) point
      (windowApproxPrecision (3 * parameter ^ 2 - 1) bits) ≤ 32 * parameter ^ 2 :=
  actual_root_gaussian_resources parameter hn point _
    (actual_root_windowApproxPrecision_le parameter hn bits hbits)

/-- Summing the lengths of the two pi series and the exponential series over
every atom of the actual root window gives at most `360 n⁴` terms. -/
theorem actual_root_window_series_terms_le (parameter : ℕ) (hn : 2 ≤ parameter)
    (bits : ℕ) (hbits : bits ≤ 3 * parameter ^ 2) :
    (∑ point : GaussianSource.Window (3 * parameter ^ 2 - 1),
      (2 * (gaussianPiPrecision (8 * (parameter : ℚ)^2) point
        (windowApproxPrecision (3 * parameter ^ 2 - 1) bits) + 3) +
      gaussianTaylorTerms (8 * (parameter : ℚ)^2) point
        (windowApproxPrecision (3 * parameter ^ 2 - 1) bits))) ≤ 360 * parameter ^ 4 := by
  have hp (point : GaussianSource.Window (3 * parameter ^ 2 - 1)) :
      2 * (gaussianPiPrecision (8 * (parameter : ℚ)^2) point
        (windowApproxPrecision (3 * parameter ^ 2 - 1) bits) + 3) +
      gaussianTaylorTerms (8 * (parameter : ℚ)^2) point
        (windowApproxPrecision (3 * parameter ^ 2 - 1) bits) ≤ 60 * parameter ^ 2 := by
    have hh := actual_root_window_gaussian_resources parameter hn point bits hbits
    omega
  have hcard : Fintype.card (GaussianSource.Window (3 * parameter ^ 2 - 1)) ≤
      6 * parameter ^ 2 := by
    rw [← Fintype.card_congr (FiniteConvolutionProgram.windowIndexEquiv _), Fintype.card_fin]
    have hn2 : 4 ≤ parameter ^ 2 := by nlinarith
    omega
  calc
    _ ≤ ∑ _point : GaussianSource.Window (3 * parameter ^ 2 - 1), 60 * parameter ^ 2 :=
      Finset.sum_le_sum (fun point _ => hp point)
    _ = Fintype.card (GaussianSource.Window (3 * parameter ^ 2 - 1)) * (60 * parameter ^ 2) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id]
    _ ≤ (6 * parameter ^ 2) * (60 * parameter ^ 2) := Nat.mul_le_mul_right _ hcard
    _ = _ := by ring

end
end AFT.RationalNumerics
