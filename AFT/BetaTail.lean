import AFT.BetaReference
import AFT.HistogramTail

/-!
# Quantitative lower tail of the actual beta reference

The cutoff error is the integral proved in `BetaReference`, not an abstract
negligible-error parameter. We bound that integral directly, including the
growing beta shape parameter used by the V7 sampler.
-/

namespace AFT.BetaReference

open MeasureTheory

/-- Dropping the factor `(1-x)^n` and integrating the remaining monomial
gives an exact binomial-coefficient upper bound for the lower tail. -/
theorem lower_tail_le_choose (K n : ℕ) (cutoff : ℝ)
    (hc : 0 ≤ cutoff) (hc1 : cutoff ≤ 1) :
    (∫ x : ℝ in (0 : ℝ)..cutoff, density K n x) ≤
      ((K + n + 1).choose (K + 1) : ℝ) * cutoff ^ (K + 1) := by
  let coefficient : ℝ := ((K + n + 1).factorial : ℝ) /
    (K.factorial * n.factorial)
  have hcoeff : 0 ≤ coefficient := by dsimp [coefficient]; positivity
  have hbound : (∫ x : ℝ in (0 : ℝ)..cutoff, density K n x) ≤
      ∫ x : ℝ in (0 : ℝ)..cutoff, coefficient * x ^ K := by
    apply intervalIntegral.integral_mono_on hc
      (by unfold density; exact (by fun_prop : Continuous _).intervalIntegrable _ _)
      (by exact (by fun_prop : Continuous _).intervalIntegrable _ _)
    intro x hx
    have hx1 : x ≤ 1 := hx.2.trans hc1
    have hpow : (1 - x) ^ n ≤ 1 := pow_le_one₀ (sub_nonneg.mpr hx1) (by linarith [hx.1])
    exact (mul_le_mul_of_nonneg_left hpow
      (mul_nonneg hcoeff (pow_nonneg hx.1 _))).trans_eq (mul_one _)
  have heq : (∫ x : ℝ in (0 : ℝ)..cutoff, coefficient * x ^ K) =
      ((K + n + 1).choose (K + 1) : ℝ) * cutoff ^ (K + 1) := by
    rw [intervalIntegral.integral_const_mul coefficient (fun x : ℝ => x ^ K), integral_pow]
    rw [Nat.cast_choose ℝ (show K + 1 ≤ K + n + 1 by omega)]
    have hsub : K + n + 1 - (K + 1) = n := by omega
    rw [hsub]
    simp only [Nat.factorial_succ K, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    dsimp [coefficient]
    have hK : (K.factorial : ℝ) ≠ 0 := by positivity
    have hn : (n.factorial : ℝ) ≠ 0 := by positivity
    have hK1 : (K : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    simp only [zero_pow (Nat.succ_ne_zero K), sub_zero]
  exact hbound.trans_eq heq

/-- Nonasymptotic exponential lower-tail bound, obtained from the true beta
integral and the elementary factorial bound. -/
theorem lower_tail_le_power (K n : ℕ) (cutoff : ℝ)
    (hc : 0 ≤ cutoff) (hc1 : cutoff ≤ 1) :
    (∫ x : ℝ in (0 : ℝ)..cutoff, density K n x) ≤
      (Real.exp 1 * (K + n + 1 : ℕ) * cutoff / (K + 1 : ℕ)) ^ (K + 1) := by
  have hf : (0 : ℝ) < (K + 1).factorial := by positivity
  have hk : (0 : ℝ) < (K + 1 : ℕ) := by positivity
  have hcN : (0 : ℝ) ≤ (K + n + 1 : ℕ) := by positivity
  have hfac := HistogramTail.factorial_exp_lower (K + 1)
  have hcoeff : ((K + n + 1).choose (K + 1) : ℝ) ≤
      (Real.exp 1 * (K + n + 1 : ℕ) / (K + 1 : ℕ)) ^ (K + 1) := by
    calc
      _ ≤ ((K + n + 1 : ℕ) : ℝ) ^ (K + 1) / (K + 1).factorial :=
        Nat.choose_le_pow_div _ _
      _ ≤ _ := by
        rw [div_pow, mul_pow]
        apply (div_le_div_iff₀ hf (pow_pos hk _)).mpr
        have h := mul_le_mul_of_nonneg_left hfac (pow_nonneg hcN (K + 1))
        nlinarith [h]
  calc
    _ ≤ ((K + n + 1).choose (K + 1) : ℝ) * cutoff ^ (K + 1) :=
      lower_tail_le_choose K n cutoff hc hc1
    _ ≤ (Real.exp 1 * (K + n + 1 : ℕ) / (K + 1 : ℕ)) ^ (K + 1) *
        cutoff ^ (K + 1) := mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hc _)
    _ = _ := by rw [← mul_pow]; congr 1; ring

/-- Any numerical parameter check reducing the normalized cutoff below a
given base transfers directly to the actual reference error. -/
theorem lower_tail_le_geometric (K n : ℕ) (cutoff base : ℝ)
    (hc : 0 ≤ cutoff) (hc1 : cutoff ≤ 1)
    (hsmall : Real.exp 1 * (K + n + 1 : ℕ) * cutoff / (K + 1 : ℕ) ≤ base) :
    (∫ x : ℝ in (0 : ℝ)..cutoff, density K n x) ≤ base ^ (K + 1) := by
  exact (lower_tail_le_power K n cutoff hc hc1).trans
    (pow_le_pow_left₀ (by positivity) hsmall _)

end AFT.BetaReference
