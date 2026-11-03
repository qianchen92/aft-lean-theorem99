import AFT.CanonicalTaylor
import AFT.GaussianMoments

/-!
# Product exponential moments for the root remainder

All expectations are finite sums under the explicitly specified product law.
The estimates retain the fixed root order and do not introduce a factor
depending on the root alphabet's cardinality.
-/

namespace AFT

open scoped BigOperators Classical

namespace FiniteDist

variable {α ι : Type*} [Fintype α] [Fintype ι]

theorem expectation_exp_sum (p : ι → FiniteDist α) (value : ι → α → ℝ) :
    (independent p).expectation (fun x => Real.exp (∑ i, value i (x i))) =
      ∏ i, (p i).expectation (fun a => Real.exp (value i a)) := by
  unfold expectation independent
  simp only [Real.exp_sum, ← Finset.prod_mul_distrib]
  rw [Fintype.prod_sum]

theorem expectation_exp_sum_le (p : ι → FiniteDist α) (value : ι → α → ℝ)
    (bound : ℝ) (hbound : ∀ i, (p i).expectation (fun a => Real.exp (value i a)) ≤ bound) :
    (independent p).expectation (fun x => Real.exp (∑ i, value i (x i))) ≤
      bound ^ Fintype.card ι := by
  rw [expectation_exp_sum]
  simpa only [Finset.prod_const, Finset.card_univ] using Finset.prod_le_prod
    (fun i _ => Finset.sum_nonneg fun a _ => mul_nonneg ((p i).nonneg a) (Real.exp_pos _).le)
    (fun i _ => hbound i)

end FiniteDist

/-- A polynomial moment times a smaller exponential is dominated by a
single exponential-square moment, with an explicit fixed-order constant. -/
theorem power_exp_le_larger_exp (size rate parameter : ℝ) (degree : ℕ)
    (hsize : 0 ≤ size) (hparameter : 0 < parameter)
    (hsmall : 4 * rate ≤ parameter) :
    size ^ degree * Real.exp (2 * rate * size) ≤
      ((degree.factorial : ℝ) / (parameter / 2) ^ degree) * Real.exp (parameter * size) := by
  have hc : 0 < parameter / 2 := by positivity
  have hf : (0 : ℝ) < degree.factorial := by positivity
  have hpow := Real.pow_div_factorial_le_exp (parameter / 2 * size) (mul_nonneg hc.le hsize) degree
  have hp : size ^ degree ≤ ((degree.factorial : ℝ) / (parameter / 2) ^ degree) *
      Real.exp (parameter / 2 * size) := by
    rw [mul_pow] at hpow
    have hh := (div_le_iff₀ hf).mp hpow
    have hh' : size ^ degree ≤ (Real.exp (parameter / 2 * size) * (degree.factorial : ℝ)) /
        (parameter / 2) ^ degree :=
      (le_div_iff₀ (pow_pos hc degree)).mpr (by nlinarith [hh])
    convert hh' using 1
    ring
  have he : Real.exp (2 * rate * size) ≤ Real.exp (parameter / 2 * size) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) hsize)
  calc
    _ ≤ (((degree.factorial : ℝ) / (parameter / 2) ^ degree) *
        Real.exp (parameter / 2 * size)) * Real.exp (parameter / 2 * size) :=
      mul_le_mul hp he (Real.exp_pos _).le (by positivity)
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

/-- Uniform pointwise domination for the exact Taylor remainder. -/
theorem quadratic_remainder_moment_bound (exponent size rate parameter : ℝ) (order : ℕ)
    (hsize : 0 ≤ size) (hrate : 0 ≤ rate) (hparameter : 0 < parameter)
    (hsmall : 4 * rate ≤ parameter) (hexponent : |exponent| ≤ rate * size) :
    (|exponent| ^ order * Real.exp |exponent|) ^ 2 ≤
      rate ^ (2 * order) * (((2 * order).factorial : ℝ) / (parameter / 2) ^ (2 * order)) *
        Real.exp (parameter * size) := by
  have hbound := power_exp_le_larger_exp size rate parameter (2 * order)
    hsize hparameter hsmall
  calc
    _ = |exponent| ^ (2 * order) * Real.exp (2 * |exponent|) := by
      rw [mul_pow, ← pow_mul, ← Real.exp_nat_mul]
      simp only [Nat.cast_ofNat, Nat.mul_comm]
    _ ≤ (rate * size) ^ (2 * order) * Real.exp (2 * (rate * size)) := by
      gcongr
    _ = rate ^ (2 * order) * (size ^ (2 * order) * Real.exp (2 * rate * size)) := by
      rw [mul_pow, mul_assoc, mul_assoc 2 rate size]
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hbound (pow_nonneg hrate _)

namespace Hoeffding

variable {α ι : Type*} [Fintype α] [Fintype ι]

/-- A fixed-order bound for the actual canonical exponential, obtained from
coordinate exponential-square moments and the proved Taylor cancellation. -/
theorem projection_quadratic_exp_moment_bound (p : ι → FiniteDist α)
    (hp : ∀ i a, 0 < (p i).weight a) (S : Finset ι) (value : ι → α → ℝ)
    (quadratic : MvPolynomial ι ℝ) (hdegree : quadratic.totalDegree ≤ 2)
    (order : ℕ) (horder : ∀ j < order, 2 * j < S.card)
    (rate parameter bound : ℝ) (hrate : 0 ≤ rate) (hparameter : 0 < parameter)
    (hsmall : 4 * rate ≤ parameter)
    (hexponent : ∀ x : ι → α, |MvPolynomial.eval (fun i => value i (x i)) quadratic| ≤
      rate * ∑ i, value i (x i) ^ 2)
    (hmoment : ∀ i, (p i).expectation (fun a => Real.exp (parameter * value i a ^ 2)) ≤ bound) :
    (FiniteDist.independent p).l2Sq (projection p S (fun x =>
      Real.exp (MvPolynomial.eval (fun i => value i (x i)) quadratic))) ≤
      rate ^ (2 * order) * (((2 * order).factorial : ℝ) / (parameter / 2) ^ (2 * order)) *
        bound ^ Fintype.card ι := by
  apply (projection_quadratic_exp_bound p hp S value quadratic hdegree order horder).trans
  let constant := rate ^ (2 * order) *
    (((2 * order).factorial : ℝ) / (parameter / 2) ^ (2 * order))
  have hc : 0 ≤ constant := by dsimp [constant]; positivity
  calc
    _ ≤ constant * (FiniteDist.independent p).expectation
        (fun x => Real.exp (∑ i, parameter * value i (x i) ^ 2)) := by
      unfold FiniteDist.expectation
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro x _
      have hx := quadratic_remainder_moment_bound
        (MvPolynomial.eval (fun i => value i (x i)) quadratic)
        (∑ i, value i (x i) ^ 2) rate parameter order
        (Finset.sum_nonneg fun i _ => sq_nonneg _) hrate hparameter hsmall (hexponent x)
      rw [Finset.mul_sum] at hx
      have hh := mul_le_mul_of_nonneg_left hx ((FiniteDist.independent p).nonneg x)
      simpa only [constant, mul_assoc, mul_left_comm] using hh
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (FiniteDist.expectation_exp_sum_le p (fun i a => parameter * value i a ^ 2) bound hmoment) hc

end Hoeffding

end AFT
