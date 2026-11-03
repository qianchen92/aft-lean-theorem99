import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic

/-!
# Finite-population factorial comparison for the complete histogram tail

The estimates here cover every degree up to the actual population size. They
are the numerical comparison in reference V7, Lemma 9.17, and do not assume a
Poisson limit or discard degrees comparable to the population size.

`coefficientEnergy k` denotes the squared Hilbert norm of the homogeneous
coefficient tensor. The analytic Fock bound and the identification of these
coefficients with the physical histogram likelihood are separate obligations.
-/

namespace AFT
namespace HistogramTail

open scoped BigOperators

/-- Comparison of descending factorials by multiplying the elementary ratios
`(population - i) / (degree - i) ≥ population / degree`. -/
theorem factorial_power_comparison (population degree : ℕ) (hdegree : degree ≤ population) :
    population ^ degree * degree.factorial ≤
      degree ^ degree * population.descFactorial degree := by
  have hpoint (i : ℕ) (hi : i ∈ Finset.range degree) :
      population * (degree - i) ≤ degree * (population - i) := by
    have hi' : i ≤ degree := Nat.le_of_lt (Finset.mem_range.mp hi)
    have hip : i ≤ population := hi'.trans hdegree
    have hmono : degree * i ≤ population * i := Nat.mul_le_mul_right i hdegree
    rw [Nat.mul_sub, Nat.mul_sub, Nat.mul_comm degree population]
    exact Nat.sub_le_sub_left hmono _
  have hprod := Finset.prod_le_prod' hpoint
  simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
    ← Nat.descFactorial_eq_prod_range, Nat.descFactorial_self] using hprod

/-- The elementary factorial lower bound required here follows directly from
one term in the exponential series. No asymptotic Stirling formula is needed. -/
theorem factorial_exp_lower (degree : ℕ) :
    (degree : ℝ) ^ degree ≤ Real.exp 1 ^ degree * (degree.factorial : ℝ) := by
  have h := Real.pow_div_factorial_le_exp (degree : ℝ) (by positivity) degree
  have hf : (0 : ℝ) < degree.factorial := by positivity
  rw [div_le_iff₀ hf] at h
  simpa only [← Real.exp_nat_mul, mul_one] using h

/-- The exact finite-population lower bound from V7: `(N/e)^k ≤ (N)_k`
for every `k ≤ N`, including `k = N`. -/
theorem descFactorial_exp_lower (population degree : ℕ) (hdegree : degree ≤ population) :
    ((population : ℝ) / Real.exp 1) ^ degree ≤
      (population.descFactorial degree : ℝ) := by
  have hnat := factorial_power_comparison population degree hdegree
  have hcast : (population : ℝ) ^ degree * (degree.factorial : ℝ) ≤
      (degree : ℝ) ^ degree * (population.descFactorial degree : ℝ) := by exact_mod_cast hnat
  have hfac := factorial_exp_lower degree
  have hmul := mul_le_mul_of_nonneg_right hfac
    (show (0 : ℝ) ≤ population.descFactorial degree by positivity)
  have hf : (0 : ℝ) < degree.factorial := by positivity
  have h : (population : ℝ) ^ degree ≤
      Real.exp 1 ^ degree * (population.descFactorial degree : ℝ) := by
    nlinarith [hcast, hmul]
  rw [div_pow]
  exact (div_le_iff₀ (by positivity)).mpr (by simpa [mul_comm] using h)

/-- The population-normalized coefficient weight is at most `e^k` times
its Fock weight. The positive-population condition prevents division by zero. -/
theorem reciprocal_descFactorial_le (population degree : ℕ)
    (hpopulation : 0 < population) (hdegree : degree ≤ population) :
    (1 : ℝ) / (population.descFactorial degree : ℝ) ≤
      Real.exp 1 ^ degree / (population : ℝ) ^ degree := by
  have hp : (0 : ℝ) < population := by exact_mod_cast hpopulation
  have hd : (0 : ℝ) < population.descFactorial degree := by
    exact_mod_cast Nat.descFactorial_pos.mpr hdegree
  have h := descFactorial_exp_lower population degree hdegree
  rw [div_pow] at h
  apply (div_le_div_iff₀ hd (pow_pos hp degree)).mpr
  have hx := (div_le_iff₀ (show (0 : ℝ) < Real.exp 1 ^ degree by positivity)).mp h
  simpa [mul_comm] using hx

/-- Complete finite Fock energy, including the constant and highest terms. -/
noncomputable def fockEnergy (population : ℕ) (radius : ℝ)
    (coefficientEnergy : ℕ → ℝ) : ℝ :=
  ∑ degree ∈ Finset.range (population + 1),
    (degree.factorial : ℝ) * radius ^ (2 * degree) * coefficientEnergy degree /
      (population : ℝ) ^ degree

/-- Exact finite-population weights of the degrees strictly above a cutoff. -/
noncomputable def likelihoodTailEnergy (population cutoff : ℕ)
    (coefficientEnergy : ℕ → ℝ) : ℝ :=
  ∑ degree ∈ (Finset.range (population + 1)).filter (cutoff < ·),
    (degree.factorial : ℝ) * coefficientEnergy degree /
      (population.descFactorial degree : ℝ)

/-- Complete tail comparison, with the exact finite-population denominator.
Every homogeneous coefficient is included; the statement is uniform in the
population and cutoff. The radius is only required to satisfy `radius² ≥ e`. -/
theorem complete_tail_energy_le (population cutoff : ℕ) (radius : ℝ)
    (coefficientEnergy : ℕ → ℝ) (hpopulation : 0 < population)
    (henergy : ∀ degree, 0 ≤ coefficientEnergy degree)
    (hradius : Real.exp 1 ≤ radius ^ 2) :
    likelihoodTailEnergy population cutoff coefficientEnergy ≤
      (Real.exp 1 / radius ^ 2) ^ (cutoff + 1) *
        fockEnergy population radius coefficientEnergy := by
  have hr : 0 < radius ^ 2 := (Real.exp_pos 1).trans_le hradius
  have hrne : radius ≠ 0 := by intro heq; simp [heq] at hr
  have hp : (0 : ℝ) < population := by exact_mod_cast hpopulation
  have hq0 : 0 ≤ Real.exp 1 / radius ^ 2 := by positivity
  have hq1 : Real.exp 1 / radius ^ 2 ≤ 1 := (div_le_one hr).mpr hradius
  let term (degree : ℕ) :=
    (degree.factorial : ℝ) * radius ^ (2 * degree) * coefficientEnergy degree /
      (population : ℝ) ^ degree
  have hterm (degree : ℕ) : 0 ≤ term degree := by
    dsimp [term]
    exact div_nonneg (mul_nonneg (mul_nonneg (by positivity)
      (pow_nonneg (sq_nonneg radius) degree |>.trans_eq (pow_mul radius 2 degree).symm))
      (henergy degree)) (by positivity)
  have hpoint (degree : ℕ)
      (hdegree : degree ∈ (Finset.range (population + 1)).filter (cutoff < ·)) :
      (degree.factorial : ℝ) * coefficientEnergy degree /
          (population.descFactorial degree : ℝ) ≤
        (Real.exp 1 / radius ^ 2) ^ (cutoff + 1) * term degree := by
    have hdegle : degree ≤ population := by
      have := (Finset.mem_filter.mp hdegree).1
      exact Nat.le_of_lt_succ (Finset.mem_range.mp this)
    have hdegcut : cutoff + 1 ≤ degree := (Finset.mem_filter.mp hdegree).2
    have hweight := reciprocal_descFactorial_le population degree hpopulation hdegle
    have hm := mul_le_mul_of_nonneg_left hweight
      (mul_nonneg (show (0 : ℝ) ≤ degree.factorial by positivity) (henergy degree))
    have hpow := pow_le_pow_of_le_one hq0 hq1 hdegcut
    calc
      (degree.factorial : ℝ) * coefficientEnergy degree /
          (population.descFactorial degree : ℝ) ≤
          (degree.factorial : ℝ) * coefficientEnergy degree *
            (Real.exp 1 ^ degree / (population : ℝ) ^ degree) := by
        simpa only [mul_one_div] using hm
      _ = (Real.exp 1 / radius ^ 2) ^ degree * term degree := by
        dsimp [term]
        rw [div_pow, pow_mul]
        field_simp
      _ ≤ (Real.exp 1 / radius ^ 2) ^ (cutoff + 1) * term degree :=
        mul_le_mul_of_nonneg_right hpow (hterm degree)
  calc
    likelihoodTailEnergy population cutoff coefficientEnergy ≤
        ∑ degree ∈ (Finset.range (population + 1)).filter (cutoff < ·),
          (Real.exp 1 / radius ^ 2) ^ (cutoff + 1) * term degree :=
      Finset.sum_le_sum hpoint
    _ ≤ ∑ degree ∈ Finset.range (population + 1),
          (Real.exp 1 / radius ^ 2) ^ (cutoff + 1) * term degree := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro degree _ _
      exact mul_nonneg (pow_nonneg hq0 _) (hterm degree)
    _ = (Real.exp 1 / radius ^ 2) ^ (cutoff + 1) *
        fockEnergy population radius coefficientEnergy := by
      rw [← Finset.mul_sum]
      rfl

/-- The square-root form is exactly the complete Fock-to-tail comparison in
V7. It retains the full finite-population sum, not just any fixed degree. -/
theorem complete_tail_norm_le (population cutoff : ℕ) (radius : ℝ)
    (coefficientEnergy : ℕ → ℝ) (hpopulation : 0 < population)
    (henergy : ∀ degree, 0 ≤ coefficientEnergy degree)
    (hradius0 : 0 ≤ radius) (hradius : Real.exp 1 ≤ radius ^ 2) :
    Real.sqrt (likelihoodTailEnergy population cutoff coefficientEnergy) ≤
      (Real.sqrt (Real.exp 1) / radius) ^ (cutoff + 1) *
        Real.sqrt (fockEnergy population radius coefficientEnergy) := by
  have hq0 : 0 ≤ Real.exp 1 / radius ^ 2 := by positivity
  have hsqrtpow (degree : ℕ) :
      Real.sqrt ((Real.exp 1 / radius ^ 2) ^ degree) =
        (Real.sqrt (Real.exp 1) / radius) ^ degree := by
    induction degree with
    | zero => simp
    | succ degree ih =>
      rw [pow_succ, Real.sqrt_mul (pow_nonneg hq0 degree), ih,
        Real.sqrt_div (le_of_lt (Real.exp_pos 1)), Real.sqrt_sq hradius0, pow_succ]
  have h := Real.sqrt_le_sqrt (complete_tail_energy_le population cutoff radius
    coefficientEnergy hpopulation henergy hradius)
  rwa [Real.sqrt_mul (pow_nonneg hq0 _), hsqrtpow] at h

end HistogramTail
end AFT
