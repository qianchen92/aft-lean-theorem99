import Mathlib

/-!
# Finite correction identities used by reference V7

These are algebraic and scalar analytic results. They do not assert the
certificate bounds or the complete histogram tail estimates of Section 9.
-/

namespace AFT

open scoped BigOperators

section FiniteInverse

variable {R : Type*} [Ring R]

/-- The finite Neumann correction in `eq:accuracy-finite-weight`. -/
def finiteCorrection (error : R) (depth : ℕ) : R :=
  ∑ index ∈ Finset.range (depth + 1), (-error) ^ index

/-- The exact residual identity; valid also for noncommutative operator rings. -/
theorem finiteCorrection_residual (error : R) (depth : ℕ) :
    (1 + error) * finiteCorrection error depth = 1 - (-error) ^ (depth + 1) := by
  induction depth with
  | zero => simp [finiteCorrection]
  | succ depth ih =>
    have hs : finiteCorrection error (depth + 1) =
        finiteCorrection error depth + (-error) ^ (depth + 1) := by
      simp only [finiteCorrection, Finset.sum_range_succ]
    rw [hs, mul_add, ih, pow_succ (-error) (depth + 1)]
    have hc : error * (-error) ^ (depth + 1) =
        (-error) ^ (depth + 1) * error := by
      have h := Commute.self_pow (-error) (depth + 1)
      simpa only [Commute, SemiconjBy, neg_mul, mul_neg, neg_inj] using h
    rw [one_add_mul, hc, mul_neg]
    abel

/-- Applying the finite correction to an input certificate leaves precisely
the next-power residual. This does not assume the residual is small. -/
theorem finiteCorrection_apply {V : Type*} [AddCommGroup V] [Module R V]
    (error : Module.End R V) (depth : ℕ) (target : V) :
    (1 + error) (finiteCorrection error depth target) =
      target - ((-error) ^ (depth + 1)) target := by
  have h := congrArg (fun operator : Module.End R V => operator target)
    (finiteCorrection_residual error depth)
  simpa using h

end FiniteInverse

/-- The division step in `lem:accuracy-charge`, with the positive denominator
made explicit. `numerator` and `denominator` are the charge probabilities
multiplied by the modulus. -/
theorem ratio_deviation_bound (numerator denominator numeratorError denominatorError : ℝ)
    (hn : |numerator - 1| ≤ numeratorError)
    (hd : |denominator - 1| ≤ denominatorError)
    (hsmall : denominatorError < 1) :
    |numerator / denominator - 1| ≤
      (numeratorError + denominatorError) / (1 - denominatorError) := by
  have hbase : 0 < 1 - denominatorError := by linarith
  have hden : 1 - denominatorError ≤ denominator := by
    have := (abs_le.mp hd).1
    linarith
  have hpos : 0 < denominator := lt_of_lt_of_le hbase hden
  have hdiff : |numerator - denominator| ≤ numeratorError + denominatorError := by
    calc
      |numerator - denominator| = |(numerator - 1) + -(denominator - 1)| := by
        congr 1
        ring
      _ ≤ |numerator - 1| + |-(denominator - 1)| := abs_add_le _ _
      _ ≤ numeratorError + denominatorError := by simpa only [abs_neg] using add_le_add hn hd
  have herr : 0 ≤ numeratorError + denominatorError :=
    (abs_nonneg _).trans hdiff
  calc
    |numerator / denominator - 1| = |numerator - denominator| / denominator := by
      rw [div_sub_one (ne_of_gt hpos), abs_div, abs_of_pos hpos]
    _ ≤ (numeratorError + denominatorError) / denominator :=
      div_le_div_of_nonneg_right hdiff (le_of_lt hpos)
    _ ≤ (numeratorError + denominatorError) / (1 - denominatorError) :=
      div_le_div_of_nonneg_left herr hbase hden

/-- The denominator condition cannot be discarded from the standalone ratio
lemma. This is a guard against overgeneralizing V7's asymptotic statement,
not a counterexample to its eventual-parameter theorem. -/
theorem charge_bound_negative_at_small_parameters :
    ((3 - 1 : ℝ) * ((9 / 10 : ℝ) ^ (1 - 1 : ℕ) + (9 / 10 : ℝ) ^ (1 : ℕ)) /
      (1 - (3 - 1 : ℝ) * (9 / 10 : ℝ) ^ (1 : ℕ))) = -(19 / 4 : ℝ) := by
  norm_num

/-- The integer ceiling choices in `eq:accuracy-orders` leave at least two
powers of the security parameter beyond the requested exponent. -/
theorem correction_order_slack (accuracyExponent : ℕ) :
    accuracyExponent + 42 ≤ 2 * ((accuracyExponent + 41) / 2 + 1) ∧
    2 * accuracyExponent + 80 ≤ 5 * ((2 * (accuracyExponent + 40) + 4) / 5 + 1) ∧
    accuracyExponent + 2 ≤ 4 * ((accuracyExponent + 5) / 4) := by
  omega

/-- A finite set of fixed-order eventual guarantees has a common threshold.
The selected order may oscillate; no convergence assumption is necessary. -/
theorem finite_orders_eventually {property : ℕ → ℕ → Prop}
    (ceiling : ℕ)
    (h : ∀ order ≤ ceiling, ∃ threshold, ∀ parameter ≥ threshold,
      property order parameter) :
    ∃ threshold, ∀ parameter ≥ threshold, ∀ order ≤ ceiling,
      property order parameter := by
  induction ceiling with
  | zero =>
    obtain ⟨threshold, ht⟩ := h 0 (by omega)
    exact ⟨threshold, fun parameter hp order ho => by
      have : order = 0 := by omega
      subst order
      exact ht parameter hp⟩
  | succ ceiling ih =>
    obtain ⟨oldThreshold, hold⟩ := ih (fun order ho => h order (by omega))
    obtain ⟨newThreshold, hnew⟩ := h (ceiling + 1) (by omega)
    refine ⟨max oldThreshold newThreshold, ?_⟩
    intro parameter hp order ho
    by_cases heq : order = ceiling + 1
    · subst order
      exact hnew parameter ((le_max_right _ _).trans hp)
    · exact hold parameter ((le_max_left _ _).trans hp) order (by omega)

end AFT
