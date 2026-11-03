import AFT.Hoeffding
import AFT.Correction

/-!
# Normalization with one shared queue value

All averaging is over a single finite queue law. The operations are finite
polynomials in the represented algebra, so no interchange of averaging and
inversion is made.
-/

namespace AFT.QueueNormalization

open scoped BigOperators Classical

noncomputable section

variable {α R : Type*} [Fintype α]

section Average

variable [NormedAddCommGroup R] [NormedSpace ℝ R]

def average (queue : FiniteDist α) (value : α → R) : R :=
  ∑ a, queue.weight a • value a

theorem average_add (queue : FiniteDist α) (left right : α → R) :
    average queue (left + right) = average queue left + average queue right := by
  simp [average, smul_add, Finset.sum_add_distrib]

theorem average_sub (queue : FiniteDist α) (left right : α → R) :
    average queue (left - right) = average queue left - average queue right := by
  simp [average, smul_sub, Finset.sum_sub_distrib]

theorem average_const (queue : FiniteDist α) (value : R) :
    average queue (fun _ => value) = value := by
  rw [average, ← Finset.sum_smul, queue.sum_one, one_smul]

theorem norm_average_le (queue : FiniteDist α) (value : α → R) :
    ‖average queue value‖ ≤ ∑ a, queue.weight a * ‖value a‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (queue.nonneg a)]

theorem norm_average_le_bound (queue : FiniteDist α) (value : α → R) (bound : ℝ)
    (h : ∀ a, ‖value a‖ ≤ bound) : ‖average queue value‖ ≤ bound := by
  apply (norm_average_le queue value).trans
  calc
    _ ≤ ∑ a, queue.weight a * bound :=
      Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (h a) (queue.nonneg a)
    _ = bound := by rw [← Finset.sum_mul, queue.sum_one, one_mul]

end Average

section Algebra

variable [NormedCommRing R] [NormedAlgebra ℝ R] [NormOneClass R]

def finiteExp (value : R) (degree : ℕ) : R :=
  ∑ i ∈ Finset.range (degree + 1), ((i.factorial : ℝ)⁻¹) • value ^ i

omit [NormOneClass R] in
theorem finiteExp_sub_one (value : R) (degree : ℕ) :
    finiteExp value degree - 1 =
      ∑ i ∈ Finset.range degree, (((i + 1).factorial : ℝ)⁻¹) • value ^ (i + 1) := by
  rw [finiteExp, Finset.sum_range_succ']
  simp

theorem norm_finiteExp_sub_one (value : R) (degree : ℕ) :
    ‖finiteExp value degree - 1‖ ≤ Real.exp ‖value‖ - 1 := by
  rw [finiteExp_sub_one]
  calc
    _ ≤ ∑ i ∈ Finset.range degree, ‖(((i + 1).factorial : ℝ)⁻¹) • value ^ (i + 1)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range degree, ‖value‖ ^ (i + 1) / (i + 1).factorial := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      simpa only [div_eq_mul_inv, mul_comm] using
        mul_le_mul_of_nonneg_left (norm_pow_le value (i + 1)) (by positivity : 0 ≤ ((i + 1).factorial : ℝ)⁻¹)
    _ ≤ _ := by
      have hh := Real.sum_le_exp_of_nonneg (norm_nonneg value) (degree + 1)
      rw [Finset.sum_range_succ'] at hh
      simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] at hh
      linarith

theorem norm_finiteExp_sub_one_le (value : R) (degree : ℕ) (budget : ℝ)
    (h : ‖value‖ ≤ budget) : ‖finiteExp value degree - 1‖ ≤ Real.exp budget - 1 :=
  (norm_finiteExp_sub_one value degree).trans (sub_le_sub_right (Real.exp_le_exp.mpr h) 1)

omit [NormedAlgebra ℝ R] in
theorem norm_finiteCorrection_le_two (error : R) (degree : ℕ) (h : ‖error‖ ≤ 1 / 2) :
    ‖finiteCorrection error degree‖ ≤ 2 := by
  have hsum : ∑ i ∈ Finset.range (degree + 1), ‖error‖ ^ i ≤ 2 := by
    calc
      _ ≤ ∑ i ∈ Finset.range (degree + 1), (1 / 2 : ℝ) ^ i :=
        Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg error) h i
      _ ≤ ∑' i : ℕ, (1 / 2 : ℝ) ^ i :=
        (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1)).sum_le_tsum _ (fun i _ => by positivity)
      _ = 2 := by rw [tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1)]; norm_num
  apply le_trans _ hsum
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  simpa only [norm_neg] using norm_pow_le (-error) i

omit [NormOneClass R] in
/-- Membership in the nilpotent positive-degree ideal is retained by the
finite exponential after removing its constant coefficient. -/
theorem finiteExp_sub_one_mem (ideal : Ideal R) (value : R) (degree : ℕ)
    (h : value ∈ ideal) : finiteExp value degree - 1 ∈ ideal := by
  rw [finiteExp_sub_one]
  apply ideal.sum_mem
  intro i _
  rw [Algebra.smul_def]
  apply ideal.mul_mem_left
  rw [pow_succ]
  exact ideal.mul_mem_left _ h

omit [NormOneClass R] in
theorem average_mem (queue : FiniteDist α) (ideal : Ideal R) (value : α → R)
    (h : ∀ a, value a ∈ ideal) : average queue value ∈ ideal := by
  apply ideal.sum_mem
  intro a _
  rw [Algebra.smul_def]
  exact ideal.mul_mem_left _ (h a)

def multiplier (logarithm : α → R) (degree : ℕ) : α → R := fun a => finiteExp (logarithm a) degree

omit [NormOneClass R] in
theorem average_multiplier_sub_one (queue : FiniteDist α) (logarithm : α → R) (degree : ℕ) :
    average queue (multiplier logarithm degree) - 1 =
      average queue (fun a => multiplier logarithm degree a - 1) := by
  have hh := average_sub queue (multiplier logarithm degree) (fun _ => (1 : R))
  rw [average_const] at hh
  exact hh.symm

theorem average_multiplier_small (queue : FiniteDist α) (logarithm : α → R)
    (degree : ℕ) (budget : ℝ) (h : ∀ a, ‖logarithm a‖ ≤ budget) :
    ‖average queue (multiplier logarithm degree) - 1‖ ≤ Real.exp budget - 1 := by
  rw [average_multiplier_sub_one]
  exact norm_average_le_bound queue _ _ (fun a => norm_finiteExp_sub_one_le _ _ _ (h a))

/-- The inverse of the shared-queue average is an explicit finite
polynomial, with both inverse identities proved from nilpotence. -/
def averageUnit (queue : FiniteDist α) (logarithm : α → R) (degree : ℕ)
    (ideal : Ideal R) (hnil : ideal ^ (degree + 1) = ⊥)
    (hlog : ∀ a, logarithm a ∈ ideal) : Rˣ where
  val := average queue (multiplier logarithm degree)
  inv := finiteCorrection (average queue (multiplier logarithm degree) - 1) degree
  val_inv := by
    have hm : average queue (multiplier logarithm degree) - 1 ∈ ideal := by
      rw [average_multiplier_sub_one]
      exact average_mem queue ideal _ (fun a => finiteExp_sub_one_mem ideal _ degree (hlog a))
    have hp : (-(average queue (multiplier logarithm degree) - 1)) ^ (degree + 1) = 0 := by
      simpa only [hnil, Ideal.mem_bot] using ideal.pow_mem_pow (ideal.neg_mem hm) (degree + 1)
    have hh := finiteCorrection_residual (average queue (multiplier logarithm degree) - 1) degree
    simpa only [add_sub_cancel, hp, sub_zero] using hh
  inv_val := by
    rw [mul_comm]
    have hm : average queue (multiplier logarithm degree) - 1 ∈ ideal := by
      rw [average_multiplier_sub_one]
      exact average_mem queue ideal _ (fun a => finiteExp_sub_one_mem ideal _ degree (hlog a))
    have hp : (-(average queue (multiplier logarithm degree) - 1)) ^ (degree + 1) = 0 := by
      simpa only [hnil, Ideal.mem_bot] using ideal.pow_mem_pow (ideal.neg_mem hm) (degree + 1)
    have hh := finiteCorrection_residual (average queue (multiplier logarithm degree) - 1) degree
    simpa only [add_sub_cancel, hp, sub_zero] using hh

theorem averageUnit_inverse_norm (queue : FiniteDist α) (logarithm : α → R) (degree : ℕ)
    (ideal : Ideal R) (hnil : ideal ^ (degree + 1) = ⊥) (hlog : ∀ a, logarithm a ∈ ideal)
    (budget : ℝ) (hbound : ∀ a, ‖logarithm a‖ ≤ budget)
    (hsmall : Real.exp budget - 1 ≤ 1 / 2) :
    ‖(↑((averageUnit queue logarithm degree ideal hnil hlog)⁻¹) : R)‖ ≤ 2 :=
  norm_finiteCorrection_le_two _ degree ((average_multiplier_small queue logarithm degree budget hbound).trans hsmall)

omit [NormOneClass R] in
/-- The ratio identity averages the entire physical queue-dependent
transform. In particular it never replaces the shared queue by independent
values at its different occurrences. -/
theorem shared_queue_ratio (queue : FiniteDist α) (logarithm defect : α → R) (degree : ℕ)
    (ideal : Ideal R) (hnil : ideal ^ (degree + 1) = ⊥) (hlog : ∀ a, logarithm a ∈ ideal) :
    (↑((averageUnit queue logarithm degree ideal hnil hlog)⁻¹) : R) *
        average queue (fun a => multiplier logarithm degree a * (1 + defect a)) - 1 =
      (↑((averageUnit queue logarithm degree ideal hnil hlog)⁻¹) : R) *
        average queue (fun a => multiplier logarithm degree a * defect a) := by
  have hexpand : (fun a => multiplier logarithm degree a * (1 + defect a)) =
      multiplier logarithm degree + (fun a => multiplier logarithm degree a * defect a) := by
    funext a
    simp [mul_add]
  rw [hexpand, average_add, mul_add]
  have hinv : (↑((averageUnit queue logarithm degree ideal hnil hlog)⁻¹) : R) *
      average queue (multiplier logarithm degree) = 1 :=
    (averageUnit queue logarithm degree ideal hnil hlog).inv_val
  rw [hinv]
  abel

omit [Fintype α] in
theorem multiplier_norm_le (logarithm : α → R) (degree : ℕ) (budget : ℝ)
    (hbound : ∀ a, ‖logarithm a‖ ≤ budget) (a : α) :
    ‖multiplier logarithm degree a‖ ≤ Real.exp budget := by
  have hh := norm_finiteExp_sub_one_le (logarithm a) degree budget (hbound a)
  have ht := norm_add_le (finiteExp (logarithm a) degree - 1) (1 : R)
  simp only [sub_add_cancel, norm_one] at ht
  exact ht.trans (by linarith)

/-- This bound also permits signed defects: no positivity of the numerator
or its coefficients is used. -/
theorem shared_queue_signed_bound (queue : FiniteDist α) (logarithm defect : α → R) (degree : ℕ)
    (ideal : Ideal R) (hnil : ideal ^ (degree + 1) = ⊥) (hlog : ∀ a, logarithm a ∈ ideal)
    (budget : ℝ) (hbound : ∀ a, ‖logarithm a‖ ≤ budget)
    (hsmall : Real.exp budget - 1 ≤ 1 / 2) :
    ‖(↑((averageUnit queue logarithm degree ideal hnil hlog)⁻¹) : R) *
      average queue (fun a => multiplier logarithm degree a * defect a)‖ ≤
      2 * Real.exp budget * (∑ a, queue.weight a * ‖defect a‖) := by
  have haverage : ‖average queue (fun a => multiplier logarithm degree a * defect a)‖ ≤
      Real.exp budget * (∑ a, queue.weight a * ‖defect a‖) := by
    apply (norm_average_le queue _).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a _
    have hp := (norm_mul_le (multiplier logarithm degree a) (defect a)).trans
      (mul_le_mul_of_nonneg_right (multiplier_norm_le logarithm degree budget hbound a) (norm_nonneg _))
    convert mul_le_mul_of_nonneg_left hp (queue.nonneg a) using 1
    ring
  have hnorm := averageUnit_inverse_norm queue logarithm degree ideal hnil hlog budget hbound hsmall
  apply (norm_mul_le _ _).trans
  have hh := mul_le_mul hnorm haverage (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  simpa only [mul_assoc] using hh

theorem shared_queue_ratio_bound (queue : FiniteDist α) (logarithm defect : α → R) (degree : ℕ)
    (ideal : Ideal R) (hnil : ideal ^ (degree + 1) = ⊥) (hlog : ∀ a, logarithm a ∈ ideal)
    (budget : ℝ) (hbound : ∀ a, ‖logarithm a‖ ≤ budget)
    (hsmall : Real.exp budget - 1 ≤ 1 / 2) :
    ‖(↑((averageUnit queue logarithm degree ideal hnil hlog)⁻¹) : R) *
        average queue (fun a => multiplier logarithm degree a * (1 + defect a)) - 1‖ ≤
      2 * Real.exp budget * (∑ a, queue.weight a * ‖defect a‖) := by
  rw [shared_queue_ratio]
  exact shared_queue_signed_bound queue logarithm defect degree ideal hnil hlog budget hbound hsmall

end Algebra

end

end AFT.QueueNormalization
