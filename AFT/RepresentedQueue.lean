import AFT.RepresentedTruncation

/-!
# Shared-queue normalization in the explicit input polynomial algebra

The average, exponential and finite reciprocal are concrete finite
polynomials.  Exactness is checked coefficient by coefficient through the
specified input-order cutoff; the activity estimates use the actual seed
weights, with no normed-algebra instance supplied as an assumption.
-/

namespace AFT.RepresentedPolynomial

open scoped BigOperators Classical

noncomputable section

variable {Seed Queue : Type*} [Fintype Queue]

omit [Fintype Queue] in
theorem hasOrder_sum {Tag : Type*} (order : Seed → ℕ) (minimum : ℕ)
    (tables : Tag → Table Seed) (tags : Finset Tag)
    (h : ∀ tag ∈ tags, HasOrder order minimum (tables tag)) :
    HasOrder order minimum (∑ tag ∈ tags, tables tag) := by
  intro powers hp
  exact (MvPolynomial.coeff_sum tags tables powers).trans
    (Finset.sum_eq_zero fun tag ht => h tag ht powers hp)

omit [Fintype Queue] in
theorem hasOrder_mono (order : Seed → ℕ) (first second : ℕ) (table : Table Seed)
    (h : HasOrder order second table) (hle : first ≤ second) : HasOrder order first table :=
  fun powers hp => h powers (hp.trans_le hle)

omit [Fintype Queue] in
theorem hasOrder_exponential_sub_one (order : Seed → ℕ) (table : Table Seed)
    (degree : ℕ) (h : HasOrder order 1 table) :
    HasOrder order 1 (exponential table degree - 1) := by
  rw [exponential_sub_one]
  apply hasOrder_sum
  intro index _
  have hp := hasOrder_pow order 1 table h (index + 1)
  simp only [mul_one] at hp
  exact hasOrder_mul order 0 1 _ _ (hasOrder_zero order _)
    (hasOrder_mono order 1 (index + 1) _ hp (by omega))

def queueAverage (queue : FiniteDist Queue) (tables : Queue → Table Seed) : Table Seed :=
  ∑ value, MvPolynomial.C (queue.weight value) * tables value

theorem queueAverage_add (queue : FiniteDist Queue) (first second : Queue → Table Seed) :
    queueAverage queue (fun value => first value + second value) =
      queueAverage queue first + queueAverage queue second := by
  simp only [queueAverage, mul_add, Finset.sum_add_distrib]

theorem queueAverage_sub (queue : FiniteDist Queue) (first second : Queue → Table Seed) :
    queueAverage queue (fun value => first value - second value) =
      queueAverage queue first - queueAverage queue second := by
  simp only [queueAverage, mul_sub, Finset.sum_sub_distrib]

@[simp] theorem queueAverage_const (queue : FiniteDist Queue) (table : Table Seed) :
    queueAverage queue (fun _ => table) = table := by
  simp only [queueAverage, ← Finset.sum_mul, ← map_sum, queue.sum_one, map_one, one_mul]

theorem queueAverage_hasOrder (queue : FiniteDist Queue) (order : Seed → ℕ)
    (minimum : ℕ) (tables : Queue → Table Seed)
    (h : ∀ value, HasOrder order minimum (tables value)) :
    HasOrder order minimum (queueAverage queue tables) := by
  apply hasOrder_sum
  intro value _
  simpa only [zero_add] using hasOrder_mul order 0 minimum
    (MvPolynomial.C (queue.weight value)) (tables value) (hasOrder_zero order _) (h value)

theorem activity_queueAverage_le (weight : Seed → ℝ) (hweight : ∀ seed, 0 ≤ weight seed)
    (queue : FiniteDist Queue) (tables : Queue → Table Seed) :
    activity weight (queueAverage queue tables) ≤
      ∑ value, queue.weight value * activity weight (tables value) := by
  apply (activity_sum_le weight hweight _ _).trans
  apply Finset.sum_le_sum
  intro value _
  simpa only [activity_C, abs_of_nonneg (queue.nonneg value)] using
    activity_mul_le weight hweight (MvPolynomial.C (queue.weight value)) (tables value)

theorem activity_queueAverage_le_bound (weight : Seed → ℝ) (hweight : ∀ seed, 0 ≤ weight seed)
    (queue : FiniteDist Queue) (tables : Queue → Table Seed) (bound : ℝ)
    (h : ∀ value, activity weight (tables value) ≤ bound) :
    activity weight (queueAverage queue tables) ≤ bound := by
  apply (activity_queueAverage_le weight hweight queue tables).trans
  calc
    _ ≤ ∑ value, queue.weight value * bound :=
      Finset.sum_le_sum fun value _ => mul_le_mul_of_nonneg_left (h value) (queue.nonneg value)
    _ = bound := by rw [← Finset.sum_mul, queue.sum_one, one_mul]

omit [Fintype Queue] in
theorem activity_exponential_le (weight : Seed → ℝ) (hweight : ∀ seed, 0 ≤ weight seed)
    (table : Table Seed) (degree : ℕ) :
    activity weight (exponential table degree) ≤ Real.exp (activity weight table) := by
  have hadd := activity_add_le weight hweight (exponential table degree - 1) 1
  rw [sub_add_cancel, activity_one] at hadd
  have hexp := activity_exponential_sub_one weight hweight table degree
  linarith

def queueError (queue : FiniteDist Queue) (logarithm : Queue → Table Seed) (degree : ℕ) : Table Seed :=
  queueAverage queue (fun value => exponential (logarithm value) degree) - 1

def queueReciprocal (queue : FiniteDist Queue) (logarithm : Queue → Table Seed) (degree : ℕ) : Table Seed :=
  finiteCorrection (queueError queue logarithm degree) degree

theorem queueError_identity (queue : FiniteDist Queue) (logarithm : Queue → Table Seed) (degree : ℕ) :
    queueError queue logarithm degree =
      queueAverage queue (fun value => exponential (logarithm value) degree - 1) := by
  rw [queueAverage_sub, queueAverage_const]
  rfl

theorem queueError_hasOrder (queue : FiniteDist Queue) (order : Seed → ℕ)
    (logarithm : Queue → Table Seed) (degree : ℕ) (h : ∀ value, HasOrder order 1 (logarithm value)) :
    HasOrder order 1 (queueError queue logarithm degree) := by
  rw [queueError_identity]
  exact queueAverage_hasOrder queue order 1 _ fun value =>
    hasOrder_exponential_sub_one order (logarithm value) degree (h value)

theorem queueError_activity (weight : Seed → ℝ) (hweight : ∀ seed, 0 ≤ weight seed)
    (queue : FiniteDist Queue) (logarithm : Queue → Table Seed) (degree : ℕ) (budget : ℝ)
    (h : ∀ value, activity weight (logarithm value) ≤ budget) :
    activity weight (queueError queue logarithm degree) ≤ Real.exp budget - 1 := by
  rw [queueError_identity]
  apply activity_queueAverage_le_bound weight hweight
  intro value
  exact (activity_exponential_sub_one weight hweight _ _).trans
    (sub_le_sub_right (Real.exp_le_exp.mpr (h value)) 1)

theorem queueReciprocal_identity (queue : FiniteDist Queue) (order : Seed → ℕ)
    (logarithm : Queue → Table Seed) (degree : ℕ) (h : ∀ value, HasOrder order 1 (logarithm value)) :
    truncate order degree (queueReciprocal queue logarithm degree *
      queueAverage queue (fun value => exponential (logarithm value) degree)) = 1 := by
  have hh := truncate_finiteCorrection_residual order degree (queueError queue logarithm degree)
    (queueError_hasOrder queue order logarithm degree h)
  simpa only [queueError, add_sub_cancel, mul_comm, queueReciprocal] using hh

theorem queueReciprocal_activity (weight : Seed → ℝ) (hweight : ∀ seed, 0 ≤ weight seed)
    (queue : FiniteDist Queue) (logarithm : Queue → Table Seed) (degree : ℕ) (budget : ℝ)
    (h : ∀ value, activity weight (logarithm value) ≤ budget)
    (hsmall : Real.exp budget - 1 ≤ 1 / 2) :
    activity weight (queueReciprocal queue logarithm degree) ≤ 2 :=
  activity_finiteCorrection_le_two weight hweight _ _
    ((queueError_activity weight hweight queue logarithm degree budget h).trans hsmall)

/-- All occurrences use one queue value; expectation precedes the reciprocal. -/
theorem shared_queue_truncated_ratio (queue : FiniteDist Queue) (order : Seed → ℕ)
    (logarithm defect : Queue → Table Seed) (degree : ℕ)
    (h : ∀ value, HasOrder order 1 (logarithm value)) :
    truncate order degree (queueReciprocal queue logarithm degree * queueAverage queue
      (fun value => exponential (logarithm value) degree * (1 + defect value)) - 1) =
    truncate order degree (queueReciprocal queue logarithm degree * queueAverage queue
      (fun value => exponential (logarithm value) degree * defect value)) := by
  have heq : (fun value => exponential (logarithm value) degree * (1 + defect value)) =
      (fun value => exponential (logarithm value) degree + exponential (logarithm value) degree * defect value) := by
    funext value
    ring
  rw [heq, queueAverage_add, mul_add, truncate_sub, truncate_add, truncate_one,
    queueReciprocal_identity queue order logarithm degree h]
  ring

theorem shared_queue_truncated_activity (weight : Seed → ℝ) (hweight : ∀ seed, 0 ≤ weight seed)
    (queue : FiniteDist Queue) (order : Seed → ℕ) (logarithm defect : Queue → Table Seed)
    (degree : ℕ) (budget : ℝ) (h : ∀ value, activity weight (logarithm value) ≤ budget)
    (hsmall : Real.exp budget - 1 ≤ 1 / 2) :
    activity weight (truncate order degree (queueReciprocal queue logarithm degree * queueAverage queue
      (fun value => exponential (logarithm value) degree * defect value))) ≤
      2 * Real.exp budget * (∑ value, queue.weight value * activity weight (defect value)) := by
  have havg : activity weight (queueAverage queue
      (fun value => exponential (logarithm value) degree * defect value)) ≤
      Real.exp budget * (∑ value, queue.weight value * activity weight (defect value)) := by
    apply (activity_queueAverage_le weight hweight queue _).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro value _
    have hterm := (activity_mul_le weight hweight (exponential (logarithm value) degree) (defect value)).trans
      (mul_le_mul_of_nonneg_right ((activity_exponential_le weight hweight _ _).trans
        (Real.exp_le_exp.mpr (h value))) (activity_nonneg weight hweight _))
    nlinarith [queue.nonneg value]
  apply (activity_truncate_le weight hweight order degree _).trans
  apply (activity_mul_le weight hweight _ _).trans
  have hinv := queueReciprocal_activity weight hweight queue logarithm degree budget h hsmall
  have hnonneg := activity_nonneg weight hweight
    (queueAverage queue (fun value => exponential (logarithm value) degree * defect value))
  nlinarith

end

end AFT.RepresentedPolynomial
