import AFT.RepresentedLogarithm

/-! # Exact finite background certificates and shared-queue normalization -/

namespace AFT.RepresentedPolynomial

open scoped BigOperators Classical

noncomputable section

variable {Seed Block Queue : Type*}

def backgroundLogarithm (errors : Block → Table Seed) (blocks : Finset Block)
    (cutoff : ℕ) : Table Seed := ∑ block ∈ blocks, logarithm (errors block) cutoff

theorem backgroundLogarithm_hasOrder (order : Seed → ℕ) (cutoff : ℕ)
    (errors : Block → Table Seed) (blocks : Finset Block)
    (h : ∀ block ∈ blocks, HasOrder order 1 (errors block)) :
    HasOrder order 1 (backgroundLogarithm errors blocks cutoff) :=
  hasOrder_sum order 1 _ blocks (fun block hb => hasOrder_logarithm order cutoff _ (h block hb))

theorem quotient_background_exponential (order : Seed → ℕ) (cutoff : ℕ)
    (errors : Block → Table Seed) (blocks : Finset Block)
    (h : ∀ block ∈ blocks, HasOrder order 1 (errors block)) :
    quotientMap order cutoff (exponential (backgroundLogarithm errors blocks cutoff) cutoff) =
      quotientMap order cutoff (∏ block ∈ blocks, (1 + errors block)) := by
  classical
  induction blocks using Finset.induction_on with
  | empty =>
    simp only [backgroundLogarithm, Finset.sum_empty, Finset.prod_empty]
    rw [quotient_exponential order cutoff 0 (by intro powers _; simp)]
    simp only [map_zero, map_one]
    exact IsNilpotent.exp_zero
  | @insert block blocks hnot ih =>
    have hblock := h block (Finset.mem_insert_self _ _)
    have hrest := fun other ho => h other (Finset.mem_insert_of_mem ho)
    have hsum : backgroundLogarithm errors (insert block blocks) cutoff =
        logarithm (errors block) cutoff + backgroundLogarithm errors blocks cutoff := by
      simp only [backgroundLogarithm, Finset.sum_insert hnot]
    rw [hsum, quotient_exponential order cutoff _ (by
      intro powers hp
      simp only [MvPolynomial.coeff_add, hasOrder_logarithm order cutoff _ hblock powers hp,
        backgroundLogarithm_hasOrder order cutoff errors blocks hrest powers hp, zero_add]), map_add]
    rw [IsNilpotent.exp_add_of_commute (Commute.all _ _)
      (quotient_nilpotent order cutoff _ (hasOrder_logarithm order cutoff _ hblock))
      (quotient_nilpotent order cutoff _ (backgroundLogarithm_hasOrder order cutoff errors blocks hrest))]
    rw [quotient_logarithm, FormalLogarithm.exp_finiteLogarithm _ _
      (quotient_pow_zero order cutoff _ hblock),
      ← quotient_exponential order cutoff _ (backgroundLogarithm_hasOrder order cutoff errors blocks hrest),
      ih hrest, Finset.prod_insert hnot, map_mul, map_add, map_one]
    rfl

theorem truncate_background_exponential (order : Seed → ℕ) (cutoff : ℕ)
    (errors : Block → Table Seed) (blocks : Finset Block)
    (h : ∀ block ∈ blocks, HasOrder order 1 (errors block)) :
    truncate order cutoff (exponential (backgroundLogarithm errors blocks cutoff) cutoff) =
      truncate order cutoff (∏ block ∈ blocks, (1 + errors block)) :=
  (quotient_eq_iff_truncate order cutoff _ _).mp
    (quotient_background_exponential order cutoff errors blocks h)

theorem activity_backgroundLogarithm_le (weight : Seed → ℝ) (hweight : ∀ seed, 0 ≤ weight seed)
    (cutoff : ℕ) (errors : Block → Table Seed) (blocks : Finset Block)
    (hsmall : ∀ block ∈ blocks, activity weight (errors block) ≤ 1 / 2) :
    activity weight (backgroundLogarithm errors blocks cutoff) ≤
      2 * ∑ block ∈ blocks, activity weight (errors block) := by
  apply (activity_sum_le weight hweight _ _).trans
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun block hb => activity_logarithm_le weight hweight _ cutoff (hsmall block hb)

variable [Fintype Queue]

/-- The reciprocal is formed after averaging the common queue.  Its exact
normalization applies to the actual product of all local law polynomials. -/
theorem shared_queue_background_inverse (queue : FiniteDist Queue) (order : Seed → ℕ)
    (cutoff : ℕ) (errors : Queue → Block → Table Seed) (blocks : Finset Block)
    (h : ∀ value block, block ∈ blocks → HasOrder order 1 (errors value block)) :
    truncate order cutoff
      (queueReciprocal queue (fun value => backgroundLogarithm (errors value) blocks cutoff) cutoff *
        queueAverage queue (fun value => ∏ block ∈ blocks, (1 + errors value block))) = 1 := by
  have hid := queueReciprocal_identity queue order
    (fun value => backgroundLogarithm (errors value) blocks cutoff) cutoff
    (fun value => backgroundLogarithm_hasOrder order cutoff _ blocks (h value))
  conv_rhs => rw [← truncate_one order cutoff]
  apply (quotient_eq_iff_truncate order cutoff _ _).mp
  have hh := (quotient_eq_iff_truncate order cutoff _ _).mpr
    (hid.trans (truncate_one order cutoff).symm)
  simp only [map_mul, queueAverage, map_sum, quotient_background_exponential order cutoff _ blocks (h _)] at hh
  simpa only [queueAverage, map_mul, map_sum] using hh

end

end AFT.RepresentedPolynomial
