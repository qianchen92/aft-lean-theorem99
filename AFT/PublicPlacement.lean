import AFT.BodyBlur
import AFT.Hoeffding

/-! # Public permutation placements and a single shared queue

All positions use the same realized queue value. Only the selected public
positions receive it. The one-position marginal is derived from the exact
uniform permutation law; no independence of different positions is asserted.
-/

namespace AFT.FiniteDist

open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {Position Sample : Type*} [Fintype Position] [DecidableEq Position] [Nonempty Position]
  [Fintype Sample]

omit [Fintype Sample] in
theorem uniform_permutation_expectation (position : Position) (value : Position → ℝ) :
    (uniform (Equiv.Perm Position)).expectation (fun permutation => value (permutation position)) =
      (uniform Position).expectation value := by
  let average (position : Position) :=
    (uniform (Equiv.Perm Position)).expectation (fun permutation => value (permutation position))
  have hsame (other : Position) : average other = average position := by
    have h := Equiv.sum_comp (Equiv.mulRight (Equiv.swap position other))
      (fun permutation : Equiv.Perm Position =>
        (uniform (Equiv.Perm Position)).weight permutation * value (permutation position))
    simpa only [average, expectation, uniform_weight, Equiv.coe_mulRight,
      Equiv.Perm.mul_apply, Equiv.swap_apply_left] using h
  have hsum : (∑ other, average other) = ∑ other, value other := by
    unfold average expectation
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, Equiv.sum_comp]
    rw [← Finset.sum_mul, sum_one, one_mul]
  have hcard : (Fintype.card Position : ℝ) * average position = ∑ other, value other := by
    simpa only [hsame, Finset.sum_const, nsmul_eq_mul, Finset.card_univ] using hsum
  have hpos : (0 : ℝ) < Fintype.card Position := by exact_mod_cast Fintype.card_pos
  change average position = _
  unfold expectation
  simp only [uniform_weight, ← Finset.mul_sum]
  apply (mul_left_cancel₀ hpos.ne')
  rw [hcard]
  field_simp

omit [Fintype Sample] in
/-- Evaluation of a uniform permutation at a fixed position is exactly uniform. -/
theorem uniform_permutation_map (position : Position) :
    (uniform (Equiv.Perm Position)).map (fun permutation => permutation position) = uniform Position := by
  ext output
  have hh := uniform_permutation_expectation position (fun value => if value = output then 1 else 0)
  simpa only [expectation, map_weight, mul_ite, mul_one, mul_zero,
    uniform_weight, Finset.sum_ite_eq', Finset.mem_univ, if_true] using hh

omit [Fintype Sample] in
/-- A public mask is moved by a single random permutation. -/
def permutationMask (selected : Finset Position) (permutation : Equiv.Perm Position) : Finset Position :=
  selected.map permutation.symm.toEmbedding

omit [Fintype Sample] [Fintype Position] [DecidableEq Position] [Nonempty Position] in
@[simp] theorem permutationMask_mem (selected : Finset Position) (permutation : Equiv.Perm Position)
    (position : Position) : position ∈ permutationMask selected permutation ↔ permutation position ∈ selected := by
  simp [permutationMask]

omit [Fintype Sample] [Fintype Position] [DecidableEq Position] [Nonempty Position] in
@[simp] theorem permutationMask_card (selected : Finset Position) (permutation : Equiv.Perm Position) :
    (permutationMask selected permutation).card = selected.card := Finset.card_map _

omit [Fintype Sample] in
def sharedQueueShift (selected : Finset Position) (queue : ℤ) (permutation : Equiv.Perm Position)
    (position : Position) : ℤ := if permutation position ∈ selected then queue else 0

omit [Fintype Sample] [Fintype Position] [Nonempty Position] in
theorem sharedQueueShift_bound (selected : Finset Position) (queue : ℤ)
    (permutation : Equiv.Perm Position) (position : Position) :
    |sharedQueueShift selected queue permutation position| ≤ |queue| := by
  unfold sharedQueueShift
  split_ifs <;> simp [abs_nonneg]

omit [Fintype Sample] in
/-- Exact one-position shift marginal at a fixed common queue value. -/
theorem sharedQueueShift_expectation (selected : Finset Position) (queue : ℤ) (position : Position)
    (value : ℤ → ℝ) :
    (uniform (Equiv.Perm Position)).expectation
      (fun permutation => value (sharedQueueShift selected queue permutation position)) =
      (1 - (selected.card : ℝ) / Fintype.card Position) * value 0 +
        ((selected.card : ℝ) / Fintype.card Position) * value queue := by
  change (uniform (Equiv.Perm Position)).expectation
    (fun permutation => (fun point => value (if point ∈ selected then queue else 0)) (permutation position)) = _
  rw [uniform_permutation_expectation position (fun point => value (if point ∈ selected then queue else 0))]
  have hpoint (point : Position) : value (if point ∈ selected then queue else 0) =
      value 0 + if point ∈ selected then value queue - value 0 else 0 := by
    split_ifs <;> ring
  simp only [expectation, uniform_weight, hpoint, ← Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Finset.sum_ite_mem, Finset.univ_inter]
  have hcard : (Fintype.card Position : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp
  ring


/-- Draw the queue once, independently of the public permutation. Its exact
one-position marginal is the optional source in the V7 body blur. -/
theorem sharedQueue_optional_expectation (selected : Finset Position) (source : FiniteDist Sample)
    (sourceShift : Sample → ℤ) (position : Position) (value : ℤ → ℝ) :
    (source.prod (uniform (Equiv.Perm Position))).expectation
      (fun sample => value (sharedQueueShift selected (sourceShift sample.1) sample.2 position)) =
      (optional source ((selected.card : ℝ) / Fintype.card Position)
        (by positivity)
        (by
          apply (div_le_one (by exact_mod_cast Fintype.card_pos : (0 : ℝ) < Fintype.card Position)).mpr
          exact_mod_cast Finset.card_le_univ selected)).expectation
        (fun sample => value (sample.elim 0 sourceShift)) := by
  have hpoint (sample : Sample) := sharedQueueShift_expectation selected (sourceShift sample) position value
  unfold expectation at hpoint ⊢
  simp only [prod_weight, Fintype.sum_prod_type, mul_assoc, ← Finset.mul_sum, hpoint,
    mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, source.sum_one, one_mul]
  rw [Fintype.sum_option]
  simp only [optional_none, optional_some, Option.elim_none, Option.elim_some]
  congr 1
  apply Finset.sum_congr rfl
  intro sample _
  ring

end
end AFT.FiniteDist
