import AFT.SelectionBound
import AFT.Hoeffding

/-! # Retaining the full mean cancellation after finitely many block deletions -/

namespace CurrentAFT.OmittedBlockMean

open AFT
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {Index Coordinate : Type*} [Fintype Index] [Fintype Coordinate]

def removed (kept : Finset Index) : Finset Index := Finset.univ.filter (fun index => index ∉ kept)

/-- The loss from deleting actual blocks is exponential only in their
number. The original aggregate first-coefficient cancellation is retained. -/
theorem omitted_exp_le (kept : Finset Index) (coefficient : Index → Coordinate → ℝ)
    (henergy : (∑ index, ∑ coordinate, coefficient index coordinate ^ 2) ≤ 1 / 8) :
    Real.exp (8 * ∑ coordinate, (∑ index ∈ kept, coefficient index coordinate) ^ 2) ≤
      Real.exp (16 * ∑ coordinate, (∑ index, coefficient index coordinate) ^ 2) *
        Real.exp (2 * ((removed kept).card : ℝ)) := by
  let choice : Index → NonlinearFock.BlockChoice := fun index => if index ∈ kept then none else some false
  have hremaining (index : Index) (coordinate : Coordinate) :
      NonlinearFock.remainingLinear coefficient choice index coordinate =
        if index ∈ kept then coefficient index coordinate else 0 := by
    by_cases hmem : index ∈ kept <;> simp [NonlinearFock.remainingLinear, choice, hmem]
  have hsum (coordinate : Coordinate) :
      (∑ index, NonlinearFock.remainingLinear coefficient choice index coordinate) =
        ∑ index ∈ kept, coefficient index coordinate := by
    simp_rw [hremaining]
    simp
  have hcount : SelectionBound.selectionCount choice = (removed kept).card := by
    unfold SelectionBound.selectionCount removed
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro index _
    by_cases hmem : index ∈ kept <;> simp [choice, hmem, SelectionBound.choiceActive]
  have hmean := SelectionBound.remaining_mean_energy_le coefficient choice
  simp_rw [hsum, hcount] at hmean
  have hcount0 : (0 : ℝ) ≤ (removed kept).card := Nat.cast_nonneg _
  have hbudget := mul_le_mul_of_nonneg_left henergy hcount0
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith only [hmean, hbudget]

theorem omitted_exp_le_of_card_le (kept : Finset Index) (coefficient : Index → Coordinate → ℝ)
    (maximum : ℕ) (hremoved : (removed kept).card ≤ maximum)
    (henergy : (∑ index, ∑ coordinate, coefficient index coordinate ^ 2) ≤ 1 / 8) :
    Real.exp (8 * ∑ coordinate, (∑ index ∈ kept, coefficient index coordinate) ^ 2) ≤
      Real.exp (16 * ∑ coordinate, (∑ index, coefficient index coordinate) ^ 2) *
        Real.exp (2 * (maximum : ℝ)) := by
  apply (omitted_exp_le kept coefficient henergy).trans
  apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hremoved) (by norm_num)

/-- A finite source average gains the same fixed deletion constant. No
independence between the original mean and the removed blocks is required. -/
theorem omitted_square_mgf_le {Sample : Type*} [Fintype Sample] (source : FiniteDist Sample)
    (kept : Finset Index) (coefficient : Sample → Index → Coordinate → ℝ)
    (maximum : ℕ) (hremoved : (removed kept).card ≤ maximum)
    (henergy : ∀ sample, (∑ index, ∑ coordinate, coefficient sample index coordinate ^ 2) ≤ 1 / 8) :
    source.expectation (fun sample => Real.exp (8 * ∑ coordinate,
      (∑ index ∈ kept, coefficient sample index coordinate) ^ 2)) ≤
      Real.exp (2 * (maximum : ℝ)) * source.expectation (fun sample =>
        Real.exp (16 * ∑ coordinate, (∑ index, coefficient sample index coordinate) ^ 2)) := by
  calc
    _ ≤ source.expectation (fun sample =>
        Real.exp (16 * ∑ coordinate, (∑ index, coefficient sample index coordinate) ^ 2) *
          Real.exp (2 * (maximum : ℝ))) :=
      Finset.sum_le_sum (fun sample _ => mul_le_mul_of_nonneg_left
        (omitted_exp_le_of_card_le kept (coefficient sample) maximum hremoved (henergy sample)) (source.nonneg sample))
    _ = _ := by unfold FiniteDist.expectation; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring

end

end CurrentAFT.OmittedBlockMean
