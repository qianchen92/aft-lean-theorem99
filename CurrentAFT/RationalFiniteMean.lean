import CurrentAFT.CalibrationCoordinateError
import CurrentAFT.CyclePatternProgram

/-! # Finite reference perturbations for literal numerical means -/
namespace CurrentAFT.RationalFiniteMean
open AFT
open scoped BigOperators
set_option maxHeartbeats 1200000

theorem expectation_error {State : Type*} [Fintype State]
    (reference approximate : FiniteDist State) (value computed : State → ℝ)
    (pointError atomError bound : ℝ) (_ha : 0 ≤ atomError) (hb : 0 ≤ bound)
    (hpoint : ∀ state, |computed state-value state| ≤ pointError)
    (hatom : ∀ state, |approximate.weight state-reference.weight state| ≤ atomError)
    (hbound : ∀ state, |value state| ≤ bound) :
    |approximate.expectation computed-reference.expectation value| ≤
      pointError+bound*((Fintype.card State:ℝ)*atomError) := by
  have hfirst := CalibrationCoordinateError.expectation_abs_bound approximate (fun state => computed state-value state) pointError hpoint
  rw [FiniteDist.expectation_sub] at hfirst
  have hl1 : (∑ state, |approximate.weight state-reference.weight state|) ≤ (Fintype.card State:ℝ)*atomError := by
    exact (Finset.sum_le_sum (s := Finset.univ) (fun state _ => hatom state)).trans_eq (by simp)
  have hsecond := (CyclePatternProgram.expectation_difference_le_l1 approximate reference value bound hbound).trans
    (mul_le_mul_of_nonneg_left hl1 hb)
  exact (abs_sub_le _ (approximate.expectation value) _).trans (add_le_add hfirst hsecond)

end CurrentAFT.RationalFiniteMean
