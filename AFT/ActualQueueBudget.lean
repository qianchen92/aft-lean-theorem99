import AFT.ActualRootBudget
import AFT.V7PublicPlacement

/-! # The actual common queue costs only its q selected body positions -/

namespace AFT.V7Calibration

open Filter GaussianSource FiniteConcentration
open scoped BigOperators Classical Topology

noncomputable section

local instance actualQueueBudgetFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance actualQueueBudgetSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _

/-- Difference of the true normalized body means for one realized common
queue and the zero queue, with the complete root word retained. -/
def actualQueueDisplacement (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (root : blockIndex parameter → ℤ)
    (sample : Window (queueCutoff parameter) × Equiv.Perm (blockIndex parameter)) :
    EuclideanSpace ℝ (Fin (Parameters.modulus parameter)) :=
  actualFockScale parameter • (∑ index,
    (actualBlockBodyVector cutoffScale parameter beta index (root index) (actualQueueShifts parameter sample index) -
      actualBlockBodyVector cutoffScale parameter beta index (root index) 0))

/-- Only the q publicly selected coordinates can change. The bound is
uniform even though every selected coordinate shares the same queue draw. -/
theorem actual_queue_displacement_bound_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ root : blockIndex parameter → ℤ,
      (∀ index, |root index| ≤ (v7RootCutoff parameter : ℤ)) →
      ∀ sample, ‖actualQueueDisplacement cutoffScale parameter (beta parameter) root sample‖ ≤
        592 / (parameter : ℝ) ^ 7 := by
  filter_upwards [actual_body_vector_bound_eventually cutoffScale hscale beta hbeta,
    eventually_ge_atTop 2] with parameter hb hp root hroot sample
  have hx : (0 : ℝ) < parameter := by exact_mod_cast (by omega : 0 < parameter)
  let changeAt (index : blockIndex parameter) :=
    actualBlockBodyVector cutoffScale parameter (beta parameter) index (root index) (actualQueueShifts parameter sample index) -
      actualBlockBodyVector cutoffScale parameter (beta parameter) index (root index) 0
  have hpoint (index : blockIndex parameter) : ‖changeAt index‖ ≤
      if sample.2 index ∈ actualQueueSelection parameter then 148 / (parameter : ℝ) ^ 19 else 0 := by
    by_cases hi : sample.2 index ∈ actualQueueSelection parameter
    · rw [if_pos hi]
      have hq := hb index (root index) _ (hroot index) (actualQueueShifts_bound parameter sample index)
      have hz := hb index (root index) 0 (hroot index) (by simp only [abs_zero]; positivity)
      exact (norm_sub_le _ _).trans ((add_le_add hq hz).trans_eq (by ring))
    · simp only [if_neg hi]
      have hzero : actualQueueShifts parameter sample index = 0 := by
        simp only [actualQueueShifts, FiniteDist.sharedQueueShift, if_neg hi]
      simp only [changeAt, hzero, sub_self, norm_zero, le_refl]
  have hsum : ‖∑ index, changeAt index‖ ≤
      Parameters.modulus parameter * (148 / (parameter : ℝ) ^ 19) := by
    apply (norm_sum_le _ _).trans
    apply (Finset.sum_le_sum fun index _ => hpoint index).trans_eq
    rw [Equiv.sum_comp sample.2 (fun index =>
      if index ∈ actualQueueSelection parameter then 148 / (parameter : ℝ) ^ 19 else 0)]
    simp only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul,
      actualQueueSelection_card]
  have hq : (Parameters.modulus parameter : ℝ) ≤ 2 * (parameter : ℝ) ^ 40 := by
    exact_mod_cast (show Parameters.modulus parameter ≤ 2 * parameter ^ 40 by
      simpa only [Parameters.security_eq parameter hp] using (Parameters.modulus_bounds parameter).2)
  change ‖actualFockScale parameter • (∑ index, changeAt index)‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (actualFockScale_nonneg parameter)]
  calc
    _ ≤ (2 / (parameter : ℝ) ^ 28) * (Parameters.modulus parameter * (148 / (parameter : ℝ) ^ 19)) :=
      mul_le_mul (actualFockScale_le parameter hp) hsum (norm_nonneg _) (by positivity)
    _ ≤ (2 / (parameter : ℝ) ^ 28) * ((2 * (parameter : ℝ) ^ 40) * (148 / (parameter : ℝ) ^ 19)) := by gcongr
    _ = _ := by field_simp; ring

end

end AFT.V7Calibration
