import AFT.RepresentedCanonical

/-! # The small finite reciprocal after averaging one shared queue -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
variable {Seed Target Queue : Type*}

theorem finiteCorrection_sub_one_succ (error : Table Seed) (depth : ℕ) :
    finiteCorrection error (depth+1)-1 = (-error)*finiteCorrection error depth := by
  unfold finiteCorrection
  rw [Finset.sum_range_succ']
  simp only [pow_zero,add_sub_cancel_right,Finset.mul_sum,pow_succ']

theorem activity_finiteCorrection_sub_one_le (weight : Seed → ℝ) (hw : ∀ seed, 0 ≤ weight seed)
    (error : Table Seed) (depth : ℕ) (hs : activity weight error ≤ 1/2) :
    activity weight (finiteCorrection error depth-1) ≤ 2*activity weight error := by
  cases depth with
  | zero =>
    simp [finiteCorrection]
    exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (activity_nonneg weight hw error)
  | succ depth =>
    rw [finiteCorrection_sub_one_succ]
    apply (activity_mul_le weight hw _ _).trans
    rw [activity_neg]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left
      (activity_finiteCorrection_le_two weight hw error depth hs) (activity_nonneg weight hw error)

theorem hasOrder_finiteCorrection_sub_one (order : Seed → ℕ) (error : Table Seed)
    (depth : ℕ) (he : HasOrder order 1 error) :
    HasOrder order 1 (finiteCorrection error depth-1) := by
  cases depth with
  | zero => simp [finiteCorrection,HasOrder]
  | succ depth =>
    rw [finiteCorrection_sub_one_succ]
    exact hasOrder_mul order 1 0 _ _ (hasOrder_neg order 1 error he) (hasOrder_zero order _)

theorem hasOrder_truncate (order : Seed → ℕ) (minimum cutoff : ℕ) (table : Table Seed)
    (h : HasOrder order minimum table) : HasOrder order minimum (truncate order cutoff table) := by
  intro powers hp
  simp only [coeff_truncate,h powers hp,ite_self]

theorem map_queueAverage [Fintype Queue] (hom : Table Seed →ₐ[ℝ] Table Target)
    (queue : FiniteDist Queue) (tables : Queue → Table Seed) :
    hom (queueAverage queue tables) = queueAverage queue (fun sample => hom (tables sample)) := by
  unfold queueAverage
  simp only [map_sum,map_mul]
  apply Finset.sum_congr rfl
  intro sample _
  exact congrArg (fun value => value*hom (tables sample)) (hom.commutes (queue.weight sample))

theorem truncate_queueAverage_congr [Fintype Queue] (queue : FiniteDist Queue)
    (order : Seed → ℕ) (cutoff : ℕ) (first second : Queue → Table Seed)
    (h : ∀ sample, truncate order cutoff (first sample) = truncate order cutoff (second sample)) :
    truncate order cutoff (queueAverage queue first) = truncate order cutoff (queueAverage queue second) := by
  apply (quotient_eq_iff_truncate _ _ _ _).mp
  simp only [queueAverage,map_sum,map_mul]
  apply Finset.sum_congr rfl
  intro sample _
  rw [(quotient_eq_iff_truncate _ _ _ _).mpr (h sample)]

theorem queueReciprocal_small_activity [Fintype Queue] (weight : Seed → ℝ)
    (hw : ∀ seed, 0 ≤ weight seed) (queue : FiniteDist Queue) (logarithm : Queue → Table Seed)
    (cutoff : ℕ) (budget : ℝ) (hbudget : 0 ≤ budget) (hsmall : budget ≤ 1/4)
    (hlog : ∀ sample, activity weight (logarithm sample) ≤ budget) :
    activity weight (queueReciprocal queue logarithm cutoff) ≤ 2 ∧
    activity weight (queueReciprocal queue logarithm cutoff-1) ≤ 4*budget := by
  have hexp : Real.exp budget-1 ≤ 2*budget := by
    have hh := Real.abs_exp_sub_one_le (show |budget| ≤ 1 by rw [abs_of_nonneg hbudget]; linarith)
    exact (le_abs_self _).trans (by simpa only [abs_of_nonneg hbudget] using hh)
  have he := queueError_activity weight hw queue logarithm cutoff budget hlog
  have hes : activity weight (queueError queue logarithm cutoff) ≤ 1/2 :=
    he.trans (hexp.trans (by linarith))
  refine ⟨activity_finiteCorrection_le_two weight hw _ _ hes,?_⟩
  exact (activity_finiteCorrection_sub_one_le weight hw _ _ hes).trans (by linarith)

end
end AFT.RepresentedPolynomial
