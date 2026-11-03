import AFT.RejectionStability

/-! # Finite rejection is stable under approximating each acceptance coin -/
namespace AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
variable {State : Type*} [Fintype State]

theorem rejectionKernel_event (coin : State → ℝ)
    (hcoin : ∀ point,0 ≤ coin point ∧ coin point ≤ 1)
    (remaining : FiniteDist State) (point : State) (event : Finset State) :
    (rejectionKernel coin hcoin remaining point).event event=
      (if point∈event then coin point else 0)+(1-coin point)*remaining.event event := by
  simp only [FiniteDist.event,rejectionKernel,Finset.sum_add_distrib,← Finset.mul_sum]
  simp

/-- One coin perturbation costs its absolute probability error, uniformly
in the fallback distribution and without an inverse acceptance factor. -/
theorem rejectionStep_coin_tv (proposal : FiniteDist State) (first second : State → ℝ)
    (hfirst : ∀ point,0 ≤ first point ∧ first point ≤ 1)
    (hsecond : ∀ point,0 ≤ second point ∧ second point ≤ 1)
    (remaining : FiniteDist State) (error : ℝ)
    (herror : ∀ point,|first point-second point| ≤ error) :
    TVBound (rejectionStep proposal first hfirst remaining)
      (rejectionStep proposal second hsecond remaining) error := by
  intro event
  rw [rejectionStep_eq_mix,rejectionStep_eq_mix,event_mix,event_mix,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ point,proposal.weight point*error := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro point _
      rw [← mul_sub,abs_mul,abs_of_nonneg (proposal.nonneg point)]
      apply mul_le_mul_of_nonneg_left _ (proposal.nonneg point)
      rw [rejectionKernel_event,rejectionKernel_event]
      have he := remaining.event_nonneg event
      have he' := remaining.event_le_one event
      by_cases hp : point∈event
      · simp only [if_pos hp]
        have hid : first point+(1-first point)*remaining.event event-
            (second point+(1-second point)*remaining.event event)=
            (first point-second point)*(1-remaining.event event) := by ring
        rw [hid,abs_mul,abs_of_nonneg (by linarith : 0≤1-remaining.event event)]
        exact (mul_le_mul_of_nonneg_left (by linarith : 1-remaining.event event≤1) (abs_nonneg _)).trans
          (by simpa only [mul_one] using herror point)
      · simp only [if_neg hp,zero_add]
        have hid : (1-first point)*remaining.event event-(1-second point)*remaining.event event=
            -(first point-second point)*remaining.event event := by ring
        rw [hid,abs_mul,abs_neg,abs_of_nonneg he]
        exact (mul_le_mul_of_nonneg_left he' (abs_nonneg _)).trans
          (by simpa only [mul_one] using herror point)
    _ = error := by rw [← Finset.sum_mul,proposal.sum_one,one_mul]

theorem cappedRejection_coin_tv (proposal : FiniteDist State) (first second : State → ℝ)
    (hfirst : ∀ point,0 ≤ first point ∧ first point ≤ 1)
    (hsecond : ∀ point,0 ≤ second point ∧ second point ≤ 1)
    (fallback : FiniteDist State) (error : ℝ)
    (herror : ∀ point,|first point-second point| ≤ error) (count : ℕ) :
    TVBound (cappedRejection proposal first hfirst fallback count)
      (cappedRejection proposal second hsecond fallback count) ((count : ℝ)*error) := by
  induction count with
  | zero => intro event; simp only [cappedRejection,Nat.cast_zero,zero_mul,sub_self,abs_zero,le_refl]
  | succ count ih =>
    have hstep := rejectionStep_coin_tv proposal first second hfirst hsecond
      (cappedRejection proposal first hfirst fallback count) error herror
    have hremaining := rejectionStep_remaining_tv proposal second hsecond _ _ _ ih
    have hh := hstep.triangle hremaining
    simpa only [cappedRejection,Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_comm] using hh

end
end AFT.FiniteDist
