import AFT.Rejection

/-! # Proposal approximation propagates through a finite rejection loop -/
namespace AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
variable {State : Type*} [Fintype State]

def rejectionKernel (coin : State → ℝ) (hcoin : ∀ point,0 ≤ coin point ∧ coin point ≤ 1)
    (remaining : FiniteDist State) (point : State) : FiniteDist State where
  weight output := (if point=output then coin point else 0)+(1-coin point)*remaining.weight output
  nonneg output := add_nonneg (by split_ifs; exact (hcoin point).1; rfl)
    (mul_nonneg (by linarith [(hcoin point).2]) (remaining.nonneg output))
  sum_one := by
    simp only [Finset.sum_add_distrib,← Finset.mul_sum,remaining.sum_one,mul_one]
    simp

theorem rejectionStep_eq_mix (proposal : FiniteDist State) (coin : State → ℝ)
    (hcoin : ∀ point,0 ≤ coin point ∧ coin point ≤ 1) (remaining : FiniteDist State) :
    rejectionStep proposal coin hcoin remaining=proposal.mix (rejectionKernel coin hcoin remaining) := by
  ext point
  simp only [rejectionStep,mix_weight,rejectionKernel,mul_add,Finset.sum_add_distrib,
    mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  simp only [← mul_assoc]
  rw [← Finset.sum_mul]
  simp only [mul_sub,mul_one,Finset.sum_sub_distrib,proposal.sum_one,acceptance]

theorem rejectionStep_remaining_tv (proposal : FiniteDist State) (coin : State → ℝ)
    (hcoin : ∀ point,0 ≤ coin point ∧ coin point ≤ 1) (first second : FiniteDist State)
    (error : ℝ) (h : TVBound first second error) :
    TVBound (rejectionStep proposal coin hcoin first) (rejectionStep proposal coin hcoin second) error := by
  intro event
  have he : (rejectionStep proposal coin hcoin first).event event-
      (rejectionStep proposal coin hcoin second).event event=
      (1-acceptance proposal coin)*(first.event event-second.event event) := by
    simp only [FiniteDist.event,rejectionStep,Finset.sum_add_distrib,← Finset.mul_sum]
    ring
  rw [he,abs_mul,abs_of_nonneg (sub_nonneg.mpr (acceptance_bounds proposal coin hcoin).2)]
  calc
    _ ≤ 1*|first.event event-second.event event| :=
      mul_le_mul_of_nonneg_right (by linarith [(acceptance_bounds proposal coin hcoin).1]) (abs_nonneg _)
    _ ≤ error := by simpa only [one_mul] using h event

/-- Replacing the proposal by a TV-close law costs at most one proposal
error per actual attempted draw, with no inverse acceptance loss. -/
theorem cappedRejection_proposal_tv (first second : FiniteDist State) (coin : State → ℝ)
    (hcoin : ∀ point,0 ≤ coin point ∧ coin point ≤ 1) (fallback : FiniteDist State)
    (error : ℝ) (h : TVBound first second error) (count : ℕ) :
    TVBound (cappedRejection first coin hcoin fallback count)
      (cappedRejection second coin hcoin fallback count) ((count : ℝ)*error) := by
  induction count with
  | zero => intro event; simp only [cappedRejection,Nat.cast_zero,zero_mul,sub_self,abs_zero,le_refl]
  | succ count ih =>
    have hproposal := h.mix (rejectionKernel coin hcoin (cappedRejection first coin hcoin fallback count))
    rw [← rejectionStep_eq_mix,← rejectionStep_eq_mix] at hproposal
    have hremaining := rejectionStep_remaining_tv second coin hcoin _ _ _ ih
    have hh := hproposal.triangle hremaining
    simpa only [cappedRejection,Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_comm] using hh

end
end AFT.FiniteDist
