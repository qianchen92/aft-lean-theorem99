import AFT.Rejection
import AFT.MixtureConditioning

/-! # Finite rejection with a decidable event, without a random accept coin -/
namespace AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
variable {State : Type*} [Fintype State]

def eventCoin (event : State → Prop) : State → ℝ := fun point => if event point then 1 else 0

omit [Fintype State] in
theorem eventCoin_bounds (event : State → Prop) : ∀ point,0 ≤ eventCoin event point ∧ eventCoin event point ≤ 1 := by
  intro point
  simp only [eventCoin]
  split_ifs <;> norm_num

theorem eventCoin_acceptance (proposal : FiniteDist State) (event : State → Prop) :
    acceptance proposal (eventCoin event)=proposal.eventMass event := by
  simp only [acceptance,eventCoin,eventMass,mul_ite,mul_one,mul_zero]

theorem acceptedLaw_eventCoin (proposal : FiniteDist State) (event : State → Prop)
    (hpos : 0 < proposal.eventMass event) :
    acceptedLaw proposal (eventCoin event) (fun point => (eventCoin_bounds event point).1)
      (by rw [eventCoin_acceptance]; exact hpos)=proposal.condition event hpos := by
  ext point
  simp only [acceptedLaw,condition,eventCoin,eventCoin_acceptance,mul_ite,mul_one,mul_zero]

def cappedCondition (proposal : FiniteDist State) (event : State → Prop)
    (fallback : FiniteDist State) (count : ℕ) : FiniteDist State :=
  cappedRejection proposal (eventCoin event) (eventCoin_bounds event) fallback count

theorem cappedCondition_tv (proposal : FiniteDist State) (event : State → Prop)
    (hpos : 0 < proposal.eventMass event) (fallback : FiniteDist State) (count : ℕ) :
    TVBound (cappedCondition proposal event fallback count) (proposal.condition event hpos)
      (Real.exp (-(count : ℝ)*proposal.eventMass event)) := by
  have hh := cappedRejection_exp_bound proposal (eventCoin event) (eventCoin_bounds event)
    (by rw [eventCoin_acceptance]; exact hpos) fallback count
  rw [acceptedLaw_eventCoin proposal event hpos] at hh
  simpa only [eventCoin_acceptance,cappedCondition] using hh

theorem cappedCondition_outside (proposal : FiniteDist State) (event : State → Prop)
    (fallback : FiniteDist State) (count : ℕ) (point : State)
    (he : ¬event point) (hf : fallback.weight point=0) :
    (cappedCondition proposal event fallback count).weight point=0 := by
  induction count with
  | zero => exact hf
  | succ count ih =>
    change proposal.weight point*eventCoin event point+
      (1-acceptance proposal (eventCoin event))*(cappedCondition proposal event fallback count).weight point=0
    simp only [eventCoin,if_neg he,ih,mul_zero,add_zero]

end
end AFT.FiniteDist
