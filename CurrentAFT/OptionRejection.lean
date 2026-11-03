import CurrentAFT.BoundedRejection
import AFT.RationalRejectionProgram

/-! # Capped public rejection with an explicit failed outcome

Failure returns `none`; it never requires constructing a public core by
choice. The accepted target is exactly the original positive core law.
-/
namespace CurrentAFT.OptionRejection
open AFT
open scoped BigOperators Classical
noncomputable section
variable {Core : Type*} [Fintype Core]
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

def weight (value : Core → ℝ) : Option Core → ℝ
  | none => 0
  | some core => value core

def charge (predicate : Core → Prop) : Option Core → Prop
  | none => False
  | some core => predicate core

theorem proposal_none (proposal : FiniteDist Core) : (proposal.map some).weight none = 0 := by
  simp [FiniteDist.map_weight]

theorem proposal_some (proposal : FiniteDist Core) (core : Core) :
    (proposal.map some).weight (some core) = proposal.weight core := by
  simp [FiniteDist.map_weight]

theorem mass (proposal : FiniteDist Core) (value : Core → ℝ) (predicate : Core → Prop) :
    publicCoreMass (proposal.map some) (weight value) (charge predicate) =
      publicCoreMass proposal value predicate := by
  simp only [publicCoreMass, Fintype.sum_option, clippedPublicCoreWeight, charge, weight,
    if_false, zero_add, proposal_some]

theorem positive_law (proposal : FiniteDist Core) (value : Core → ℝ) (predicate : Core → Prop)
    (hpositive : 0 < publicCoreMass proposal value predicate) :
    positivePublicCoreLaw (proposal.map some) (weight value) (charge predicate)
      (by rw [mass]; exact hpositive) = (positivePublicCoreLaw proposal value predicate hpositive).map some := by
  ext output
  cases output with
  | none =>
    simp [positivePublicCoreLaw, FiniteDist.normalize, clippedPublicCoreWeight, charge, proposal_none]
  | some core =>
    rw [proposal_some]
    change clippedPublicCoreWeight (proposal.map some) (weight value) (charge predicate) (some core) /
      publicCoreMass (proposal.map some) (weight value) (charge predicate) =
      clippedPublicCoreWeight proposal value predicate core / publicCoreMass proposal value predicate
    rw [mass]
    simp only [clippedPublicCoreWeight, charge, weight, proposal_some]

def ideal (proposal : FiniteDist Core) (value : Core → ℝ) (predicate : Core → Prop) (trials : ℕ) : FiniteDist (Option Core) :=
  (proposal.map some).cappedRejection (clippedChargeCoin (weight value) (charge predicate))
    (clippedChargeCoin_bounds (weight value) (charge predicate)) (CanonicalMoments.pointLaw none) trials

theorem ideal_error (proposal : FiniteDist Core) (value : Core → ℝ) (predicate : Core → Prop)
    (q : ℝ) (hq : 0 < q) (hmass : 1/(4*q) ≤ publicCoreMass proposal value predicate) (trials : ℕ) :
    FiniteDist.TVBound (ideal proposal value predicate trials)
      ((positivePublicCoreLaw proposal value predicate (lt_of_lt_of_le (by positivity) hmass)).map some)
      (Real.exp (-(trials : ℝ)/(8*q))) := by
  have h := clipped_capped_rejection_tv (proposal.map some) (weight value) (charge predicate)
    q hq (by rw [mass]; exact hmass) (CanonicalMoments.pointLaw none) trials
  rw [positive_law] at h
  exact h

theorem approximate_error (proposal approximation : FiniteDist Core) (value : Core → ℝ) (predicate : Core → Prop)
    (coin : Option Core → ℝ) (hcoin : ∀ core, 0 ≤ coin core ∧ coin core ≤ 1)
    (q proposalError coinError : ℝ) (hq : 0 < q)
    (hmass : 1/(4*q) ≤ publicCoreMass proposal value predicate)
    (hproposal : FiniteDist.TVBound approximation proposal proposalError)
    (herror : ∀ core, |coin core-clippedChargeCoin (weight value) (charge predicate) core| ≤ coinError)
    (trials : ℕ) :
    FiniteDist.TVBound
      ((approximation.map some).cappedRejection coin hcoin (CanonicalMoments.pointLaw none) trials)
      ((positivePublicCoreLaw proposal value predicate (lt_of_lt_of_le (by positivity) hmass)).map some)
      ((trials : ℝ)*(proposalError+coinError)+Real.exp (-(trials : ℝ)/(8*q))) := by
  have hp := FiniteDist.cappedRejection_proposal_tv (approximation.map some) (proposal.map some)
    coin hcoin (CanonicalMoments.pointLaw none) proposalError (hproposal.map some) trials
  have hc := FiniteDist.cappedRejection_coin_tv (proposal.map some) coin
    (clippedChargeCoin (weight value) (charge predicate)) hcoin
    (clippedChargeCoin_bounds (weight value) (charge predicate)) (CanonicalMoments.pointLaw none)
    coinError herror trials
  have ht := ideal_error proposal value predicate q hq hmass trials
  convert (hp.triangle hc).triangle ht using 1
  ring

end
end CurrentAFT.OptionRejection
