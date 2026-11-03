import AFT.Rejection
import CurrentAFT.PublicCore

/-!
# Finite capped public rejection at one fixed placement

The actual acceptance coin is the public charge indicator times the clipped
weight divided by two. Exact finite-distribution semantics and a legal
fallback give the stated exponential timeout cost. No real-valued coin is
claimed to be a finite-bit implementation by this module.
-/

namespace CurrentAFT

open AFT
open scoped BigOperators Classical

noncomputable section

variable {Core : Type*} [Fintype Core]

def clippedChargeCoin (weight : Core → ℝ) (charge : Core → Prop) (core : Core) : ℝ :=
  if charge core then clip (weight core) / 2 else 0

omit [Fintype Core] in
theorem clippedChargeCoin_bounds (weight : Core → ℝ) (charge : Core → Prop) :
    ∀ core, 0 ≤ clippedChargeCoin weight charge core ∧
      clippedChargeCoin weight charge core ≤ 1 := by
  intro core
  unfold clippedChargeCoin
  split_ifs
  · constructor <;> linarith [clip_nonneg (weight core), clip_le_two (weight core)]
  · norm_num

theorem clippedChargeCoin_acceptance (proposal : FiniteDist Core)
    (weight : Core → ℝ) (charge : Core → Prop) :
    proposal.acceptance (clippedChargeCoin weight charge) =
      publicCoreMass proposal weight charge / 2 := by
  unfold FiniteDist.acceptance publicCoreMass clippedPublicCoreWeight clippedChargeCoin
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro core _
  split_ifs <;> ring

theorem acceptedLaw_clippedChargeCoin (proposal : FiniteDist Core)
    (weight : Core → ℝ) (charge : Core → Prop)
    (hpositive : 0 < publicCoreMass proposal weight charge) :
    proposal.acceptedLaw (clippedChargeCoin weight charge)
      (fun core => (clippedChargeCoin_bounds weight charge core).1)
      (by rw [clippedChargeCoin_acceptance]; positivity) =
        positivePublicCoreLaw proposal weight charge hpositive := by
  ext core
  change proposal.weight core * clippedChargeCoin weight charge core /
      proposal.acceptance (clippedChargeCoin weight charge) =
    clippedPublicCoreWeight proposal weight charge core / publicCoreMass proposal weight charge
  rw [clippedChargeCoin_acceptance]
  unfold clippedChargeCoin clippedPublicCoreWeight
  by_cases hcharge : charge core
  · simp only [if_pos hcharge]
    field_simp [hpositive.ne']
  · simp [hcharge]

/-- Exact public rejection semantics with any fallback at the same placement.
Only the actual public coin is evaluated by the rejection loop. -/
theorem clipped_capped_rejection_tv (proposal : FiniteDist Core)
    (weight : Core → ℝ) (charge : Core → Prop) (q : ℝ) (hq : 0 < q)
    (hmass : 1 / (4 * q) ≤ publicCoreMass proposal weight charge)
    (fallback : FiniteDist Core) (trials : ℕ) :
    FiniteDist.TVBound
      (proposal.cappedRejection (clippedChargeCoin weight charge)
        (clippedChargeCoin_bounds weight charge) fallback trials)
      (positivePublicCoreLaw proposal weight charge
        (lt_of_lt_of_le (by positivity) hmass))
      (Real.exp (-(trials : ℝ) / (8 * q))) := by
  have hpositive : 0 < publicCoreMass proposal weight charge :=
    lt_of_lt_of_le (by positivity) hmass
  have haccept : 0 < proposal.acceptance (clippedChargeCoin weight charge) := by
    rw [clippedChargeCoin_acceptance]
    positivity
  have hlower : 1 / (8 * q) ≤ proposal.acceptance (clippedChargeCoin weight charge) := by
    rw [clippedChargeCoin_acceptance]
    have hhalf : (1 / (4 * q)) / 2 = 1 / (8 * q) := by ring
    linarith
  have hbound := FiniteDist.cappedRejection_exp_bound proposal (clippedChargeCoin weight charge)
    (clippedChargeCoin_bounds weight charge) haccept fallback trials
  rw [acceptedLaw_clippedChargeCoin proposal weight charge hpositive] at hbound
  apply hbound.mono
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left hlower (Nat.cast_nonneg trials)
  calc
    _ = -((trials : ℝ) * proposal.acceptance (clippedChargeCoin weight charge)) := by ring
    _ ≤ -((trials : ℝ) * (1 / (8 * q))) := neg_le_neg h
    _ = _ := by ring

/-- The real-valued timeout inequality for a prescribed logarithmic cap. -/
theorem timeout_bound (q error : ℝ) (hq : 0 < q) (herror : 0 < error)
    (trials : ℕ) (htrials : 8 * q * Real.log (1 / error) ≤ (trials : ℝ)) :
    Real.exp (-(trials : ℝ) / (8 * q)) ≤ error := by
  have hexponent : -(trials : ℝ) / (8 * q) ≤ Real.log error := by
    rw [Real.log_div (by norm_num) (ne_of_gt herror), Real.log_one] at htrials
    have hdenom : 0 < 8 * q := by positivity
    apply (div_le_iff₀ hdenom).mpr
    nlinarith
  exact (Real.exp_le_exp.mpr hexponent).trans_eq (Real.exp_log herror)

/-- Taking the natural ceiling gives the cap in `lem:df-bounded-rejection`. -/
theorem timeout_ceiling (q error : ℝ) (hq : 0 < q) (herror : 0 < error) :
    Real.exp (-((⌈8 * q * Real.log (1 / error)⌉₊ : ℕ) : ℝ) / (8 * q)) ≤ error :=
  timeout_bound q error hq herror _ (Nat.le_ceil _)

end

end CurrentAFT
