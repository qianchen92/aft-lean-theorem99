import AFT.ConditionalRepair

/-!
# Finite capped rejection, exact output law and retry error

This module describes the finite-probability semantics of rejection sampling.
It does not assert a bit-machine implementation for real probabilities.
-/

namespace AFT.FiniteDist

open scoped BigOperators Classical

noncomputable section

variable {A S : Type*} [Fintype A] [Fintype S]

def acceptance (proposal : FiniteDist A) (coin : A → ℝ) : ℝ :=
  ∑ a, proposal.weight a * coin a

theorem acceptance_bounds (proposal : FiniteDist A) (coin : A → ℝ)
    (hcoin : ∀ a, 0 ≤ coin a ∧ coin a ≤ 1) :
    0 ≤ acceptance proposal coin ∧ acceptance proposal coin ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg fun a _ => mul_nonneg (proposal.nonneg a) (hcoin a).1
  · calc
      _ ≤ ∑ a, proposal.weight a * 1 := Finset.sum_le_sum fun a _ =>
        mul_le_mul_of_nonneg_left (hcoin a).2 (proposal.nonneg a)
      _ = 1 := by simp only [mul_one, proposal.sum_one]

def acceptedLaw (proposal : FiniteDist A) (coin : A → ℝ)
    (hcoin : ∀ a, 0 ≤ coin a) (haccept : 0 < acceptance proposal coin) : FiniteDist A where
  weight a := proposal.weight a * coin a / acceptance proposal coin
  nonneg a := div_nonneg (mul_nonneg (proposal.nonneg a) (hcoin a)) haccept.le
  sum_one := by rw [← Finset.sum_div]; exact div_self (ne_of_gt haccept)

/-- One fresh proposal is accepted or replaced by the recursively obtained
remaining-attempt law. -/
def rejectionStep (proposal : FiniteDist A) (coin : A → ℝ)
    (hcoin : ∀ a, 0 ≤ coin a ∧ coin a ≤ 1) (remaining : FiniteDist A) : FiniteDist A where
  weight a := proposal.weight a * coin a + (1 - acceptance proposal coin) * remaining.weight a
  nonneg a := add_nonneg (mul_nonneg (proposal.nonneg a) (hcoin a).1)
    (mul_nonneg (sub_nonneg.mpr (acceptance_bounds proposal coin hcoin).2) (remaining.nonneg a))
  sum_one := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, remaining.sum_one, mul_one]
    change acceptance proposal coin + (1 - acceptance proposal coin) = 1
    ring

def cappedRejection (proposal : FiniteDist A) (coin : A → ℝ)
    (hcoin : ∀ a, 0 ≤ coin a ∧ coin a ≤ 1) (fallback : FiniteDist A) : ℕ → FiniteDist A
  | 0 => fallback
  | count + 1 => rejectionStep proposal coin hcoin (cappedRejection proposal coin hcoin fallback count)

/-- Exact finite retry semantics, including the exhaustion fallback. -/
theorem cappedRejection_weight (proposal : FiniteDist A) (coin : A → ℝ)
    (hcoin : ∀ a, 0 ≤ coin a ∧ coin a ≤ 1) (haccept : 0 < acceptance proposal coin)
    (fallback : FiniteDist A) (count : ℕ) (a : A) :
    (cappedRejection proposal coin hcoin fallback count).weight a =
      (1 - (1 - acceptance proposal coin) ^ count) *
        (acceptedLaw proposal coin (fun a => (hcoin a).1) haccept).weight a +
          (1 - acceptance proposal coin) ^ count * fallback.weight a := by
  induction count with
  | zero => simp [cappedRejection]
  | succ count ih =>
    simp only [cappedRejection, rejectionStep, ih, pow_succ, acceptedLaw]
    field_simp
    ring

/-- No factor depending on the size of the sample space is paid on retry
exhaustion. -/
theorem cappedRejection_tv (proposal : FiniteDist A) (coin : A → ℝ)
    (hcoin : ∀ a, 0 ≤ coin a ∧ coin a ≤ 1) (haccept : 0 < acceptance proposal coin)
    (fallback : FiniteDist A) (count : ℕ) :
    TVBound (cappedRejection proposal coin hcoin fallback count)
      (acceptedLaw proposal coin (fun a => (hcoin a).1) haccept)
      ((1 - acceptance proposal coin) ^ count) := by
  intro event
  let accepted := acceptedLaw proposal coin (fun a => (hcoin a).1) haccept
  have hfailure : 0 ≤ (1 - acceptance proposal coin) ^ count :=
    pow_nonneg (sub_nonneg.mpr (acceptance_bounds proposal coin hcoin).2) _
  have hid : (cappedRejection proposal coin hcoin fallback count).event event - accepted.event event =
      (1 - acceptance proposal coin) ^ count * (fallback.event event - accepted.event event) := by
    simp only [FiniteDist.event, cappedRejection_weight proposal coin hcoin haccept fallback count, Finset.sum_add_distrib, ← Finset.mul_sum]
    dsimp [accepted]
    ring
  change |(cappedRejection proposal coin hcoin fallback count).event event - accepted.event event| ≤ _
  rw [hid, abs_mul, abs_of_nonneg hfailure]
  have hdiff : |fallback.event event - accepted.event event| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [event_nonneg fallback event, event_le_one fallback event,
      event_nonneg accepted event, event_le_one accepted event]
  exact (mul_le_mul_of_nonneg_left hdiff hfailure).trans_eq (mul_one _)

theorem cappedRejection_exp_bound (proposal : FiniteDist A) (coin : A → ℝ)
    (hcoin : ∀ a, 0 ≤ coin a ∧ coin a ≤ 1) (haccept : 0 < acceptance proposal coin)
    (fallback : FiniteDist A) (count : ℕ) :
    TVBound (cappedRejection proposal coin hcoin fallback count)
      (acceptedLaw proposal coin (fun a => (hcoin a).1) haccept)
      (Real.exp (-(count : ℝ) * acceptance proposal coin)) := by
  apply (cappedRejection_tv proposal coin hcoin haccept fallback count).mono
  have hbase : 1 - acceptance proposal coin ≤ Real.exp (-acceptance proposal coin) := by
    linarith [Real.add_one_le_exp (-acceptance proposal coin)]
  have hh := pow_le_pow_left₀ (sub_nonneg.mpr (acceptance_bounds proposal coin hcoin).2) hbase count
  simpa only [← Real.exp_nat_mul, mul_neg, neg_mul] using hh

theorem cappedRejection_support (proposal : FiniteDist A) (coin : A → ℝ)
    (hcoin : ∀ a, 0 ≤ coin a ∧ coin a ≤ 1) (fallback : FiniteDist A)
    (a : A) (hproposal : proposal.weight a = 0) (hfallback : fallback.weight a = 0) (count : ℕ) :
    (cappedRejection proposal coin hcoin fallback count).weight a = 0 := by
  induction count with
  | zero => exact hfallback
  | succ count ih => simp only [cappedRejection, rejectionStep, hproposal, ih, zero_mul, mul_zero, add_zero]

end

end AFT.FiniteDist

namespace AFT.FiniteDist

open scoped BigOperators Classical

noncomputable section

variable {A : Type*} [Fintype A]

def positiveCoin (weight : A → ℝ) (envelope : ℝ) : A → ℝ :=
  fun a => max (weight a) 0 / envelope

omit [Fintype A] in
theorem positiveCoin_bounds (weight : A → ℝ) (envelope : ℝ) (henvelope : 0 < envelope)
    (hbound : ∀ a, max (weight a) 0 ≤ envelope) :
    ∀ a, 0 ≤ positiveCoin weight envelope a ∧ positiveCoin weight envelope a ≤ 1 := by
  intro a
  exact ⟨div_nonneg (le_max_right _ _) henvelope.le,
    (div_le_one henvelope).mpr (hbound a)⟩

theorem positiveCoin_acceptance (proposal : FiniteDist A) (weight : A → ℝ) (envelope : ℝ) :
    acceptance proposal (positiveCoin weight envelope) =
      positiveMass (weightedMass proposal weight) / envelope := by
  unfold acceptance positiveCoin positiveMass weightedMass
  simp only [← mul_div_assoc, ← Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [mul_max_of_nonneg _ _ (proposal.nonneg a), mul_zero]

theorem positiveCoin_acceptance_lower (proposal : FiniteDist A) (weight : A → ℝ)
    (envelope meanFloor : ℝ) (henvelope : 0 < envelope)
    (hmean : meanFloor ≤ signedMass (weightedMass proposal weight)) :
    meanFloor / envelope ≤ acceptance proposal (positiveCoin weight envelope) := by
  rw [positiveCoin_acceptance, positiveMass_eq]
  exact div_le_div_of_nonneg_right (hmean.trans (le_add_of_nonneg_right (negativeMass_nonneg _))) henvelope.le

/-- Rejection with the positive public weight produces exactly the
conditional positive repair; it need not evaluate the normalizer. -/
theorem acceptedLaw_positiveCoin (proposal : FiniteDist A) (weight : A → ℝ)
    (envelope : ℝ) (henvelope : 0 < envelope)
    (hmean : 0 < signedMass (weightedMass proposal weight)) :
    acceptedLaw proposal (positiveCoin weight envelope)
      (fun a => div_nonneg (le_max_right _ _) henvelope.le)
      (by rw [positiveCoin_acceptance]; exact div_pos (positiveMass_pos _ hmean) henvelope) =
        positiveRepairLaw proposal weight hmean := by
  ext a
  simp only [acceptedLaw, positiveCoin, positiveCoin_acceptance, positiveRepairLaw_weight]
  field_simp

/-- A finite retry cap implements the repaired law within the exact
exponential budget, with arbitrary legal fallback. -/
theorem positiveRepair_capped_tv (proposal : FiniteDist A) (weight : A → ℝ)
    (envelope meanFloor : ℝ) (henvelope : 0 < envelope) (hfloor : 0 < meanFloor)
    (hbound : ∀ a, max (weight a) 0 ≤ envelope)
    (hmean : meanFloor ≤ signedMass (weightedMass proposal weight))
    (fallback : FiniteDist A) (count : ℕ) :
    TVBound (cappedRejection proposal (positiveCoin weight envelope)
      (positiveCoin_bounds weight envelope henvelope hbound) fallback count)
      (positiveRepairLaw proposal weight (lt_of_lt_of_le hfloor hmean))
      (Real.exp (-(count : ℝ) * meanFloor / envelope)) := by
  have haccept : 0 < acceptance proposal (positiveCoin weight envelope) :=
    (div_pos hfloor henvelope).trans_le
      (positiveCoin_acceptance_lower proposal weight envelope meanFloor henvelope hmean)
  have hh := cappedRejection_exp_bound proposal (positiveCoin weight envelope)
    (positiveCoin_bounds weight envelope henvelope hbound) haccept fallback count
  have heq : acceptedLaw proposal (positiveCoin weight envelope)
      (fun a => (positiveCoin_bounds weight envelope henvelope hbound a).1) haccept =
      positiveRepairLaw proposal weight (lt_of_lt_of_le hfloor hmean) :=
    acceptedLaw_positiveCoin proposal weight envelope henvelope (lt_of_lt_of_le hfloor hmean)
  rw [heq] at hh
  apply hh.mono
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left
    (positiveCoin_acceptance_lower proposal weight envelope meanFloor henvelope hmean)
    (Nat.cast_nonneg count)
  calc
    _ = -((count : ℝ) * acceptance proposal (positiveCoin weight envelope)) := by ring
    _ ≤ -((count : ℝ) * (meanFloor / envelope)) := neg_le_neg h
    _ = _ := by ring

end

end AFT.FiniteDist

namespace AFT.FiniteDist

open scoped BigOperators Classical

noncomputable section

variable {A S : Type*} [Fintype A] [Fintype S]

/-- A uniform conditional comparison controls the full joint law, without
conditioning on a rare skeleton event. -/
theorem joint_tv_bound (skeleton : FiniteDist S) (first second : S → FiniteDist A)
    (error : ℝ) (h : ∀ s, TVBound (first s) (second s) error) :
    TVBound (joint skeleton first) (joint skeleton second) error := by
  intro event
  let row (s : S) : Finset A := Finset.univ.filter fun a => (s, a) ∈ event
  have hevent (law : S → FiniteDist A) :
      (joint skeleton law).event event = ∑ s, skeleton.weight s * (law s).event (row s) := by
    unfold FiniteDist.event
    have hh : (∑ pair ∈ event, (joint skeleton law).weight pair) =
        ∑ pair : S × A, if pair ∈ event then (joint skeleton law).weight pair else 0 := by
      simp only [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
    rw [hh, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro s _
    simp only [row, Finset.sum_filter, Finset.mul_sum, joint_weight, mul_ite, mul_zero]
  rw [hevent first, hevent second, ← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  calc
    _ ≤ ∑ s, skeleton.weight s * |(first s).event (row s) - (second s).event (row s)| := by
      simpa only [abs_mul, abs_of_nonneg (skeleton.nonneg _)] using
        Finset.abs_sum_le_sum_abs
          (fun s => skeleton.weight s * ((first s).event (row s) - (second s).event (row s))) Finset.univ
    _ ≤ ∑ s, skeleton.weight s * error := Finset.sum_le_sum fun s _ =>
      mul_le_mul_of_nonneg_left (h s (row s)) (skeleton.nonneg s)
    _ = error := by rw [← Finset.sum_mul, skeleton.sum_one, one_mul]

/-- Retry count for a requested dyadic exhaustion error. -/
def dyadicRetries (envelope meanFloor : ℝ) (bits : ℕ) : ℕ :=
  ⌈envelope / meanFloor * (bits : ℝ) * Real.log 2⌉₊

theorem dyadicRetries_error (envelope meanFloor : ℝ) (bits : ℕ)
    (henvelope : 0 < envelope) (hfloor : 0 < meanFloor) :
    Real.exp (-(dyadicRetries envelope meanFloor bits : ℝ) * meanFloor / envelope) ≤
      ((2 : ℝ) ^ bits)⁻¹ := by
  have hceil := Nat.le_ceil (envelope / meanFloor * (bits : ℝ) * Real.log 2)
  have hh := mul_le_mul_of_nonneg_right hceil (div_nonneg hfloor.le henvelope.le)
  have hcancel : envelope / meanFloor * (bits : ℝ) * Real.log 2 * (meanFloor / envelope) =
      (bits : ℝ) * Real.log 2 := by field_simp
  rw [hcancel] at hh
  have hexp := Real.exp_le_exp.mpr (neg_le_neg hh)
  have heq : Real.exp (-((bits : ℝ) * Real.log 2)) = ((2 : ℝ) ^ bits)⁻¹ := by
    rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [heq] at hexp
  convert hexp using 1
  congr 1
  unfold dyadicRetries
  ring

/-- Concrete finite retry budget for positive repair, with dyadic TV error. -/
theorem positiveRepair_dyadic_tv (proposal : FiniteDist A) (weight : A → ℝ)
    (envelope meanFloor : ℝ) (henvelope : 0 < envelope) (hfloor : 0 < meanFloor)
    (hbound : ∀ a, max (weight a) 0 ≤ envelope)
    (hmean : meanFloor ≤ signedMass (weightedMass proposal weight))
    (fallback : FiniteDist A) (bits : ℕ) :
    TVBound (cappedRejection proposal (positiveCoin weight envelope)
      (positiveCoin_bounds weight envelope henvelope hbound) fallback (dyadicRetries envelope meanFloor bits))
      (positiveRepairLaw proposal weight (lt_of_lt_of_le hfloor hmean))
      (((2 : ℝ) ^ bits)⁻¹) :=
  (positiveRepair_capped_tv proposal weight envelope meanFloor henvelope hfloor hbound hmean fallback _).mono
    (dyadicRetries_error envelope meanFloor bits henvelope hfloor)

end

end AFT.FiniteDist
