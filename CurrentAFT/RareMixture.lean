import AFT.RootSlice

/-!
# Finite L2 averaging supported on a rare public event

If every conditional coefficient vanishes outside a public event, its
mixture norm costs the event probability itself. Squared Cauchy--Schwarz
is applied before and after the reference average, so no square root of
that probability is lost.
-/

namespace CurrentAFT

open AFT
open scoped BigOperators Classical

noncomputable section

/-- Cauchy--Schwarz for a test supported on a finite event. -/
theorem weighted_event_square {Choice : Type*} [Fintype Choice]
    (law : FiniteDist Choice) (event : Choice → Prop) (test : Choice → ℝ)
    (hzero : ∀ choice, ¬event choice → test choice = 0) :
    law.expectation test ^ 2 ≤ law.eventMass event * law.expectation (fun choice => test choice ^ 2) := by
  let first := fun choice => Real.sqrt (law.weight choice) * (if event choice then (1 : ℝ) else 0)
  let second := fun choice => Real.sqrt (law.weight choice) * test choice
  have hdot : (∑ choice, first choice * second choice) = law.expectation test := by
    unfold FiniteDist.expectation
    apply Finset.sum_congr rfl
    intro choice _
    by_cases hevent : event choice
    · simp only [first, second, if_pos hevent, mul_one]
      calc
        _ = Real.sqrt (law.weight choice) ^ 2 * test choice := by ring
        _ = _ := by rw [Real.sq_sqrt (law.nonneg choice)]
    · simp [first, second, hevent, hzero choice hevent]
  have hfirst : (∑ choice, first choice ^ 2) = law.eventMass event := by
    unfold FiniteDist.eventMass
    apply Finset.sum_congr rfl
    intro choice _
    by_cases hevent : event choice
    · simp only [first, if_pos hevent, mul_one, Real.sq_sqrt (law.nonneg choice)]
    · simp [first, hevent]
  have hsecond : (∑ choice, second choice ^ 2) = law.expectation (fun choice => test choice ^ 2) := by
    unfold FiniteDist.expectation
    apply Finset.sum_congr rfl
    intro choice _
    simp only [second, mul_pow, Real.sq_sqrt (law.nonneg choice)]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ first second
  rwa [hdot, hfirst, hsecond] at hcs

/-- Rare-event averaging in a real finite reference Hilbert space. Vanishing
is required only on reference support; zero atoms are allowed throughout. -/
theorem rare_mixture_l2Sq {Choice Output : Type*} [Fintype Choice] [Fintype Output]
    (law : FiniteDist Choice) (reference : FiniteDist Output)
    (event : Choice → Prop) (coefficient : Choice → Output → ℝ) (bound : ℝ)
    (hzero : ∀ choice, ¬event choice → ∀ output, reference.weight output ≠ 0 → coefficient choice output = 0)
    (hbound : ∀ choice, reference.l2Sq (coefficient choice) ≤ bound ^ 2) :
    reference.l2Sq (fun output => law.expectation (fun choice => coefficient choice output)) ≤
      law.eventMass event ^ 2 * bound ^ 2 := by
  let probability := law.eventMass event
  have hprobability : 0 ≤ probability := law.eventMass_nonneg event
  have hpoint (output : Output) :
      reference.weight output * law.expectation (fun choice => coefficient choice output) ^ 2 ≤
        reference.weight output *
          (probability * law.expectation (fun choice => coefficient choice output ^ 2)) := by
    by_cases hweight : reference.weight output = 0
    · simp [hweight]
    · exact mul_le_mul_of_nonneg_left
        (weighted_event_square law event (fun choice => coefficient choice output)
          (fun choice hevent => hzero choice hevent output hweight)) (reference.nonneg output)
  have hswap :
      (∑ output, reference.weight output *
        (probability * law.expectation (fun choice => coefficient choice output ^ 2))) =
      probability * law.expectation (fun choice => reference.l2Sq (coefficient choice)) := by
    simp only [FiniteDist.expectation, FiniteDist.l2Sq]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro choice _
    apply Finset.sum_congr rfl
    intro output _
    ring
  have hconditional (choice : Choice) :
      reference.l2Sq (coefficient choice) ≤ if event choice then bound ^ 2 else 0 := by
    by_cases hevent : event choice
    · simpa only [if_pos hevent] using hbound choice
    · rw [if_neg hevent]
      apply le_of_eq
      unfold FiniteDist.l2Sq FiniteDist.expectation
      apply Finset.sum_eq_zero
      intro output _
      by_cases hweight : reference.weight output = 0
      · simp [hweight]
      · change reference.weight output * coefficient choice output ^ 2 = 0
        rw [hzero choice hevent output hweight]
        ring
  have haverage : law.expectation (fun choice => reference.l2Sq (coefficient choice)) ≤
      probability * bound ^ 2 := by
    unfold FiniteDist.expectation
    calc
      _ ≤ ∑ choice, law.weight choice * (if event choice then bound ^ 2 else 0) :=
        Finset.sum_le_sum (fun choice _ =>
          mul_le_mul_of_nonneg_left (hconditional choice) (law.nonneg choice))
      _ = _ := by
        unfold probability FiniteDist.eventMass
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro choice _
        by_cases hevent : event choice <;> simp [hevent]
  have hsum := Finset.sum_le_sum (fun output (_ : output ∈ Finset.univ) => hpoint output)
  change reference.l2Sq (fun output => law.expectation (fun choice => coefficient choice output)) ≤ _ at hsum
  rw [hswap] at hsum
  apply hsum.trans
  calc
    _ ≤ probability * (probability * bound ^ 2) :=
      mul_le_mul_of_nonneg_left haverage hprobability
    _ = _ := by ring

end

end CurrentAFT
