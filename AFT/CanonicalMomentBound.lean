import AFT.MomentActivity

/-! # Palette-independent fixed moments of genuine canonical U-statistics -/

set_option maxHeartbeats 800000

namespace AFT.CanonicalMoments

open scoped BigOperators Classical

noncomputable section


variable {Slot Pool Color : Type*} [Fintype Slot] [Fintype Pool] [Fintype Color]

/-- An explicit constant depending only on kernel order and moment order. -/
def momentConstant (order power : ℕ) : ℝ :=
  (power * order + 1 : ℕ) * (2 : ℝ) ^ (power * order) * (power * order : ℕ) ^ (power * order)

/-- Complete canonical moment estimate under the actual exact distinct-index
normalizer. The constant depends only on fixed orders, with all population
powers and all arbitrary joint-kernel mixed fibers retained. -/
theorem statistic_moment_le_activity (reference : FiniteDist Color) (kernel : (Slot → Color) → ℝ)
    (hcanonical : Hoeffding.Canonical (fun _ : Slot => reference) Finset.univ kernel)
    (power : ℕ) (hpopulation : 0 < Fintype.card Pool)
    (hlarge : 2 * Fintype.card Slot ≤ Fintype.card Pool) :
    (FiniteDist.independent (fun _ : Pool => reference)).expectation
      (fun word => statistic kernel word ^ power) ≤
      momentConstant (Fintype.card Slot) power *
        MixedKernel.activity (fun _ : Slot => 1 / Real.sqrt (Fintype.card Pool))
          (fun _ => reference) kernel ^ power := by
  let occurrences := power * Fintype.card Slot
  let activity := MixedKernel.activity (fun _ : Slot => 1 / Real.sqrt (Fintype.card Pool))
    (fun _ => reference) kernel
  let denominator : ℝ := ((Fintype.card Pool).descFactorial (Fintype.card Slot) : ℝ) ^ power
  let survivors := Finset.univ.filter (NoSingleton (Copy := Fin power) (Slot := Slot) (Pool := Pool))
  let term (pattern : Fin power → Slot ↪ Pool) :=
    (FiniteDist.independent (fun _ : Pool => reference)).expectation (patternProduct kernel pattern) / denominator
  have ha : 0 ≤ activity := MixedKernel.activity_nonneg _ _ _ (fun _ => by positivity)
  have hden : 0 < denominator := by
    apply pow_pos
    exact_mod_cast (Nat.descFactorial_pos.mpr (by omega : Fintype.card Slot ≤ Fintype.card Pool))
  have hmaps (pattern : Fin power → Slot ↪ Pool) (_ : pattern ∈ survivors) :
      (usedLabels pattern).card ∈ Finset.range (occurrences + 1) := by
    have hh := usedLabels_card_le_occurrences pattern
    simp only [Fintype.card_fin] at hh
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hh)
  have hgroup := Finset.sum_fiberwise_of_maps_to hmaps term
  have hused (used : ℕ) (hused : used ∈ Finset.range (occurrences + 1)) :
      (∑ pattern ∈ survivors.filter (fun pattern => (usedLabels pattern).card = used), term pattern) ≤
        (2 : ℝ) ^ occurrences * ((occurrences : ℝ) ^ occurrences * activity ^ power) := by
    let selected := survivors.filter (fun pattern => (usedLabels pattern).card = used)
    have hcount : (selected.card : ℝ) ≤
        ((Fintype.card Pool).descFactorial used : ℝ) * (occurrences : ℝ) ^ occurrences := by
      have hh := noSingletonPatterns_card_le (Slot := Slot) (Pool := Pool) (Copy := Fin power) used
      simp only [Fintype.card_fin] at hh
      have heq : selected = Finset.univ.filter (fun pattern : Fin power → Slot ↪ Pool =>
          NoSingleton pattern ∧ (usedLabels pattern).card = used) := by
        ext pattern
        simp only [selected, survivors, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [heq]
      have hh' : (Finset.univ.filter (fun pattern : Fin power → Slot ↪ Pool =>
          NoSingleton pattern ∧ (usedLabels pattern).card = used)).card ≤
          (Fintype.card Pool).descFactorial used * occurrences ^ occurrences := by
        convert hh using 1
        congr 1
        ext pattern
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact_mod_cast hh'
    have hterm (pattern : Fin power → Slot ↪ Pool) (hpattern : pattern ∈ selected) :
        term pattern ≤ (Fintype.card Pool : ℝ) ^ (occurrences - used) * activity ^ power / denominator := by
      have hm := Finset.mem_filter.mp hpattern
      have hs : NoSingleton pattern := (Finset.mem_filter.mp hm.1).2
      have hh := pattern_expectation_activity_le reference kernel pattern hs hpopulation
      rw [hm.2] at hh
      apply div_le_div_of_nonneg_right _ hden.le
      exact (le_abs_self _).trans hh
    calc
      _ ≤ (selected.card : ℝ) * ((Fintype.card Pool : ℝ) ^ (occurrences - used) * activity ^ power / denominator) := by
        simpa only [nsmul_eq_mul] using Finset.sum_le_card_nsmul selected term
          ((Fintype.card Pool : ℝ) ^ (occurrences - used) * activity ^ power / denominator) hterm
      _ ≤ (((Fintype.card Pool).descFactorial used : ℝ) * (occurrences : ℝ) ^ occurrences) *
          ((Fintype.card Pool : ℝ) ^ (occurrences - used) * activity ^ power / denominator) :=
        mul_le_mul_of_nonneg_right hcount (by positivity)
      _ = (((Fintype.card Pool).descFactorial used : ℝ) * (Fintype.card Pool : ℝ) ^ (occurrences - used) / denominator) *
          ((occurrences : ℝ) ^ occurrences * activity ^ power) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (collision_normalizer_bound (Fintype.card Pool) (Fintype.card Slot) power used hpopulation hlarge
          (Nat.le_of_lt_succ (Finset.mem_range.mp hused))) (by positivity)
  rw [statistic_moment_surviving_expansion reference kernel hcanonical power]
  change (∑ pattern ∈ survivors, _) / denominator ≤ _
  rw [Finset.sum_div]
  change (∑ pattern ∈ survivors, term pattern) ≤ _
  rw [← hgroup]
  apply (Finset.sum_le_sum hused).trans_eq
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, momentConstant]
  dsimp only [occurrences, activity]
  push_cast
  ring

/-- Every fixed even absolute moment is bounded by the full mixed input
activity, with no rank restriction and no alphabet-dependent constant. -/
theorem statistic_even_moment_le_activity (reference : FiniteDist Color) (kernel : (Slot → Color) → ℝ)
    (hcanonical : Hoeffding.Canonical (fun _ : Slot => reference) Finset.univ kernel)
    (moment : ℕ) (hpopulation : 0 < Fintype.card Pool)
    (hlarge : 2 * Fintype.card Slot ≤ Fintype.card Pool) :
    (FiniteDist.independent (fun _ : Pool => reference)).expectation
      (fun word => |statistic kernel word| ^ (2 * moment)) ≤
      momentConstant (Fintype.card Slot) (2 * moment) *
        MixedKernel.activity (fun _ : Slot => 1 / Real.sqrt (Fintype.card Pool))
          (fun _ => reference) kernel ^ (2 * moment) := by
  simpa only [pow_mul, sq_abs] using statistic_moment_le_activity
    reference kernel hcanonical (2 * moment) hpopulation hlarge

end

end AFT.CanonicalMoments
