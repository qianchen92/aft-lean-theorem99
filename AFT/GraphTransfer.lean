import AFT.FiniteRefresh

/-! # Actual mixed-fiber contraction of one finite collision-graph step -/

namespace AFT.CanonicalMoments

open scoped BigOperators Classical

variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]

omit [Fintype Slot] [Fintype Color] in
/-- Enlarging a declared dependence set preserves dependence. -/
theorem dependsOn_mono (small large : Finset Slot) (function : (Slot → Color) → ℝ)
    (hsmall : Hoeffding.DependsOn small function) (hsubset : small ⊆ large) :
    Hoeffding.DependsOn large function := by
  intro first second hequal
  exact hsmall first second (fun slot hslot => hequal slot (hsubset hslot))

omit [Fintype Slot] [Fintype Color] in
/-- The squared kernel has exactly the same coordinate dependence. -/
theorem dependsOn_square (selected : Finset Slot) (function : (Slot → Color) → ℝ)
    (hdepends : Hoeffding.DependsOn selected function) :
    Hoeffding.DependsOn selected (fun word => function word ^ 2) := by
  intro first second hequal
  dsimp only
  rw [hdepends first second hequal]

/-- Refreshing a dependent square integrates precisely its remaining
arguments, yielding the actual mixed-fiber square. -/
theorem refresh_square_eq_fiberSq (reference : Slot → FiniteDist Color)
    (resampled selected : Finset Slot) (function : (Slot → Color) → ℝ)
    (hdepends : Hoeffding.DependsOn selected function) (word : Slot → Color) :
    refresh reference resampled (fun values => function values ^ 2) word =
      MixedKernel.fiberSq reference function (selected \ resampled) word := by
  rw [refresh_eq_freeze]
  unfold MixedKernel.fiberSq FiniteDist.l2Sq FiniteDist.expectation
  apply Finset.sum_congr rfl
  intro integrated _
  dsimp only
  congr 2
  apply hdepends
  intro slot hslot
  by_cases hs : slot ∈ resampled <;> simp [MixedKernel.freeze, hslot, hs]

/-- One true graph-elimination step. A fresh argument contributes its L2
norm; an argument used both before and after this copy contributes only the
prescribed fixed-coordinate supremum. This holds for a genuine joint kernel. -/
theorem graph_step_energy_le (reference : Slot → FiniteDist Color)
    (active selected ending : Finset Slot) (kernel input : (Slot → Color) → ℝ)
    (hkernel : Hoeffding.DependsOn selected kernel) (hinput : Hoeffding.DependsOn active input) :
    (FiniteDist.independent reference).l2Sq
      (refresh reference ending (fun word => kernel word * input word)) ≤
      MixedKernel.fiberNorm reference kernel (selected \ ((selected \ active) ∪ ending)) ^ 2 *
        (FiniteDist.independent reference).l2Sq input := by
  let fresh := selected \ active
  let first := refresh reference ending (fun word => kernel word ^ 2)
  let second := refresh reference ending (fun word => input word ^ 2)
  let bound := MixedKernel.fiberNorm reference kernel (selected \ (fresh ∪ ending)) ^ 2
  have hsecond (word : Slot → Color) : 0 ≤ second word :=
    Finset.sum_nonneg fun value _ => mul_nonneg ((refreshLaw reference ending word).nonneg _) (sq_nonneg _)
  have hdepends : Hoeffding.DependsOn freshᶜ second := by
    apply dependsOn_mono (active \ ending) freshᶜ second
      (refresh_dependsOn reference ending active _ (dependsOn_square active input hinput))
    intro slot hslot
    simp only [fresh, Finset.mem_compl, Finset.mem_sdiff, not_and]
    intro _
    exact not_not_intro (Finset.mem_sdiff.mp hslot).1
  have hfirst (word : Slot → Color) : refresh reference fresh first word ≤ bound := by
    rw [refresh_refresh, refresh_square_eq_fiberSq reference _ selected kernel hkernel]
    exact MixedKernel.fiberSq_le_norm_sq reference kernel _ word
  have hpoint (word : Slot → Color) :
      refresh reference ending (fun values => kernel values * input values) word ^ 2 ≤ first word * second word :=
    expectation_mul_sq_le (refreshLaw reference ending word) kernel input
  have hcs : (FiniteDist.independent reference).l2Sq
      (refresh reference ending (fun word => kernel word * input word)) ≤
      (FiniteDist.independent reference).expectation (fun word => first word * second word) :=
    Finset.sum_le_sum fun word _ => mul_le_mul_of_nonneg_left (hpoint word)
      ((FiniteDist.independent reference).nonneg word)
  apply hcs.trans
  rw [← expectation_refresh reference fresh (fun word => first word * second word)]
  have heq : refresh reference fresh (fun word => first word * second word) =
      (fun word => refresh reference fresh first word * second word) :=
    funext (refresh_mul_fixed reference fresh first second hdepends)
  rw [heq]
  have hh : (FiniteDist.independent reference).expectation
      (fun word => refresh reference fresh first word * second word) ≤
      (FiniteDist.independent reference).expectation (fun word => bound * second word) :=
    Finset.sum_le_sum fun word _ => mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (hfirst word) (hsecond word)) ((FiniteDist.independent reference).nonneg word)
  apply hh.trans_eq
  have hfactor : (FiniteDist.independent reference).expectation (fun word => bound * second word) =
      bound * (FiniteDist.independent reference).expectation second := by
    unfold FiniteDist.expectation
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro word _
    ring
  rw [hfactor, expectation_refresh]
  rfl

end AFT.CanonicalMoments
