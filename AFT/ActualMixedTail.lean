import AFT.ActualTaggedTail

/-! # The complete actual mixed histogram tail -/

namespace AFT.V7Calibration

open Filter GaussianSource BlockProducts HistogramNormalization
open scoped BigOperators Classical Topology
noncomputable section
local instance actualMixedTailFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance actualMixedTailSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
local instance actualMixedTailSigmaDecEq {ι : Type*} {fiber : ι → Type*} : DecidableEq (Sigma fiber) := Classical.decEq _

/-- The complete marked tensor is permitted to depend jointly on every
conditioned root and on the realized common queue and its public placement. -/
abbrev ActualTaggedOutput (parameter : ℕ) (selected : Finset (blockIndex parameter)) :=
  actualRootWord parameter → (Window (queueCutoff parameter) × Equiv.Perm (blockIndex parameter)) →
    (actualMarkedSlots parameter selected → Fin (Parameters.modulus parameter)) → ℝ

/-- A finite, explicit norm of the actual marked coefficient tensors. -/
def actualTaggedEnergyBudget (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (selected : Finset (blockIndex parameter)) (tagged : ActualTaggedOutput parameter selected) : ℝ :=
  ‖fun word => fun sample => taggedCoefficientEnergy (actualReferenceLaw cutoffScale parameter beta)
    (tagged word sample) (Parameters.dimension parameter) ((parameter : ℝ) ^ 2)‖

theorem actualTaggedEnergy_le (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (selected : Finset (blockIndex parameter)) (tagged : ActualTaggedOutput parameter selected)
    (word : actualRootWord parameter)
    (sample : Window (queueCutoff parameter) × Equiv.Perm (blockIndex parameter)) :
    taggedCoefficientEnergy (actualReferenceLaw cutoffScale parameter beta) (tagged word sample)
      (Parameters.dimension parameter) ((parameter : ℝ) ^ 2) ≤
        actualTaggedEnergyBudget cutoffScale parameter beta selected tagged := by
  let energy := fun word => fun sample => taggedCoefficientEnergy (actualReferenceLaw cutoffScale parameter beta)
    (tagged word sample) (Parameters.dimension parameter) ((parameter : ℝ) ^ 2)
  have hh := (norm_le_pi_norm (energy word) sample).trans (norm_le_pi_norm energy word)
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hh)

def actualMarkedRootMass (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (selected : Finset (blockIndex parameter)) (tagged : ActualTaggedOutput parameter selected)
    (sample : Window (queueCutoff parameter) × Equiv.Perm (blockIndex parameter)) :
    ((actualMarkedSlots parameter selected ⊕ actualRemainingSlots parameter selected) → Fin (Parameters.modulus parameter)) → ℝ :=
  mixtureMass (actualRootConditionLaw parameter) (fun word =>
    actualMarkedBlockMass cutoffScale parameter beta selected (tagged word sample) word (actualQueueShifts parameter sample))

def actualMarkedRootQueueMass (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (selected : Finset (blockIndex parameter)) (tagged : ActualTaggedOutput parameter selected) :
    ((actualMarkedSlots parameter selected ⊕ actualRemainingSlots parameter selected) → Fin (Parameters.modulus parameter)) → ℝ :=
  mixtureMass (FiniteDist.retype (actualQueuePlacementLaw parameter))
    (actualMarkedRootMass cutoffScale parameter beta selected tagged)

set_option backward.isDefEq.respectTransparency false in
/-- Complete all-degree mixed tail for arbitrary actual joint marked output.
Its norm is an explicit finite coefficient expression; every bound for the
physical independent complement and both conditioned sources is proved from
the V7 parameters, with no analytic hypotheses. -/
theorem actual_complete_mixed_histogram_tail (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ selected : Finset (blockIndex parameter),
      ∀ tagged : ActualTaggedOutput parameter selected, ∀ cutoff : ℕ,
      (FiniteDist.independent (fun _ : actualMarkedSlots parameter selected ⊕ actualRemainingSlots parameter selected =>
        actualReferenceLaw cutoffScale parameter (beta parameter))).l2Sq
        (densityTail (actualReferenceLaw cutoffScale parameter (beta parameter))
          (symmetrizedMass (actualMarkedRootQueueMass cutoffScale parameter (beta parameter) selected tagged)) cutoff) ≤
        (Real.exp 1 / (parameter : ℝ) ^ 4) ^ (cutoff + 1) *
          (actualTaggedEnergyBudget cutoffScale parameter (beta parameter) selected tagged *
            (16 * Real.exp (1 + 16 * (1 + (selected.card : ℝ)) ^ 2))) := by
  filter_upwards [actual_marked_pointwise_tail_eventually cutoffScale hscale beta hbeta,
    actual_remaining_mean_exp_eventually cutoffScale hscale beta hbeta]
    with parameter hp hm selected tagged cutoff
  let reference := actualReferenceLaw cutoffScale parameter (beta parameter)
  let factor := (Real.exp 1 / (parameter : ℝ) ^ 4) ^ (cutoff + 1)
  let budget := actualTaggedEnergyBudget cutoffScale parameter (beta parameter) selected tagged
  let constant := 16 * Real.exp (1 + 16 * (1 + (selected.card : ℝ)) ^ 2)
  have hf : 0 ≤ factor := by dsimp only [factor]; positivity
  have hb : 0 ≤ budget := norm_nonneg _
  have hfixed (sample : Window (queueCutoff parameter) × Equiv.Perm (blockIndex parameter)) :
      (FiniteDist.independent (fun _ : actualMarkedSlots parameter selected ⊕ actualRemainingSlots parameter selected => reference)).l2Sq
        (densityTail reference (symmetrizedMass (actualMarkedRootMass cutoffScale parameter (beta parameter) selected tagged sample)) cutoff) ≤
        factor * (budget * constant) := by
    apply (symmetrized_mixture_tail_energy_le reference (actualRootConditionLaw parameter)
      (fun word => actualMarkedBlockMass cutoffScale parameter (beta parameter) selected (tagged word sample)
        word (actualQueueShifts parameter sample)) cutoff).trans
    have hpoint (word : actualRootWord parameter) :
        (FiniteDist.independent (fun _ : actualMarkedSlots parameter selected ⊕ actualRemainingSlots parameter selected => reference)).l2Sq
          (densityTail reference (symmetrizedMass (actualMarkedBlockMass cutoffScale parameter (beta parameter)
            selected (tagged word sample) word (actualQueueShifts parameter sample))) cutoff) ≤
        factor * (budget * (16 * Real.exp (8 * ‖actualRemainingMean cutoffScale parameter (beta parameter)
          word (actualQueueShifts parameter sample) selected‖ ^ 2))) := by
      apply (hp selected (tagged word sample) word (actualQueueShifts parameter sample)
        (actualQueueShifts_bound parameter sample) cutoff).trans
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (actualTaggedEnergy_le cutoffScale parameter (beta parameter) selected tagged word sample)
        (by positivity)) hf
    have hh := Finset.sum_le_sum (fun word (_ : word ∈ Finset.univ) =>
      mul_le_mul_of_nonneg_left (hpoint word) ((actualRootConditionLaw parameter).nonneg word))
    have heq : (∑ word, (actualRootConditionLaw parameter).weight word *
        (factor * (budget * (16 * Real.exp (8 * ‖actualRemainingMean cutoffScale parameter (beta parameter)
          word (actualQueueShifts parameter sample) selected‖ ^ 2))))) =
        (factor * budget * 16) * (actualRootConditionLaw parameter).expectation (fun word =>
          Real.exp (8 * ‖actualRemainingMean cutoffScale parameter (beta parameter)
            word (actualQueueShifts parameter sample) selected‖ ^ 2)) := by
      unfold FiniteDist.expectation
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro word _
      ring
    rw [heq] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left (hm sample selected) (by positivity)).trans_eq (by dsimp only [constant]; ring))
  apply (symmetrized_mixture_tail_energy_le reference (FiniteDist.retype (actualQueuePlacementLaw parameter))
    (actualMarkedRootMass cutoffScale parameter (beta parameter) selected tagged) cutoff).trans
  calc
    _ ≤ ∑ sample, (FiniteDist.retype (actualQueuePlacementLaw parameter)).weight sample * (factor * (budget * constant)) :=
      Finset.sum_le_sum fun sample _ => mul_le_mul_of_nonneg_left (hfixed sample) (FiniteDist.nonneg _ _)
    _ = _ := by rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]

end
end AFT.V7Calibration
