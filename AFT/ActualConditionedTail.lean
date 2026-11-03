import AFT.ActualRootLaw
import AFT.ConditionalMeanInstance
import AFT.ActualBlockTail
import AFT.V7RootTailExponent

/-! # Complete actual histogram tails after root conditioning and common queue -/

namespace AFT.V7Calibration

open Filter GaussianSource BlockProducts HistogramNormalization FiniteConcentration
open scoped BigOperators Classical Topology

noncomputable section

local instance actualConditionedTailFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance actualConditionedTailSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
local instance actualConditionedTailSigmaDecEq (parameter : ℕ) : DecidableEq (Sigma (blockSlots parameter)) := Classical.decEq _

/-- The exact algebraic mean identity needed from physical source placement. -/
def ActualJointMeanZero (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) : Prop :=
  vectorMean (FiniteDist.retype (actualQueuePlacementLaw parameter))
    (fun sample => vectorMean (actualRootConditionLaw parameter) (fun word =>
      actualNormalizedBlockMean cutoffScale parameter beta word (actualQueueShifts parameter sample))) = 0

/-- The conditioning exponent is proved for the actual source and actual
normalized output mean; the mean-zero input is the exact calibration identity. -/
theorem actual_conditioned_mean_exp_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter)
    (hmean : ∀ᶠ parameter in atTop, ActualJointMeanZero cutoffScale parameter (beta parameter)) :
    ∀ᶠ parameter in atTop, ∀ sample,
      (actualRootConditionLaw parameter).expectation (fun word =>
        Real.exp (8 * ‖actualNormalizedBlockMean cutoffScale parameter (beta parameter)
          word (actualQueueShifts parameter sample)‖ ^ 2)) ≤ Real.exp 1 := by
  filter_upwards [actual_conditional_mean_bound_eventually cutoffScale hscale beta hbeta,
    actual_centered_root_bound_eventually cutoffScale hscale beta hbeta,
    actual_root_tail_exponent_eventually, hmean, eventually_ge_atTop 1000000000]
    with parameter hm hb he hzero hp sample
  let root := fun _ : Fin (Parameters.bodies parameter) =>
    windowGaussian (v7RootWidth parameter) (v7RootCutoff parameter)
  let event := fun word : actualRootWord parameter => RootSlice.integerSum (fun z : Window (v7RootCutoff parameter) => (z : ℤ)) word = 0
  let queue := actualQueueShifts parameter sample
  let value := actualCenteredRootValue cutoffScale parameter (beta parameter) queue
  let mean := vectorMean (actualRootConditionLaw parameter)
    (fun word => actualNormalizedBlockMean cutoffScale parameter (beta parameter) word queue)
  have hprob : 0 < (FiniteDist.independent root).eventMass event :=
    window_root_probability_positive (v7RootWidth parameter) (v7RootCutoff parameter) (Parameters.bodies parameter)
  have hprobidentity : (FiniteDist.independent root).eventMass event =
      rootProbability (v7RootWidth parameter) (v7RootCutoff parameter) (Parameters.bodies parameter) 0 := rfl
  have hbudget := actual_root_budget parameter hp
  have hmeanbound : ‖mean‖ ≤ 1184 / (parameter : ℝ) ^ 7 :=
    hm (actualRootConditionLaw parameter) hzero sample
  have hh := conditioned_shifted_hilbert_sum_square_mgf_instance (Parameters.bodies parameter) root value
    (fun _ => 296 / (parameter : ℝ) ^ 47)
    (fun index => actualCenteredRootValue_mean cutoffScale parameter (beta parameter) queue index)
    (fun _ => by positivity)
    (hb queue (actualQueueShifts_bound parameter sample)) event hprob hbudget.1
    (fun _ => mean) (1184 / (parameter : ℝ) ^ 7) (by positivity) (fun _ => hmeanbound)
    8 (by norm_num) (by nlinarith only [hbudget.2.2])
  have hidentity (word : actualRootWord parameter) :
      ((∑ index, value index (word index)) -
        vectorMean ((FiniteDist.independent root).condition event hprob)
          (fun word => ∑ index, value index (word index))) + mean =
      actualNormalizedBlockMean cutoffScale parameter (beta parameter) word queue :=
    actual_mean_centering_identity cutoffScale parameter (beta parameter)
      (actualRootConditionLaw parameter) word queue
  simp only [hidentity] at hh
  have hbound : (actualRootConditionLaw parameter).expectation (fun word =>
      Real.exp (8 * ‖actualNormalizedBlockMean cutoffScale parameter (beta parameter) word queue‖ ^ 2)) ≤
      Real.exp (16 * (1184 / (parameter : ℝ) ^ 7) ^ 2 +
        (2048 * ∑ _ : Fin (Parameters.bodies parameter), (296 / (parameter : ℝ) ^ 47) ^ 2) *
          Real.log (2 * Real.exp 1 /
            rootProbability (v7RootWidth parameter) (v7RootCutoff parameter) (Parameters.bodies parameter) 0)) := by
    rw [hprobidentity] at hh
    convert hh using 1; norm_num
  exact hbound.trans (Real.exp_le_exp.mpr he)

/-- The literal independent blocks, averaged over the entire conditioned
root word at one realized common queue and placement. -/
def actualConditionalRootMass (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (sample : Window (queueCutoff parameter) × Equiv.Perm (blockIndex parameter)) :
    (Sigma (blockSlots parameter) → Fin (Parameters.modulus parameter)) → ℝ :=
  mixtureMass (actualRootConditionLaw parameter) (fun word => blockMass (blockSlots parameter)
    (actualBlockFamily cutoffScale parameter beta (actualRootField parameter word) (actualQueueShifts parameter sample)))

/-- Both shared sources are normalized actual finite probability mixtures. -/
def actualRootQueueMass (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) :
    (Sigma (blockSlots parameter) → Fin (Parameters.modulus parameter)) → ℝ :=
  mixtureMass (FiniteDist.retype (actualQueuePlacementLaw parameter))
    (actualConditionalRootMass cutoffScale parameter beta)

set_option backward.isDefEq.respectTransparency false in
/-- The complete physical histogram tail, including all orders, is uniform
after the actual zero-sum root condition and the one shared queue. -/
theorem actual_root_queue_complete_tail_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter)
    (hmean : ∀ᶠ parameter in atTop, ActualJointMeanZero cutoffScale parameter (beta parameter)) :
    ∀ᶠ parameter in atTop, ∀ cutoff : ℕ,
      (FiniteDist.independent (fun _ : Sigma (blockSlots parameter) =>
        actualReferenceLaw cutoffScale parameter (beta parameter))).l2Sq
        (densityTail (actualReferenceLaw cutoffScale parameter (beta parameter))
          (symmetrizedMass (actualRootQueueMass cutoffScale parameter (beta parameter))) cutoff) ≤
        (Real.exp 1 / (parameter : ℝ) ^ 4) ^ (cutoff + 1) * (16 * Real.exp 1) := by
  filter_upwards [actual_pointwise_complete_tail_eventually cutoffScale hscale beta hbeta,
    actual_conditioned_mean_exp_eventually cutoffScale hscale beta hbeta hmean]
    with parameter hp hm cutoff
  let reference := actualReferenceLaw cutoffScale parameter (beta parameter)
  let factor := (Real.exp 1 / (parameter : ℝ) ^ 4) ^ (cutoff + 1)
  have hf : 0 ≤ factor := by dsimp only [factor]; positivity
  have hfixed (sample : Window (queueCutoff parameter) × Equiv.Perm (blockIndex parameter)) :
      (FiniteDist.independent (fun _ : Sigma (blockSlots parameter) => reference)).l2Sq
        (densityTail reference (symmetrizedMass (actualConditionalRootMass cutoffScale parameter (beta parameter) sample)) cutoff) ≤
        factor * (16 * Real.exp 1) := by
    apply (symmetrized_mixture_tail_energy_le reference (actualRootConditionLaw parameter)
      (fun word => blockMass (blockSlots parameter) (actualBlockFamily cutoffScale parameter (beta parameter)
        (actualRootField parameter word) (actualQueueShifts parameter sample))) cutoff).trans
    have hh := Finset.sum_le_sum (fun word (_ : word ∈ Finset.univ) =>
      mul_le_mul_of_nonneg_left (hp word (actualQueueShifts parameter sample)
        (actualQueueShifts_bound parameter sample) cutoff) ((actualRootConditionLaw parameter).nonneg word))
    have heq : (∑ word, (actualRootConditionLaw parameter).weight word *
        (factor * (16 * Real.exp (8 * ‖actualNormalizedBlockMean cutoffScale parameter (beta parameter)
          word (actualQueueShifts parameter sample)‖ ^ 2)))) =
        (factor * 16) * (actualRootConditionLaw parameter).expectation (fun word =>
          Real.exp (8 * ‖actualNormalizedBlockMean cutoffScale parameter (beta parameter)
            word (actualQueueShifts parameter sample)‖ ^ 2)) := by
      unfold FiniteDist.expectation
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro word _
      ring
    change _ ≤ ∑ word, (actualRootConditionLaw parameter).weight word * (factor * (16 * _)) at hh
    rw [heq] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left (hm sample) (mul_nonneg hf (by norm_num))).trans_eq (by ring))
  apply (symmetrized_mixture_tail_energy_le reference (FiniteDist.retype (actualQueuePlacementLaw parameter))
    (actualConditionalRootMass cutoffScale parameter (beta parameter)) cutoff).trans
  calc
    _ ≤ ∑ sample, (FiniteDist.retype (actualQueuePlacementLaw parameter)).weight sample * (factor * (16 * Real.exp 1)) :=
      Finset.sum_le_sum fun sample _ => mul_le_mul_of_nonneg_left (hfixed sample) (FiniteDist.nonneg _ _)
    _ = _ := by rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]

end

end AFT.V7Calibration
