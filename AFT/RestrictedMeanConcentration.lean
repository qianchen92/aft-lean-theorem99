import AFT.ActualFullTail
import AFT.RestrictedBlockMean

/-! # Root-conditioned concentration after marking arbitrary physical blocks -/

namespace AFT.V7Calibration

open Filter GaussianSource BlockProducts FiniteConcentration
open scoped BigOperators Classical Topology
noncomputable section
local instance restrictedMeanConcentrationFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance restrictedMeanConcentrationSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _

def actualRemainingMean (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (word : actualRootWord parameter) (queue : blockIndex parameter → ℤ) (selected : Finset (blockIndex parameter)) :
    EuclideanSpace ℝ (Fin (Parameters.modulus parameter)) :=
  actualNormalizedBlockMean cutoffScale parameter beta word queue -
    actualRemovedMean cutoffScale parameter beta word queue selected

/-- Marking any fixed number of blocks costs only a constant depending on
that number, after conditioning on the actual zero-sum root word. Arbitrary
dependence of the marked output on those roots remains allowed. -/
theorem actual_remaining_mean_exp_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ sample, ∀ selected : Finset (blockIndex parameter),
      (actualRootConditionLaw parameter).expectation (fun word =>
        Real.exp (8 * ‖actualRemainingMean cutoffScale parameter (beta parameter)
          word (actualQueueShifts parameter sample) selected‖ ^ 2)) ≤
        Real.exp (1 + 16 * (1 + (selected.card : ℝ)) ^ 2) := by
  filter_upwards [actual_conditional_mean_bound_eventually cutoffScale hscale beta hbeta,
    actual_centered_root_bound_eventually cutoffScale hscale beta hbeta,
    actual_removed_mean_bound_eventually cutoffScale hscale beta hbeta,
    actual_root_tail_exponent_eventually,
    actual_joint_mean_zero_eventually cutoffScale hscale beta hbeta,
    eventually_ge_atTop 1000000000]
    with parameter hm hb hr he hzero hp sample selected
  let root := fun _ : Fin (Parameters.bodies parameter) =>
    windowGaussian (v7RootWidth parameter) (v7RootCutoff parameter)
  let event := fun word : actualRootWord parameter =>
    RootSlice.integerSum (fun z : Window (v7RootCutoff parameter) => (z : ℤ)) word = 0
  let queue := actualQueueShifts parameter sample
  let value := actualCenteredRootValue cutoffScale parameter (beta parameter) queue
  let mean := vectorMean (actualRootConditionLaw parameter)
    (fun word => actualNormalizedBlockMean cutoffScale parameter (beta parameter) word queue)
  let shift := fun word => mean - actualRemovedMean cutoffScale parameter (beta parameter) word queue selected
  have hprob : 0 < (FiniteDist.independent root).eventMass event :=
    window_root_probability_positive (v7RootWidth parameter) (v7RootCutoff parameter) (Parameters.bodies parameter)
  have hprobidentity : (FiniteDist.independent root).eventMass event =
      rootProbability (v7RootWidth parameter) (v7RootCutoff parameter) (Parameters.bodies parameter) 0 := rfl
  have hbudget := actual_root_budget parameter hp
  have hmeanbound : ‖mean‖ ≤ 1 := by
    apply (hm (actualRootConditionLaw parameter) hzero sample).trans
    have hx : (1184 : ℝ) ≤ parameter := by exact_mod_cast (by omega : 1184 ≤ parameter)
    have hx1 : (1 : ℝ) ≤ parameter := by linarith
    have hpower : (parameter : ℝ) ≤ (parameter : ℝ) ^ 7 := by
      simpa only [pow_one] using pow_le_pow_right₀ hx1 (by norm_num : 1 ≤ 7)
    apply (div_le_one (by positivity : (0 : ℝ) < (parameter : ℝ) ^ 7)).mpr
    exact hx.trans hpower
  have hshift : ∀ word, ‖shift word‖ ≤ 1 + (selected.card : ℝ) := by
    intro word
    exact (norm_sub_le _ _).trans (add_le_add hmeanbound
      (hr word queue (actualQueueShifts_bound parameter sample) selected))
  have hh := conditioned_shifted_hilbert_sum_square_mgf_instance (Parameters.bodies parameter) root value
    (fun _ => 296 / (parameter : ℝ) ^ 47)
    (fun index => actualCenteredRootValue_mean cutoffScale parameter (beta parameter) queue index)
    (fun _ => by positivity) (hb queue (actualQueueShifts_bound parameter sample))
    event hprob hbudget.1 shift (1 + (selected.card : ℝ)) (by positivity) hshift
    8 (by norm_num) (by nlinarith only [hbudget.2.2])
  have hidentity (word : actualRootWord parameter) :
      ((∑ index, value index (word index)) -
        vectorMean ((FiniteDist.independent root).condition event hprob)
          (fun word => ∑ index, value index (word index))) + shift word =
      actualRemainingMean cutoffScale parameter (beta parameter) word queue selected := by
    have hi : ((∑ index, value index (word index)) -
        vectorMean ((FiniteDist.independent root).condition event hprob)
          (fun word => ∑ index, value index (word index))) + mean =
        actualNormalizedBlockMean cutoffScale parameter (beta parameter) word queue :=
      actual_mean_centering_identity cutoffScale parameter (beta parameter)
        (actualRootConditionLaw parameter) word queue
    dsimp only [shift, actualRemainingMean]
    rw [← hi]
    abel

  simp only [hidentity] at hh
  rw [hprobidentity] at hh
  apply hh.trans
  apply Real.exp_le_exp.mpr
  nlinarith only [he, sq_nonneg (1184 / (parameter : ℝ) ^ 7)]

end
end AFT.V7Calibration
