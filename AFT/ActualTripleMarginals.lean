import AFT.ActualTripleEnergy
import AFT.TripleMarginals
import AFT.FirstCoefficientFormula

/-! # Exact body marginal of the shared-source physical triple -/

namespace AFT

open scoped BigOperators Classical

noncomputable section

local instance actualTripleMarginalsFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

namespace BlockDensity

variable {Source : Type*} [Fintype Source]

/-- Marking part of an atom leaves the underlying source expectation exact. -/
theorem activatedSource_expectation (source : FiniteDist Source) (atom : Source) (activation : ℝ)
    (ha0 : 0 ≤ activation) (ha : activation ≤ source.weight atom) (function : Source → ℝ) :
    (activatedSource source atom activation ha0 ha).expectation
      (Sum.elim (fun _ => function atom) function) = source.expectation function := by
  simp only [FiniteDist.expectation, activatedSource, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr, Fintype.sum_unique, unmarkedSourceWeight,
    sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  ring

end BlockDensity

namespace PhysicalBlockTensors

variable {Source Color : Type*} [Fintype Source] [Fintype Color]

/-- The independent center's conditional law depends on the shared source;
integrating the two endpoint coordinates preserves exactly that mixture. -/
theorem sharedSourceTriple_body_independent_endpoints (source : FiniteDist Source)
    (pair : Source → FiniteDist (Color × Color)) (body : Source → FiniteDist Color) (color : Color) :
    ((sharedSourceTriple source pair (fun sample _ _ => body sample)).map (fun word => word 2)).weight color =
      source.expectation (fun sample => (body sample).weight color) := by
  rw [sharedSourceTriple_body_marginal]
  simp only [BlockDensity.attachedMass]
  conv_lhs => arg 2; ext first; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  unfold FiniteDist.expectation
  apply Finset.sum_congr rfl
  intro sample _
  have hmass : (∑ first, ∑ second, (pair sample).weight (first, second)) = 1 := by
    simpa only [Fintype.sum_prod_type] using (pair sample).sum_one
  calc
    _ = (∑ first, ∑ second, (pair sample).weight (first, second)) *
        (source.weight sample * (body sample).weight color) := by
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro first _
      apply Finset.sum_congr rfl
      intro second _
      ring
    _ = _ := by rw [hmass, one_mul]

end PhysicalBlockTensors

namespace V7Calibration

open GaussianSource

/-- The activated/inactive physical source has precisely the original
second Gaussian as its unflagged integer marginal. -/
theorem actualActivatedSource_shift_expectation (cutoffScale : ℝ) (parameter : ℕ) (function : ℤ → ℝ) :
    (actualActivatedSource cutoffScale parameter).expectation
      (fun sample => function (actualSourceShift cutoffScale parameter sample)) =
      (windowGaussian (10 * parameter) (legCutoff cutoffScale parameter - 1)).expectation
        (fun sample => function sample) := by
  have hh := BlockDensity.activatedSource_expectation
    (windowGaussian (10 * parameter) (legCutoff cutoffScale parameter - 1))
    (windowZero (legCutoff cutoffScale parameter - 1)) (v7Activation cutoffScale parameter)
    (by unfold v7Activation GaussianSource.activation; exact mul_nonneg (by positivity) (FiniteDist.nonneg _ _))
    (activation_le_second_atom _ _ _ _) (fun source => function (source : ℤ))
  convert hh using 1
  congr 1
  funext sample
  cases sample <;> rfl

/-- In particular, activation creates no change whatsoever in the true
attached body's marginal; its root and common queue remain fixed. -/
theorem actual_fixed_root_triple_body_marginal (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (root queue : ℤ) (color : Fin (Parameters.modulus parameter)) :
    ((actualFixedRootTripleLaw cutoffScale parameter beta root queue).map (fun word => word 2)).weight color =
      (windowGaussian (10 * parameter) (legCutoff cutoffScale parameter - 1)).expectation
        (fun source => (actualShiftedBodyLaw cutoffScale parameter beta (root + source + queue)).weight color) := by
  change ((PhysicalBlockTensors.sharedSourceTriple (actualActivatedSource cutoffScale parameter)
    (actualPairBranch cutoffScale parameter beta)
    (fun sample _ _ => actualShiftedBodyLaw cutoffScale parameter beta
      (root + actualSourceShift cutoffScale parameter sample + queue))).map (fun word => word 2)).weight color = _
  rw [PhysicalBlockTensors.sharedSourceTriple_body_independent_endpoints]
  exact actualActivatedSource_shift_expectation cutoffScale parameter
    (fun shift => (actualShiftedBodyLaw cutoffScale parameter beta (root + shift + queue)).weight color)

end V7Calibration

end

end AFT
