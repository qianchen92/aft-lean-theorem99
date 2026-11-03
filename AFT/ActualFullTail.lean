import AFT.ActualConditionedTail
import AFT.ActualPhysicalMean

/-! # Unconditional complete histogram tail of the actual V7 sampler -/

namespace AFT.V7Calibration

open Filter GaussianSource BlockProducts HistogramNormalization
open scoped BigOperators Classical Topology
noncomputable section
local instance actualFullTailFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance actualFullTailSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
local instance actualFullTailSigmaDecEq (parameter : ℕ) : DecidableEq (Sigma (blockSlots parameter)) := Classical.decEq _

/-- The whole histogram likelihood has a complete all-orders tail bound for
the actual independent physical blocks, zero-sum conditioned Gaussian roots,
and one shared queue with its actual random placement. Every analytic budget
and the exact mean calibration are proved from the V7 definitions. -/
theorem actual_complete_histogram_tail (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ cutoff : ℕ,
      (FiniteDist.independent (fun _ : Sigma (blockSlots parameter) =>
        actualReferenceLaw cutoffScale parameter (beta parameter))).l2Sq
        (densityTail (actualReferenceLaw cutoffScale parameter (beta parameter))
          (symmetrizedMass (actualRootQueueMass cutoffScale parameter (beta parameter))) cutoff) ≤
        (Real.exp 1 / (parameter : ℝ) ^ 4) ^ (cutoff + 1) * (16 * Real.exp 1) :=
  actual_root_queue_complete_tail_eventually cutoffScale hscale beta hbeta
    (actual_joint_mean_zero_eventually cutoffScale hscale beta hbeta)

end
end AFT.V7Calibration
