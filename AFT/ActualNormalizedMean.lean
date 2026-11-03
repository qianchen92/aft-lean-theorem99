import AFT.ActualLinearDecomposition
import AFT.ActualQueueBudget
import AFT.FiniteMeanAlgebra
import AFT.FiniteRetype

/-! # Exact centering of the physical normalized block mean -/

namespace AFT.V7Calibration

open Filter GaussianSource FiniteConcentration
open scoped BigOperators Classical Topology

noncomputable section

local instance actualNormalizedMeanFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance actualNormalizedMeanSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _

def actualRootWord (parameter : ℕ) := Fin (Parameters.bodies parameter) → Window (v7RootCutoff parameter)

instance actualRootWordFintype (parameter : ℕ) : Fintype (actualRootWord parameter) := inferInstanceAs (Fintype (_ → _))

def actualRootField (parameter : ℕ) (word : actualRootWord parameter) : blockIndex parameter → ℤ :=
  fun index => word (actualRootIndex parameter index)

/-- The actual doubled-radius first coefficient, in finite Euclidean
coordinates, including both endpoint marginals at every leg. -/
def actualNormalizedBlockMean (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (word : actualRootWord parameter) (queue : blockIndex parameter → ℤ) :
    EuclideanSpace ℝ (Fin (Parameters.modulus parameter)) :=
  actualFockScale parameter • (∑ index,
    (actualBlockBodyVector cutoffScale parameter beta index (actualRootField parameter word index) (queue index) +
      actualEndpointVector cutoffScale parameter beta index))

theorem actualRootField_bound (parameter : ℕ) (word : actualRootWord parameter) (index : blockIndex parameter) :
    |actualRootField parameter word index| ≤ (v7RootCutoff parameter : ℤ) :=
  abs_le.mpr (Finset.mem_Icc.mp (word (actualRootIndex parameter index)).property)

/-- Literal conversion of the block normalization into the independent-root
sum; the endpoint contribution is a fixed deterministic vector. -/
theorem actualNormalizedBlockMean_split (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (word : actualRootWord parameter) (queue : blockIndex parameter → ℤ) :
    actualNormalizedBlockMean cutoffScale parameter beta word queue =
      (∑ index, actualRootValue cutoffScale parameter beta queue index (word index)) +
        actualFockScale parameter • (∑ index, actualEndpointVector cutoffScale parameter beta index) := by
  have heq := (actualRootIndex parameter).sum_comp (fun index : Fin (Parameters.bodies parameter) =>
    actualRootValue cutoffScale parameter beta queue index (word index))
  simp only [actualRootValue, Equiv.symm_apply_apply, ← Finset.smul_sum] at heq
  simp only [actualRootValue, ← Finset.smul_sum]
  rw [← heq]
  simp only [actualNormalizedBlockMean, actualRootField, Finset.sum_add_distrib, smul_add]

/-- The required conditional-mean identity is algebraic for the actual
physical block mean and the actual independent-source centered summands. -/
theorem actual_mean_centering_identity (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (law : FiniteDist (actualRootWord parameter)) (word : actualRootWord parameter)
    (queue : blockIndex parameter → ℤ) :
    ((∑ index, actualCenteredRootValue cutoffScale parameter beta queue index (word index)) -
      vectorMean law (fun input => ∑ index,
        actualCenteredRootValue cutoffScale parameter beta queue index (input index))) +
      vectorMean law (fun input => actualNormalizedBlockMean cutoffScale parameter beta input queue) =
        actualNormalizedBlockMean cutoffScale parameter beta word queue := by
  simp only [actualCenteredRootValue, Finset.sum_sub_distrib,
    vectorMean_sub, vectorMean_const, actualNormalizedBlockMean_split,
    vectorMean_add, vectorMean_const]
  abel

/-- The exact queue perturbation cancels every root-independent endpoint. -/
theorem actual_queue_displacement_identity (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (word : actualRootWord parameter)
    (sample : Window (queueCutoff parameter) × Equiv.Perm (blockIndex parameter)) :
    actualNormalizedBlockMean cutoffScale parameter beta word (actualQueueShifts parameter sample) -
      actualNormalizedBlockMean cutoffScale parameter beta word (fun _ => 0) =
      actualQueueDisplacement cutoffScale parameter beta (actualRootField parameter word) sample := by
  unfold actualNormalizedBlockMean actualQueueDisplacement
  rw [← smul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro index _
  abel

/-- Once the literal root/queue mixture mean has been identified, every
fixed shared queue incurs only its proven `lambda^-7` displacement. -/
theorem actual_conditional_mean_bound_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ law : FiniteDist (actualRootWord parameter),
      vectorMean (FiniteDist.retype (actualQueuePlacementLaw parameter))
        (fun sample => vectorMean law (fun word =>
          actualNormalizedBlockMean cutoffScale parameter (beta parameter) word (actualQueueShifts parameter sample))) = 0 →
      ∀ sample, ‖vectorMean law (fun word => actualNormalizedBlockMean cutoffScale parameter (beta parameter)
        word (actualQueueShifts parameter sample))‖ ≤ 1184 / (parameter : ℝ) ^ 7 := by
  filter_upwards [actual_queue_displacement_bound_eventually cutoffScale hscale beta hbeta]
    with parameter hb law hmean sample
  have hh := mean_le_twice_displacement law (FiniteDist.retype (actualQueuePlacementLaw parameter))
    (fun word sample => actualNormalizedBlockMean cutoffScale parameter (beta parameter) word (actualQueueShifts parameter sample))
    (fun word => actualNormalizedBlockMean cutoffScale parameter (beta parameter) word (fun _ => 0))
    (592 / (parameter : ℝ) ^ 7) hmean (by
      intro word other
      rw [actual_queue_displacement_identity]
      exact hb (actualRootField parameter word) (actualRootField_bound parameter word) other) sample
  exact hh.trans_eq (by ring)

end

end AFT.V7Calibration
