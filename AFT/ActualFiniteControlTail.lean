import AFT.ActualPlacedInputTail
import AFT.ActualActivityHistogramTail

/-! # Complete tails of actual finite signed control representations -/
namespace AFT.V7Calibration
open Filter GaussianSource BlockProducts HistogramNormalization
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance actualFiniteControlTailSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
local instance actualFiniteControlTailSigmaDecEq {ι : Type*} {fiber : ι → Type*} : DecidableEq (Sigma fiber) := Classical.decEq _

/-- A literal finite canonical joint input and its physical placement. -/
structure ActualCanonicalControl (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) where
  count : ℕ
  role : Fin count → Bool
  selected : Finset (blockIndex parameter)
  placement : ActualTaggedPlacement parameter count role selected
  kernel : (Fin count → Fin (Parameters.modulus parameter)) → ℝ
  canonical : Hoeffding.Canonical
    (fun index => actualRoleInput cutoffScale parameter beta (role index)) Finset.univ kernel

/-- The exact proven coefficient in the complete actual tail estimate. -/
def ActualCanonicalControl.tailWeight {cutoffScale beta : ℝ} {parameter : ℕ}
    (control : ActualCanonicalControl cutoffScale parameter beta) : ℝ :=
  Real.sqrt (actualJointInputEnergy cutoffScale parameter beta control.count control.role control.kernel *
    (16 * Real.exp (1 + 16 * (1 + (control.selected.card : ℝ)) ^ 2)))

theorem ActualCanonicalControl.tailWeight_nonneg {cutoffScale beta : ℝ} {parameter : ℕ}
    (control : ActualCanonicalControl cutoffScale parameter beta) : 0 ≤ control.tailWeight := Real.sqrt_nonneg _

theorem ActualCanonicalControl.tailWeight_sq {cutoffScale beta : ℝ} {parameter : ℕ}
    (control : ActualCanonicalControl cutoffScale parameter beta) :
    control.tailWeight ^ 2 =
      actualJointInputEnergy cutoffScale parameter beta control.count control.role control.kernel *
        (16 * Real.exp (1 + 16 * (1 + (control.selected.card : ℝ)) ^ 2)) :=
  Real.sq_sqrt (mul_nonneg (actualJointInputEnergy_nonneg _ _ _ _ _ _) (by positivity))

/-- The actual output of one represented canonical control. -/
def ActualCanonicalControl.outputMass {cutoffScale beta : ℝ} {parameter : ℕ}
    (control : ActualCanonicalControl cutoffScale parameter beta)
    (charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark) :
    (Sigma (blockSlots parameter) → Fin (Parameters.modulus parameter)) → ℝ :=
  actualPlacedInputMass cutoffScale parameter beta charts control.count control.role control.selected control.placement control.kernel

/-- The actual full signed control representation is summed after all
components have been placed on the same physical output coordinates. -/
def actualFiniteControlMass {Index : Type*} [Fintype Index]
    {cutoffScale beta : ℝ} {parameter : ℕ}
    (charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark)
    (coefficient : Index → ℝ) (control : Index → ActualCanonicalControl cutoffScale parameter beta) :
    (Sigma (blockSlots parameter) → Fin (Parameters.modulus parameter)) → ℝ :=
  fun word => ∑ index, coefficient index * (control index).outputMass charts word

/-- The complete actual tail of every finite signed representation is
controlled by its weighted L1 coefficient sum. All physical estimates,
root conditioning, and shared-queue normalization have been discharged. -/
theorem actual_finite_control_tail_eventually {Index : Type*} [Fintype Index]
    (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
      ∃ charts : (mark : Fin (Parameters.modulus parameter)) → PublicChartFamily cutoffScale parameter mark,
      (∀ mark attached first second, publicChartRaw cutoffScale parameter mark (charts mark) attached first second =
        conditionalJointOutput cutoffScale parameter mark attached first second) ∧
      ∀ coefficient : Index → ℝ,
      ∀ control : Index → ActualCanonicalControl cutoffScale parameter (beta parameter), ∀ cutoff : ℕ,
      (FiniteDist.independent (fun _ : Sigma (blockSlots parameter) => actualReferenceLaw cutoffScale parameter (beta parameter))).l2Sq
        (densityTail (actualReferenceLaw cutoffScale parameter (beta parameter))
          (symmetrizedMass (actualFiniteControlMass charts coefficient control)) cutoff) ≤
        (Real.exp 1 / (parameter : ℝ) ^ 4) ^ (cutoff + 1) *
          (∑ index, |coefficient index| * (control index).tailWeight) ^ 2 := by
  filter_upwards [actual_placed_input_tail_eventually cutoffScale hscale beta hbeta] with parameter ht
  obtain ⟨charts, hcharts, htail⟩ := ht
  refine ⟨charts, hcharts, ?_⟩
  intro coefficient control cutoff
  let rate : ℝ := (Real.exp 1 / (parameter : ℝ) ^ 4) ^ (cutoff + 1)
  have hr : 0 ≤ rate := by dsimp [rate]; positivity
  have hcomponent (index : Index) :
      (FiniteDist.independent (fun _ : Sigma (blockSlots parameter) => actualReferenceLaw cutoffScale parameter (beta parameter))).l2Sq
        (densityTail (actualReferenceLaw cutoffScale parameter (beta parameter))
          (symmetrizedMass ((control index).outputMass charts)) cutoff) ≤
        (Real.sqrt rate * (control index).tailWeight) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hr, ActualCanonicalControl.tailWeight_sq]
    exact htail (control index).count (control index).role (control index).selected
      (control index).placement (control index).kernel (control index).canonical cutoff
  have h := signed_sum_complete_tail_le (actualReferenceLaw cutoffScale parameter (beta parameter)) cutoff
    coefficient (fun index => Real.sqrt rate * (control index).tailWeight)
    (fun index => (control index).outputMass charts)
    (fun index => mul_nonneg (Real.sqrt_nonneg _) (control index).tailWeight_nonneg) hcomponent
  have hsum : (∑ index, |coefficient index| * (Real.sqrt rate * (control index).tailWeight)) =
      Real.sqrt rate * ∑ index, |coefficient index| * (control index).tailWeight := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro index _
    ring
  rw [hsum, mul_pow, Real.sq_sqrt hr] at h
  exact h

end
end AFT.V7Calibration
