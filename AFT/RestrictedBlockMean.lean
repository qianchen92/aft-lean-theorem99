import AFT.RestrictedBlocks
import AFT.ActualNormalizedMean

/-! # Exact removed-block means and their dimension-free bounds -/

namespace AFT.BlockProducts

open scoped BigOperators Classical
noncomputable section

variable {Index Color : Type*} [Fintype Index] [Fintype Color]
variable (Slots : Index → Type*) [∀ index, Fintype (Slots index)]

/-- The literal degree-one block tensor in Euclidean color coordinates. -/
def linearVector (reference : FiniteDist Color)
    (law : (index : Index) → FiniteDist (Slots index → Color)) (scale : ℝ) (index : Index) :
    EuclideanSpace ℝ Color := WithLp.toLp 2 (normalizedLinear Slots reference law scale index)

omit [Fintype Index] in
@[simp] theorem linearVector_apply (reference : FiniteDist Color)
    (law : (index : Index) → FiniteDist (Slots index → Color)) (scale : ℝ) (index : Index) (color : Color) :
    (linearVector Slots reference law scale index).ofLp color = normalizedLinear Slots reference law scale index color := rfl

omit [Fintype Index] in
theorem linearVector_norm_sq (reference : FiniteDist Color)
    (law : (index : Index) → FiniteDist (Slots index → Color)) (scale : ℝ) (index : Index) :
    ‖linearVector Slots reference law scale index‖ ^ 2 =
      ∑ color, normalizedLinear Slots reference law scale index color ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, linearVector_apply, Real.norm_eq_abs, sq_abs]

/-- No palette dimension enters when finitely many tagged blocks are
removed from the controlled first-degree energy. -/
theorem removed_linear_mean_le (reference : FiniteDist Color)
    (law : (index : Index) → FiniteDist (Slots index → Color)) (scale : ℝ)
    (henergy : (∑ index, ∑ color, normalizedLinear Slots reference law scale index color ^ 2) ≤ 1 / 8)
    (selected : Finset Index) :
    ‖∑ index ∈ selected, linearVector Slots reference law scale index‖ ≤ selected.card := by
  have hpoint (index : Index) : ‖linearVector Slots reference law scale index‖ ≤ 1 := by
    have hh : ‖linearVector Slots reference law scale index‖ ^ 2 ≤ 1 / 8 := by
      rw [linearVector_norm_sq]
      exact (Finset.single_le_sum (fun other _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ index)).trans henergy
    nlinarith [norm_nonneg (linearVector Slots reference law scale index)]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _index ∈ selected, (1 : ℝ) := Finset.sum_le_sum fun index _ => hpoint index
    _ = _ := by simp

/-- Deleting a marked set subtracts exactly its first-degree tensor. -/
theorem remaining_linear_mean (reference : FiniteDist Color)
    (law : (index : Index) → FiniteDist (Slots index → Color)) (scale : ℝ) (selected : Finset Index) :
    (∑ index : {i : Index // i ∉ selected},
      linearVector (fun index : {i : Index // i ∉ selected} => Slots index) reference (fun index => law index) scale index) =
      (∑ index, linearVector Slots reference law scale index) -
        ∑ index ∈ selected, linearVector Slots reference law scale index := by
  change (∑ index : {i : Index // i ∉ selected}, linearVector Slots reference law scale index) = _
  rw [← Finset.sum_subtype selectedᶜ (fun index => by simp) (fun index => linearVector Slots reference law scale index)]
  exact eq_sub_iff_add_eq.mpr (Finset.sum_compl_add_sum selected (fun index => linearVector Slots reference law scale index))


end
end AFT.BlockProducts

namespace AFT.V7Calibration

open Filter GaussianSource BlockProducts
open scoped BigOperators Classical Topology
noncomputable section
local instance restrictedBlockMeanFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance restrictedBlockMeanSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _

def actualRemovedMean (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (word : actualRootWord parameter) (queue : blockIndex parameter → ℤ) (selected : Finset (blockIndex parameter)) :
    EuclideanSpace ℝ (Fin (Parameters.modulus parameter)) :=
  ∑ index ∈ selected, linearVector (blockSlots parameter) (actualReferenceLaw cutoffScale parameter beta)
    (actualBlockFamily cutoffScale parameter beta (actualRootField parameter word) queue) (actualFockScale parameter) index

/-- The physical root/queue mean and the coefficient mean agree literally,
including the endpoint contribution. -/
theorem actual_linear_mean_eq (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (href : ∀ color, 0 < (actualReferenceLaw cutoffScale parameter beta).weight color)
    (word : actualRootWord parameter) (queue : blockIndex parameter → ℤ) :
    (∑ index, linearVector (blockSlots parameter) (actualReferenceLaw cutoffScale parameter beta)
      (actualBlockFamily cutoffScale parameter beta (actualRootField parameter word) queue) (actualFockScale parameter) index) =
      actualNormalizedBlockMean cutoffScale parameter beta word queue := by
  ext color
  simp only [WithLp.ofLp_sum, Finset.sum_apply, linearVector_apply, normalizedLinear,
    actual_first_coefficient_decomposition cutoffScale parameter beta href]
  change _ = actualFockScale parameter * ((∑ index,
    (actualBlockBodyVector cutoffScale parameter beta index (actualRootField parameter word index) (queue index) +
      actualEndpointVector cutoffScale parameter beta index)).ofLp color)
  simp only [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_add, Pi.add_apply, Finset.mul_sum]

/-- This holds uniformly for every selected set, without assuming any marked
input factorizes across its blocks. -/
theorem actual_removed_mean_bound_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ word : actualRootWord parameter, ∀ queue : blockIndex parameter → ℤ,
      (∀ index, |queue index| ≤ (queueCutoff parameter : ℤ)) → ∀ selected : Finset (blockIndex parameter),
      ‖actualRemovedMean cutoffScale parameter (beta parameter) word queue selected‖ ≤ selected.card := by
  filter_upwards [actual_cubic_conditions_eventually cutoffScale hscale beta hbeta]
    with parameter hc word queue hq selected
  apply removed_linear_mean_le
  have hh := (hc (actualRootField parameter word) queue (actualRootField_bound parameter word) hq).2.1
  simpa only [normalizedLinear, actualFockScale, mul_assoc] using hh

end
end AFT.V7Calibration
