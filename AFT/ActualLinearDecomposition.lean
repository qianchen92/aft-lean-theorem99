import AFT.ActualRootVectors

/-! # The actual normalized block mean as root vectors plus fixed endpoints -/

namespace AFT.V7Calibration

open ProfileHilbert BlockProducts GaussianSource
open scoped BigOperators Classical

noncomputable section

local instance actualLinearDecompositionFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance actualLinearDecompositionSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _

/-- The endpoint part is independent of every realized root and queue. -/
def actualEndpointVector (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (index : blockIndex parameter) : EuclideanSpace ℝ (Fin (Parameters.modulus parameter)) :=
  match index with
  | .inl _ => whiten (actualReferenceLaw cutoffScale parameter beta).weight (fun color =>
      (∑ second, ((actualActivatedSource cutoffScale parameter).mix
        (actualPairBranch cutoffScale parameter beta)).weight (color, second)) +
      (∑ first, ((actualActivatedSource cutoffScale parameter).mix
        (actualPairBranch cutoffScale parameter beta)).weight (first, color)) -
      2 * (actualReferenceLaw cutoffScale parameter beta).weight color)
  | .inr _ => 0

set_option backward.isDefEq.respectTransparency false in
/-- The first homogeneous coefficient is the literal root-dependent body
vector plus the constant endpoint vector. -/
theorem actual_first_coefficient_decomposition (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (href : ∀ color, 0 < (actualReferenceLaw cutoffScale parameter beta).weight color)
    (root queue : blockIndex parameter → ℤ) (index : blockIndex parameter)
    (color : Fin (Parameters.modulus parameter)) :
    localCoefficient (blockSlots parameter) (actualReferenceLaw cutoffScale parameter beta)
      (actualBlockFamily cutoffScale parameter beta root queue) index 1 (fun _ => color) =
      (actualBlockBodyVector cutoffScale parameter beta index (root index) (queue index)).ofLp color +
        (actualEndpointVector cutoffScale parameter beta index).ofLp color := by
  unfold localCoefficient
  rw [LocalTensors.degreeTensor_one_whitened _ href]
  cases index with
  | inl leg =>
    change ((∑ slot : Fin 3,
      (((actualFixedRootTripleLaw cutoffScale parameter beta (root (.inl leg)) (queue (.inl leg))).map
        (fun word => word slot)).weight color - (actualReferenceLaw cutoffScale parameter beta).weight color))) /
          Real.sqrt ((actualReferenceLaw cutoffScale parameter beta).weight color) = _
    rw [Fin.sum_univ_three]
    have hf := PhysicalBlockTensors.sharedSourceTriple_first_marginal
      (actualActivatedSource cutoffScale parameter) (actualPairBranch cutoffScale parameter beta)
      (actualBodyBranch cutoffScale parameter beta (root (.inl leg)) (queue (.inl leg))) color
    have hs := PhysicalBlockTensors.sharedSourceTriple_second_marginal
      (actualActivatedSource cutoffScale parameter) (actualPairBranch cutoffScale parameter beta)
      (actualBodyBranch cutoffScale parameter beta (root (.inl leg)) (queue (.inl leg))) color
    change ((actualFixedRootTripleLaw cutoffScale parameter beta (root (.inl leg)) (queue (.inl leg))).map
      (fun word => word 0)).weight color = _ at hf
    change ((actualFixedRootTripleLaw cutoffScale parameter beta (root (.inl leg)) (queue (.inl leg))).map
      (fun word => word 1)).weight color = _ at hs
    rw [hf, hs, actualBlockBodyLaw_attached cutoffScale parameter beta leg]
    simp only [actualBlockBodyVector, actualEndpointVector, whiten_apply]
    ring
  | inr body =>
    change ((∑ slot : Fin 1,
      (((singletonBlockLaw (actualShiftedBodyLaw cutoffScale parameter beta
        (root (.inr body) + queue (.inr body)))).map (fun word => word slot)).weight color -
        (actualReferenceLaw cutoffScale parameter beta).weight color))) /
          Real.sqrt ((actualReferenceLaw cutoffScale parameter beta).weight color) = _
    rw [Fin.sum_univ_one, singletonBlockLaw_marginal]
    simp only [actualBlockBodyVector, actualBlockBodyLaw, actualEndpointVector, whiten_apply, PiLp.zero_apply, add_zero]

/-- The full squared normalized mean is exactly a Euclidean norm, ready for
the proven root-conditioning concentration theorem. -/
theorem actual_normalized_mean_square (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (href : ∀ color, 0 < (actualReferenceLaw cutoffScale parameter beta).weight color)
    (root queue : blockIndex parameter → ℤ) (scale : ℝ) :
    (∑ color, (∑ index, normalizedLinear (blockSlots parameter)
      (actualReferenceLaw cutoffScale parameter beta)
      (actualBlockFamily cutoffScale parameter beta root queue) scale index color) ^ 2) =
      ‖scale • (∑ index,
        (actualBlockBodyVector cutoffScale parameter beta index (root index) (queue index) +
          actualEndpointVector cutoffScale parameter beta index))‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro color _
  simp only [Real.norm_eq_abs, sq_abs]
  congr 1
  simp only [normalizedLinear, actual_first_coefficient_decomposition cutoffScale parameter beta href]
  change _ = scale * ((∑ index,
    (actualBlockBodyVector cutoffScale parameter beta index (root index) (queue index) +
      actualEndpointVector cutoffScale parameter beta index)).ofLp color)
  simp only [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_add, Pi.add_apply, Finset.mul_sum]

end

end AFT.V7Calibration
