import AFT.TaggedBlockTail

/-! # Norms of normalized physical block coefficients -/

namespace AFT.BlockProducts

open scoped BigOperators Classical

noncomputable section

local instance (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

variable {Index Color : Type*} [Fintype Index] [Fintype Color]
variable (Slots : Index → Type*) [∀ index, Fintype (Slots index)]

/-- Exact first-degree norm in the single-color coordinate representation. -/
theorem linear_tensor_energy (tensor : BlockFock.Tensor (Fin 1) Color) :
    (∑ color, tensor (fun _ => color) ^ 2) = BlockFock.tensorEnergy tensor := by
  unfold BlockFock.tensorEnergy
  have hh := (Equiv.funUnique (Fin 1) Color).symm.sum_comp (fun word => tensor word ^ 2)
  exact hh

omit [Fintype Index] in
theorem normalized_linear_energy (reference : FiniteDist Color)
    (law : (index : Index) → FiniteDist (Slots index → Color)) (scale : ℝ) (index : Index) :
    (∑ color, normalizedLinear Slots reference law scale index color ^ 2) =
      scale ^ 2 * BlockFock.tensorEnergy (localCoefficient Slots reference law index 1) := by
  simp only [normalizedLinear, mul_pow, ← Finset.mul_sum]
  rw [linear_tensor_energy]

omit [Fintype Index] in
theorem normalized_quadratic_norm_le (reference : FiniteDist Color)
    (law : (index : Index) → FiniteDist (Slots index → Color)) (scale bound : ℝ) (index : Index)
    (hb : 0 ≤ bound) (henergy : BlockFock.tensorEnergy (localCoefficient Slots reference law index 2) ≤ bound ^ 2) :
    SelectionBound.localPairNorm (normalizedQuadratic Slots reference law scale) index ≤ scale ^ 2 * bound := by
  unfold SelectionBound.localPairNorm normalizedQuadratic
  rw [TensorFock.tensorEnergy_smul]
  apply (Real.sqrt_le_left (by positivity)).mpr
  nlinarith [mul_le_mul_of_nonneg_left henergy (sq_nonneg (scale ^ 2))]

omit [Fintype Index] in
theorem normalized_cubic_norm_le (reference : FiniteDist Color)
    (law : (index : Index) → FiniteDist (Slots index → Color)) (scale bound : ℝ) (index : Index)
    (hs : 0 ≤ scale) (hb : 0 ≤ bound)
    (henergy : BlockFock.tensorEnergy (localCoefficient Slots reference law index 3) ≤ bound ^ 2) :
    SelectionBound.localTripleNorm (normalizedCubic Slots reference law scale) index ≤ scale ^ 3 * bound := by
  unfold SelectionBound.localTripleNorm normalizedCubic
  rw [TensorFock.tensorEnergy_smul]
  apply (Real.sqrt_le_left (by positivity)).mpr
  nlinarith [mul_le_mul_of_nonneg_left henergy (sq_nonneg (scale ^ 3))]

theorem CubicBlockConditions_of_scaled (reference : FiniteDist Color)
    (law : (index : Index) → FiniteDist (Slots index → Color)) (population capacity : ℕ) (radius : ℝ)
    (hcapacity : Fintype.card Index ≤ capacity)
    (hlinear : (∑ index, ∑ color,
      normalizedLinear Slots reference law (Real.sqrt 2 * (radius / Real.sqrt population)) index color ^ 2) ≤ 1 / 8)
    (hnonlinear : (∑ index, (128 * SelectionBound.localPairNorm
        (normalizedQuadratic Slots reference law (Real.sqrt 2 * (radius / Real.sqrt population))) index +
      128 * Real.sqrt capacity * SelectionBound.localTripleNorm
        (normalizedCubic Slots reference law (Real.sqrt 2 * (radius / Real.sqrt population))) index)) ≤ 1 / 2) :
    CubicBlockConditions Slots reference law population capacity radius := by
  refine ⟨(Finset.card_le_univ _).trans hcapacity, ?_, ?_⟩
  · simpa only [normalizedLinear, mul_assoc] using hlinear
  · have hq : (fun index word => (Real.sqrt 2) ^ 2 * normalizedQuadratic Slots reference law
        (radius / Real.sqrt population) index word) =
        normalizedQuadratic Slots reference law (Real.sqrt 2 * (radius / Real.sqrt population)) := by
      funext index word
      simp only [normalizedQuadratic, mul_pow, mul_assoc]
    have hc : (fun index word => (Real.sqrt 2) ^ 3 * normalizedCubic Slots reference law
        (radius / Real.sqrt population) index word) =
        normalizedCubic Slots reference law (Real.sqrt 2 * (radius / Real.sqrt population)) := by
      funext index word
      simp only [normalizedCubic, mul_pow, mul_assoc]
    rw [hq, hc]
    exact hnonlinear

end

end AFT.BlockProducts
