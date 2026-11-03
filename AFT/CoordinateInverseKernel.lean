import AFT.CanonicalJointInverse

/-! # Calibrating a specified list of new coordinates of a joint kernel -/
namespace AFT.MixedKernel
open scoped BigOperators Classical
noncomputable section
variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]

def coordinateInverseKernel (coordinates : List Slot) (reference : Slot → FiniteDist Color)
    (rho : ℝ) (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ)) :
    Module.End ℝ ((Slot → Color) → ℝ) :=
  (rho⁻¹)^coordinates.length • inputIteration coordinates (fun _ => operator.symm.toLinearMap) reference

omit [Fintype Slot] in
theorem coordinateInverseKernel_exact (coordinates : List Slot) (reference : Slot → FiniteDist Color)
    (rho : ℝ) (hrho : rho ≠ 0) (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ))
    (hpositive : ∀ slot ∈ coordinates, ∀ color,(reference slot).weight color ≠ 0)
    (kernel : (Slot → Color) → ℝ) :
    rho^coordinates.length • inputIteration coordinates.reverse (fun _ => operator.toLinearMap) reference
      (coordinateInverseKernel coordinates reference rho operator kernel)=kernel := by
  change rho^coordinates.length • inputIteration _ _ _
    ((rho⁻¹)^coordinates.length • inputIteration _ _ _ kernel)=kernel
  rw [map_smul,inputIteration_inverse coordinates operator reference hpositive,
    smul_smul,← mul_pow,mul_inv_cancel₀ hrho,one_pow,one_smul]

theorem coordinateInverseKernel_activity_le (coordinates : List Slot) (reference : Slot → FiniteDist Color)
    (rates : Slot → ℝ) (rho : ℝ) (hrho : 0 < rho) (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ))
    (hoperator : ∀ slot ∈ coordinates, ∀ kernel : (Slot → Color) → ℝ,
      activity rates reference (partialInputOperator slot operator.symm.toLinearMap (reference slot).weight kernel) ≤
        4*activity rates reference kernel) (kernel : (Slot → Color) → ℝ) :
    activity rates reference (coordinateInverseKernel coordinates reference rho operator kernel) ≤
      (4/rho)^coordinates.length*activity rates reference kernel := by
  have hh := inputIteration_activity_le coordinates (fun _ => operator.symm.toLinearMap)
    reference rates 4 (by norm_num) hoperator kernel
  change activity rates reference ((rho⁻¹)^coordinates.length • inputIteration _ _ _ kernel) ≤ _
  rw [activity_smul,abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hrho.le) _)]
  apply (mul_le_mul_of_nonneg_left hh (pow_nonneg (inv_nonneg.mpr hrho.le) _)).trans_eq
  rw [← mul_assoc,← mul_pow]
  congr 2
  rw [div_eq_mul_inv,mul_comm]

theorem coordinateInverseKernel_canonical (coordinates : List Slot) (reference : Slot → FiniteDist Color)
    (rho : ℝ) (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ))
    (hpositive : ∀ slot ∈ coordinates, ∀ color,(reference slot).weight color ≠ 0)
    (hmass : ∀ profile,(∑ color,operator.symm profile color)=∑ color,profile color)
    (kernel : (Slot → Color) → ℝ) (hcanonical : Hoeffding.Canonical reference Finset.univ kernel) :
    Hoeffding.Canonical reference Finset.univ (coordinateInverseKernel coordinates reference rho operator kernel) := by
  apply canonical_smul
  exact inputIteration_canonical _ _ _ hpositive (fun _ _ => hmass) kernel hcanonical

end
end AFT.MixedKernel
