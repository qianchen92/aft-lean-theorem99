import AFT.PrimaryInverseMatrix
import AFT.CoordinateSliceOutput

/-! # Literal inverse columns on the new coordinates of a joint kernel -/
namespace AFT.MixedKernel
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Rest Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]

theorem coordinateInverseKernel_all_matrix (reference : Slot → FiniteDist Color) (rho : ℝ)
    (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ)) (kernel : (Slot → Color) → ℝ) (output : Slot → Color) :
    coordinateInverseKernel allCoordinates reference rho operator kernel output=
      ∑ input,kernel input*∏ slot,
        (rho⁻¹*(reference slot).weight (input slot)*operator.symm (Pi.single (input slot) 1) (output slot)/
          (reference slot).weight (output slot)) := by
  change rho⁻¹^(allCoordinates (Slot := Slot)).length*inputIteration _ _ _ kernel output=_
  rw [allCoordinates_length,inputIteration_matrix allCoordinates (Finset.nodup_toList _)
    (fun slot => Finset.mem_toList.mpr (Finset.mem_univ slot)),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro input _
  simp only [LinearMap.toMatrix'_apply,LinearEquiv.coe_coe]
  rw [show rho⁻¹^Fintype.card Slot=∏ _slot : Slot,rho⁻¹ by simp]
  rw [mul_comm _ (kernel input*_),mul_assoc]
  congr 1
  rw [←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro slot _
  ring

variable [Fintype Rest] [DecidableEq Rest]

omit [Fintype Rest] in
/-- Remaining input coordinates stay as a fixed fiber, including body
coordinates at zero-probability atoms. -/
theorem coordinateInverseKernel_new_matrix (primary : FiniteDist Color) (other : Rest → FiniteDist Color)
    (rho : ℝ) (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ))
    (kernel : (Slot ⊕ Rest → Color) → ℝ) (output : Slot → Color) (rest : Rest → Color) :
    coordinateInverseKernel ((allCoordinates (Slot := Slot)).map Sum.inl)
      (Sum.elim (fun _ : Slot => primary) other) rho operator kernel (Sum.elim output rest)=
      ∑ input,kernel (Sum.elim input rest)*∏ slot,
        (rho⁻¹*primary.weight (input slot)*operator.symm (Pi.single (input slot) 1) (output slot)/
          primary.weight (output slot)) := by
  rw [congrFun (coordinateInverseKernel_inl_slice allCoordinates (fun _ : Slot => primary) other rho operator kernel rest) output,
    coordinateInverseKernel_all_matrix]

end
end AFT.MixedKernel
