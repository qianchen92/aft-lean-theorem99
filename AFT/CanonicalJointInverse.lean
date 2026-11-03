import AFT.PrimarySeedCanonical
import AFT.CanonicalFiberEnergy

/-! # Literal all-coordinate inverses of actual canonical joint coefficients -/

namespace AFT.MixedKernel
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]

/-- Enumerate all retained coordinates once, retaining their literal order. -/
def allCoordinates : List Slot := Finset.univ.toList

omit [DecidableEq Slot] in
@[simp] theorem allCoordinates_length : (allCoordinates (Slot := Slot)).length = Fintype.card Slot := by
  simp [allCoordinates]

/-- The full joint density is acted on directly by the calibrated inverse. -/
def inverseJointKernel (reference : Slot → FiniteDist Color) (rho : ℝ)
    (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ)) : Module.End ℝ ((Slot → Color) → ℝ) :=
  (rho⁻¹)^Fintype.card Slot • inputIteration allCoordinates (fun _ => operator.symm.toLinearMap) reference

/-- The forward image is exactly the original joint density. -/
theorem inverseJointKernel_exact (reference : Slot → FiniteDist Color) (rho : ℝ) (hrho : rho ≠ 0)
    (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ))
    (hpositive : ∀ slot color, (reference slot).weight color ≠ 0)
    (kernel : (Slot → Color) → ℝ) :
    rho^Fintype.card Slot • inputIteration (allCoordinates (Slot := Slot)).reverse
      (fun _ => operator.toLinearMap) reference (inverseJointKernel reference rho operator kernel) = kernel := by
  change rho^Fintype.card Slot • inputIteration _ _ _
    ((rho⁻¹)^Fintype.card Slot • inputIteration _ _ _ kernel) = _
  rw [map_smul,inputIteration_inverse _ operator reference (fun slot _ => hpositive slot),
    smul_smul,← mul_pow,mul_inv_cancel₀ hrho,one_pow,one_smul]

/-- The full activity controls every mixed fiber of the literal inverse. -/
theorem inverseJointKernel_activity_le (reference : Slot → FiniteDist Color) (rates : Slot → ℝ)
    (rho : ℝ) (hrho : 0 < rho) (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ))
    (hoperator : ∀ slot kernel, activity rates reference
      (partialInputOperator slot operator.symm.toLinearMap (reference slot).weight kernel) ≤
        4 * activity rates reference kernel)
    (kernel : (Slot → Color) → ℝ) :
    activity rates reference (inverseJointKernel reference rho operator kernel) ≤
      (4/rho)^Fintype.card Slot * activity rates reference kernel := by
  have hh := inputIteration_activity_le allCoordinates (fun _ => operator.symm.toLinearMap)
    reference rates 4 (by norm_num) (fun slot _ => hoperator slot) kernel
  rw [allCoordinates_length] at hh
  change activity rates reference ((rho⁻¹)^Fintype.card Slot • inputIteration _ _ _ kernel) ≤ _
  rw [activity_smul,abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hrho.le) _)]
  apply (mul_le_mul_of_nonneg_left hh (pow_nonneg (inv_nonneg.mpr hrho.le) _)).trans_eq
  rw [← mul_assoc,← mul_pow]
  congr 2
  rw [div_eq_mul_inv,mul_comm]

theorem inverseJointKernel_canonical (reference : Slot → FiniteDist Color) (rho : ℝ)
    (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ))
    (hpositive : ∀ slot color, (reference slot).weight color ≠ 0)
    (hmass : ∀ profile, (∑ color, operator.symm profile color) = ∑ color, profile color)
    (kernel : (Slot → Color) → ℝ) (hcanonical : Hoeffding.Canonical reference Finset.univ kernel) :
    Hoeffding.Canonical reference Finset.univ (inverseJointKernel reference rho operator kernel) := by
  apply canonical_smul
  exact inputIteration_canonical _ _ _ (fun slot _ => hpositive slot) (fun _ _ => hmass) kernel hcanonical

end
end AFT.MixedKernel

namespace AFT.LocalTensors
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]
local instance canonicalJointSubtypeDecEq (selected : Finset Slot) : DecidableEq selected := Classical.decEq _

/-- Every restricted actual density coefficient is canonical in all of its
retained coordinates. -/
theorem restrictedComponent_canonical (reference : Slot → FiniteDist Color)
    (hpositive : ∀ slot color, 0 < (reference slot).weight color)
    (mass : (Slot → Color) → ℝ) (selected : Finset Slot) :
    Hoeffding.Canonical (fun slot : selected => reference slot) Finset.univ
      (restrictedComponent reference mass selected) := by
  constructor
  · intro first second h
    have heq : first = second := funext fun slot => h slot (Finset.mem_univ slot)
    rw [heq]
  · intro slot _ word
    simp only [restrictedComponent,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro input _
    have hprod (color : Color) :
        (∏ other : selected, Hoeffding.centeredAtom (reference other) (input other)
          (Function.update word slot color other)) =
        Hoeffding.centeredAtom (reference slot) (input slot) color *
          ∏ other ∈ (Finset.univ : Finset selected).erase slot,
            Hoeffding.centeredAtom (reference other) (input other) (word other) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ slot)]
      simp only [Function.update_self]
      congr 1
      apply Finset.prod_congr rfl
      intro other ho
      rw [Function.update_of_ne (Finset.mem_erase.mp ho).1]
    simp_rw [hprod]
    calc
      _ = (mass input * ∏ other ∈ (Finset.univ : Finset selected).erase slot,
          Hoeffding.centeredAtom (reference other) (input other) (word other)) *
          ∑ color, (reference slot).weight color * Hoeffding.centeredAtom (reference slot) (input slot) color := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro color _
        ring
      _ = 0 := by rw [Hoeffding.centeredAtom_mean _ (hpositive slot),mul_zero]

end
end AFT.LocalTensors
