import AFT.PrimarySeedInverse
import AFT.MixedCoordinateProducts
import AFT.TensorMixedSchur

/-! # The actual primary inverse as a full joint matrix contraction -/
namespace AFT.MixedKernel
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]

/-- Coordinates outside the specified list remain literal identity channels,
including atoms of zero reference mass. -/
theorem inputIteration_partial_matrix (coordinates : List Slot) (hnodup : coordinates.Nodup)
    (operator : Slot → Module.End ℝ (Color → ℝ)) (reference : Slot → FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) (output : Slot → Color) :
    inputIteration coordinates operator reference kernel output =
      ∑ point : Slot → Color,kernel point*∏ slot,
        if slot∈coordinates then
          (reference slot).weight (point slot)*LinearMap.toMatrix' (operator slot) (output slot) (point slot)/
            (reference slot).weight (output slot)
        else if output slot=point slot then 1 else 0 := by
  have hh := congrArg (fun table => inputIteration coordinates operator reference table output)
    (kernel_product_expansion kernel)
  simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul] at hh
  rw [hh]
  apply Finset.sum_congr rfl
  intro point _
  rw [inputIteration_product coordinates hnodup]
  simp only [productKernel]
  congr 1
  apply Finset.prod_congr rfl
  intro slot _
  by_cases hs : slot∈coordinates
  · simp only [if_pos hs]
    exact densityConjugate_indicator _ _ _ _
  · simp only [if_neg hs]

end
end AFT.MixedKernel

namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Color : Type*} [Fintype Color]

def primaryInverseMatrix (primary : FiniteDist Color) (rho : ℝ)
    (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ)) (primaryOrder bodyOrder : ℕ) :
    Fin (primaryOrder+bodyOrder) → Color → Color → ℝ :=
  Fin.addCases (fun _ input output => rho⁻¹*primary.weight input*
    operator.symm (Pi.single input 1) output/primary.weight output)
    (fun _ input output => if output=input then 1 else 0)

omit [Fintype Color] in
 theorem primaryInverseCoordinates_nodup (seed : InputSeed Color) : (primaryCoordinates seed).Nodup := by
  apply List.nodup_ofFn.mpr
  intro first second he
  exact Fin.ext (congrArg (fun slot : Fin (seed.primaryOrder+seed.bodyOrder) => slot.val) he)

omit [Fintype Color] in
 theorem primaryInverseCoordinates_left (seed : InputSeed Color) (slot : Fin seed.primaryOrder) :
    Fin.castAdd seed.bodyOrder slot ∈ primaryCoordinates seed := List.mem_ofFn.mpr ⟨slot,rfl⟩

omit [Fintype Color] in
 theorem primaryInverseCoordinates_right (seed : InputSeed Color) (slot : Fin seed.bodyOrder) :
    Fin.natAdd seed.primaryOrder slot ∉ primaryCoordinates seed := by
  intro hs
  obtain ⟨index,he⟩ := List.mem_ofFn.mp hs
  have h := congrArg Fin.val he
  simp only [Fin.val_castAdd,Fin.val_natAdd] at h
  omega

/-- Every entry of the genuine seed inverse is obtained by the specified
primary matrix and identity body channels, for arbitrary joint kernels. -/
theorem inversePrimarySeed_matrix (primary body : FiniteDist Color) (rho : ℝ)
    (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ)) (seed : InputSeed Color)
    (output : Fin (seed.primaryOrder+seed.bodyOrder) → Color) :
    (inversePrimarySeed primary body rho operator seed).kernel output=
      MixedKernel.matrixApply (primaryInverseMatrix primary rho operator seed.primaryOrder seed.bodyOrder)
        seed.kernel output := by
  change rho⁻¹^seed.primaryOrder*MixedKernel.inputIteration (primaryCoordinates seed)
    (fun _ => operator.symm.toLinearMap) (inputReference primary body seed) seed.kernel output=_
  rw [MixedKernel.inputIteration_partial_matrix _ (primaryInverseCoordinates_nodup seed)]
  unfold MixedKernel.matrixApply
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro point _
  rw [Fin.prod_univ_add,Fin.prod_univ_add]
  simp only [primaryInverseCoordinates_left,primaryInverseCoordinates_right,if_true,if_false,
    inputReference,Fin.addCases_left,Fin.addCases_right,primaryInverseMatrix]
  have hmat (input output : Color) :
      LinearMap.toMatrix' operator.symm.toLinearMap output input=operator.symm (Pi.single input 1) output := rfl
  simp only [hmat]
  simp_rw [show ∀ (input output : Color),rho⁻¹*primary.weight input*operator.symm (Pi.single input 1) output/primary.weight output=
    rho⁻¹*(primary.weight input*operator.symm (Pi.single input 1) output/primary.weight output) by intros;ring]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  ring

end
end AFT.RepresentedPolynomial
