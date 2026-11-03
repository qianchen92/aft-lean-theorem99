import AFT.KernelPolynomialMonomial
import AFT.WholeBoundarySeed
import AFT.PrimaryInverseMatrix

/-! # Whole boundary projection under arbitrary polynomial forms -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
variable {Slot Color Output : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]

/-- The transpose finite-matrix action on arbitrary polynomial-valued forms. -/
def matrixPolynomialForm (matrix : Color → Color → ℝ) (form : Color → Table Output)
    (input : Color) : Table Output :=
  ∑ output,MvPolynomial.C (matrix input output)*form output

theorem kernelPolynomial_matrixApply (matrix : Slot → Color → Color → ℝ)
    (forms : Slot → Color → Table Output) (kernel : (Slot → Color) → ℝ) :
    kernelPolynomial forms (MixedKernel.matrixApply matrix kernel)=
      kernelPolynomial (fun slot => matrixPolynomialForm (matrix slot) (forms slot)) kernel := by
  unfold kernelPolynomial MixedKernel.matrixApply matrixPolynomialForm
  simp only [map_sum,map_mul,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro input _
  rw [Fintype.prod_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro output _
  rw [Finset.prod_mul_distrib,← map_prod MvPolynomial.C]
  ring

theorem kernelPolynomial_sub (forms : Slot → Color → Table Output)
    (first second : (Slot → Color) → ℝ) :
    kernelPolynomial forms (first-second)=kernelPolynomial forms first-kernelPolynomial forms second := by
  simp only [kernelPolynomial,Pi.sub_apply,map_sub,sub_mul,Finset.sum_sub_distrib]

omit [Fintype Slot] [DecidableEq Slot] in
theorem inputKernelPolynomial_all_primary (primary body : Color → Table Output)
    (seed : InputSeed Color) (hbody : seed.bodyOrder=0) :
    inputKernelPolynomial primary body seed=kernelPolynomial (fun _ => primary) seed.kernel := by
  have hf : (Fin.addCases (fun _ : Fin seed.primaryOrder => primary)
      (fun _ : Fin seed.bodyOrder => body))=(fun _ : Fin (seed.primaryOrder+seed.bodyOrder) => primary) := by
    funext slot
    cases slot using Fin.addCases with
    | left slot => simp only [Fin.addCases_left]
    | right slot => exact False.elim (by have := slot.isLt; omega)
  simp only [inputKernelPolynomial,hf]
  unfold kernelPolynomial
  apply Finset.sum_congr (by ext; simp)
  intro word _
  rfl

variable [colorDecEq : DecidableEq Color]

/-- The complementary legal operator is density-conjugated exactly as in
`inputIteration`, including the total division convention at zero atoms. -/
def complementaryPrimaryForm (primary : FiniteDist Color)
    (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ)) (interior : Finset Color)
    (form : Color → Table Output) : Color → Table Output :=
  matrixPolynomialForm
    (fun input output => primary.weight input*
      LinearMap.toMatrix' (LinearMap.id-legalInputProjection operator
        (boundaryIdealProjection interior primary.weight)) output input / primary.weight output) form

omit [Fintype Slot] [DecidableEq Slot] in
theorem wholeBoundarySeed_inputKernelPolynomial (primary body : FiniteDist Color)
    (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ)) (interior : Finset Color)
    (primaryForm bodyForm : Color → Table Output) (seed : InputSeed Color) (hbody : seed.bodyOrder=0) :
    inputKernelPolynomial primaryForm bodyForm (wholeBoundarySeed primary body operator interior seed)=
      inputKernelPolynomial primaryForm bodyForm seed-
        inputKernelPolynomial (complementaryPrimaryForm primary operator interior primaryForm) bodyForm seed := by
  rw [inputKernelPolynomial_all_primary _ _ (wholeBoundarySeed primary body operator interior seed) hbody,
    inputKernelPolynomial_all_primary _ _ seed hbody,
    inputKernelPolynomial_all_primary _ _ seed hbody]
  change kernelPolynomial (fun _ => primaryForm)
    (MixedKernel.jointLegalProjection (primaryCoordinates seed).reverse
      (fun _ => legalInputProjection operator (boundaryIdealProjection interior primary.weight))
      (inputReference primary body seed) seed.kernel)=_
  rw [MixedKernel.jointLegalProjection,LinearMap.sub_apply,LinearMap.id_apply,kernelPolynomial_sub]
  congr 1
  have hkernel : MixedKernel.inputIteration (primaryCoordinates seed).reverse
      (fun _ => LinearMap.id-legalInputProjection operator (boundaryIdealProjection interior primary.weight))
      (inputReference primary body seed) seed.kernel=
      MixedKernel.matrixApply (fun _ input output => primary.weight input*
        LinearMap.toMatrix' (LinearMap.id-legalInputProjection operator
          (boundaryIdealProjection interior primary.weight)) output input/primary.weight output) seed.kernel := by
    funext output
    rw [MixedKernel.inputIteration_matrix _ (List.nodup_reverse.mpr (primaryCoordinates_nodup seed))
      (fun slot => List.mem_reverse.mpr (primaryCoordinates_complete seed hbody slot))]
    simp only [all_primary_reference primary body seed hbody,MixedKernel.matrixApply]
    apply Finset.sum_congr (by ext; simp)
    intro input _
    congr 1
    apply Finset.prod_congr rfl
    intro slot _
    have he : colorDecEq=Classical.decEq Color := Subsingleton.elim _ _
    cases he
    rfl
  rw [hkernel,kernelPolynomial_matrixApply]
  rfl

omit [DecidableEq Color] in
theorem inputKernelPolynomial_primaryFiniteSeed (primary body : Color → Table Output)
    (kernel : (Slot → Color) → ℝ) :
    inputKernelPolynomial primary body (primaryFiniteSeed kernel)=
      kernelPolynomial (fun _ => primary) kernel := by
  rw [inputKernelPolynomial_all_primary _ _ _ rfl]
  exact kernelPolynomial_equiv (Fintype.equivFin Slot) (fun _ => primary) kernel

end
end AFT.RepresentedPolynomial
