import AFT.FiniteSeedOutput

/-! # The exact contraction of every unchanged old input coordinate -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance remainingOutputUnitDecEq : DecidableEq Unit := Classical.decEq _
variable {Rest Color Output : Type*} [Fintype Rest] [Fintype Color] [Fintype Output]

def remainingOutput (reference : Rest → FiniteDist Color)
    (channel : Rest → Color → Output → ℝ) :
    ((Rest → Color) → MvPolynomial Output ℝ) →ₗ[ℝ] MvPolynomial Output ℝ where
  toFun value := ∑ rest,MvPolynomial.C (∏ slot,(reference slot).weight (rest slot))*value rest*
    ∏ slot,channelForm (channel slot) (rest slot)
  map_add' first second := by
    simp only [Pi.add_apply,mul_add,add_mul,Finset.sum_add_distrib]
  map_smul' scalar value := by
    simp only [Pi.smul_apply,Algebra.smul_def,MvPolynomial.algebraMap_eq,RingHom.id_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro rest _
    ring

theorem remainingOutput_apply (reference : Rest → FiniteDist Color)
    (channel : Rest → Color → Output → ℝ) (value : (Rest → Color) → MvPolynomial Output ℝ) :
    remainingOutput reference channel value =
      ∑ rest,MvPolynomial.C (∏ slot,(reference slot).weight (rest slot))*value rest*
        ∏ slot,channelForm (channel slot) (rest slot) := rfl

theorem remainingOutput_mul (reference : Rest → FiniteDist Color)
    (channel : Rest → Color → Output → ℝ) (value : (Rest → Color) → MvPolynomial Output ℝ)
    (factor : MvPolynomial Output ℝ) :
    remainingOutput reference channel (fun rest => value rest*factor) =
      remainingOutput reference channel value*factor := by
  simp only [remainingOutput_apply,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro rest _
  ring

theorem indexedOutput_unit (primary : FiniteDist Color) (channel : Color → Output → ℝ)
    (kernel : (Unit → Color) → ℝ) :
    indexedOutput (fun _ : Unit => primary) (fun _ : Unit => channel) kernel =
      ∑ color,MvPolynomial.C (kernel (fun _ => color)*primary.weight color)*channelForm channel color := by
  unfold indexedOutput
  rw [← (Equiv.funUnique Unit Color).symm.sum_comp]
  simp only [Fintype.prod_unique,Equiv.funUnique_symm_apply,uniqueElim_const]
  have he (color : Color) : (uniqueElim color : Unit → Color)=(fun _ => color) := by funext slot; rfl
  simp only [he]

theorem indexedOutput_unit_profile (primary : FiniteDist Color) (channel : Color → Output → ℝ)
    (kernel : Color → ℝ) :
    indexedOutput (fun _ : Unit => primary) (fun _ : Unit => channel) (fun word => kernel (word ())) =
      ∑ output,MvPolynomial.C (∑ input,primary.weight input*kernel input*channel input output)*
        MvPolynomial.X output := by
  rw [indexedOutput_unit]
  simp only [channelForm,Finset.mul_sum,← mul_assoc,← map_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro output _
  simp only [map_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro input _
  congr 2
  ring

end
end AFT.RepresentedPolynomial
