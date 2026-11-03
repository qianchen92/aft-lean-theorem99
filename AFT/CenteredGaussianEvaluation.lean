import AFT.ActualRootResponse

/-! # The actual centered PGF evaluated in normalized Gaussian coordinates -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]

omit [Fintype Slot] in
theorem atomCoefficient_div (reference : FiniteDist Color) (href : ∀ color,0<reference.weight color)
    (input output : Color) :
    LocalTensors.atomCoefficient reference input output=
      ((if input=output then 1 else 0)-reference.weight output)/Real.sqrt (reference.weight output) := by
  have hs := Real.sqrt_pos.mpr (href output)
  have hsq := Real.sq_sqrt (href output).le
  unfold LocalTensors.atomCoefficient Hoeffding.centeredAtom
  by_cases he : input=output
  · simp only [if_pos he]
    field_simp [hs.ne',(href output).ne']
    nlinarith
  · simp only [if_neg he,zero_sub]
    apply (eq_div_iff hs.ne').mpr
    nlinarith

omit [Fintype Slot] in
theorem centeredFactor_gaussian (reference : FiniteDist Color) (href : ∀ color,0<reference.weight color)
    (color : Color) (value : Color → ℂ) :
    MvPolynomial.eval₂ Complex.ofRealHom (fun output => value output/(Real.sqrt (reference.weight output) : ℂ))
      (centeredFactor reference.weight color)=1+LocalTensors.atomLinear reference color value := by
  simp only [centeredFactor,profileForm_apply,MvPolynomial.eval₂_sub,MvPolynomial.eval₂_add,
    MvPolynomial.eval₂_one,MvPolynomial.eval₂_X,MvPolynomial.eval₂_sum,
    MvPolynomial.eval₂_mul,MvPolynomial.eval₂_C,LocalTensors.atomLinear,atomCoefficient_div reference href]
  simp only [Complex.ofReal_div,Complex.ofReal_sub,apply_ite,Complex.ofReal_one,Complex.ofReal_zero,
    sub_div,sub_mul,Finset.sum_sub_distrib]
  have he : (∑ output,((if color=output then (1 : ℂ) else 0)/(Real.sqrt (reference.weight output) : ℂ))*value output)=
      value color/(Real.sqrt (reference.weight color) : ℂ) := by
    simp only [ite_div,one_div,zero_div,ite_mul,zero_mul]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ,if_true]
    ring
  rw [he]
  have hsum : (∑ output,(reference.weight output : ℂ)/(Real.sqrt (reference.weight output) : ℂ)*value output)=
      ∑ output,(reference.weight output : ℂ)*(value output/(Real.sqrt (reference.weight output) : ℂ)) := by
    apply Finset.sum_congr rfl
    intro output houtput
    ring
  rw [hsum]
  change 1+value color/(Real.sqrt (reference.weight color) : ℂ)-
    (∑ output,(reference.weight output : ℂ)*(value output/(Real.sqrt (reference.weight output) : ℂ)))=
    1+(value color/(Real.sqrt (reference.weight color) : ℂ)-
    (∑ output,(reference.weight output : ℂ)*(value output/(Real.sqrt (reference.weight output) : ℂ))))
  ring

/-- This is the exact physical PGF, not a formal Fock surrogate. -/
theorem centeredGeneratingLinear_gaussian (reference : FiniteDist Color)
    (href : ∀ color,0<reference.weight color) (mass : (Slot → Color) → ℝ) (value : Color → ℂ) :
    MvPolynomial.eval₂ Complex.ofRealHom (fun output => value output/(Real.sqrt (reference.weight output) : ℂ))
      (centeredGeneratingLinear reference.weight mass)=
      LocalTensors.localGenerating (fun _ : Slot => reference) mass value := by
  simp only [centeredGeneratingLinear,LinearMap.coe_mk,AddHom.coe_mk,Algebra.smul_def,MvPolynomial.algebraMap_eq,
    MvPolynomial.eval₂_sum,MvPolynomial.eval₂_mul,MvPolynomial.eval₂_C,MvPolynomial.eval₂_prod,
    centeredFactor_gaussian reference href,LocalTensors.localGenerating]
  rfl

end
end AFT.RepresentedPolynomial
