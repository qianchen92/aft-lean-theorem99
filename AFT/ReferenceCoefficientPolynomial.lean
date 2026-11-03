import AFT.MixedReferenceCanonicalFibers
import AFT.CenteredPolynomial
import AFT.ActualRootResponse

/-! # The literal reference-centered coefficients reconstruct the full physical PGF -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]
local instance referenceCoefficientSubtypeDecEq (selected : Finset Slot) : DecidableEq selected := Classical.decEq _

def referenceCoefficientForm (primary reference : FiniteDist Color)
    (mass : (Slot → Color) → ℝ) (selected : Finset Slot) : MvPolynomial Color ℝ :=
  ∑ word : selected → Color,
    MvPolynomial.C (LocalTensors.referenceRestrictedComponent (fun _ : Slot => primary)
      (fun _ : Slot => reference) mass selected word*∏ slot,primary.weight (word slot))*
      ∏ slot,MvPolynomial.X (word slot)

theorem referenceAtom_form (primary reference : FiniteDist Color)
    (hp : ∀ color,0 < primary.weight color) (source : Color) :
    (∑ color,MvPolynomial.C (primary.weight color*MixedKernel.referenceAtom primary reference source color)*
      MvPolynomial.X color) = MvPolynomial.X source-profileForm reference.weight := by
  have he (color : Color) : primary.weight color*MixedKernel.referenceAtom primary reference source color =
      (if source=color then 1 else 0)-reference.weight color := by
    rw [MixedKernel.referenceAtom_eq]
    field_simp [(hp color).ne']
  simp_rw [he]
  simp only [map_sub,sub_mul,Finset.sum_sub_distrib,profileForm_apply]
  congr 1
  simp

/-- Each literal selected input coefficient is exactly its homogeneous
part of the actual centered physical generating law. -/
theorem referenceCoefficientForm_formula (primary reference : FiniteDist Color)
    (hp : ∀ color,0 < primary.weight color) (mass : (Slot → Color) → ℝ) (selected : Finset Slot) :
    referenceCoefficientForm primary reference mass selected =
      ∑ source,MvPolynomial.C (mass source)*
        ∏ slot : selected,(MvPolynomial.X (source slot)-profileForm reference.weight) := by
  cases Subsingleton.elim (inferInstance : DecidableEq Slot) (Classical.decEq Slot)
  unfold referenceCoefficientForm LocalTensors.referenceRestrictedComponent
  simp only [Finset.sum_mul,map_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro source _
  simp only [map_mul,map_prod,mul_assoc]
  have he : (∑ word : selected → Color,
      (∏ slot : selected,MvPolynomial.C (MixedKernel.referenceAtom primary reference (source slot) (word slot)))*
        ((∏ slot,MvPolynomial.C (primary.weight (word slot)))*∏ slot,MvPolynomial.X (word slot))) =
      ∏ slot : selected,(MvPolynomial.X (source slot)-profileForm reference.weight) := by
    simp_rw [← Finset.prod_mul_distrib]
    rw [← Fintype.prod_sum (fun slot : selected => fun color : Color =>
      MvPolynomial.C (MixedKernel.referenceAtom primary reference (source slot) color)*
        (MvPolynomial.C (primary.weight color)*MvPolynomial.X color))]
    apply Finset.prod_congr rfl
    intro slot _
    have hh := referenceAtom_form primary reference hp (source slot)
    convert hh using 1
    apply Finset.sum_congr rfl
    intro color _
    rw [map_mul]
    ring
  rw [← Finset.mul_sum,he]

theorem referenceCoefficientForm_empty (primary reference : FiniteDist Color)
    (mass : (Slot → Color) → ℝ) :
    referenceCoefficientForm primary reference mass ∅ = MvPolynomial.C (∑ source,mass source) := by
  simp [referenceCoefficientForm,LocalTensors.referenceRestrictedComponent]

/-- Every subset, including the exact constant mass, appears once. -/
theorem centeredGeneratingLinear_reference_expansion (primary reference : FiniteDist Color)
    (hp : ∀ color,0 < primary.weight color) (mass : (Slot → Color) → ℝ) :
    centeredGeneratingLinear reference.weight mass =
      ∑ selected : Finset Slot,referenceCoefficientForm primary reference mass selected := by
  cases Subsingleton.elim (inferInstance : DecidableEq Slot) (Classical.decEq Slot)
  simp_rw [referenceCoefficientForm_formula primary reference hp]
  rw [Finset.sum_comm]
  simp only [centeredGeneratingLinear,LinearMap.coe_mk,AddHom.coe_mk,Algebra.smul_def,MvPolynomial.algebraMap_eq]
  change (∑ source,MvPolynomial.C (mass source)*∏ slot,centeredFactor reference.weight (source slot)) = _
  apply Finset.sum_congr rfl
  intro source _
  rw [← Finset.mul_sum]
  congr 1
  have hh := Fintype.prod_add
    (fun slot => MvPolynomial.X (R := ℝ) (source slot)-profileForm reference.weight)
    (fun _ : Slot => (1 : MvPolynomial Color ℝ))
  simp only [Finset.prod_const_one,mul_one] at hh
  calc
    _ = ∑ selected : Finset Slot,∏ slot ∈ selected,
        (MvPolynomial.X (source slot)-profileForm reference.weight) := by
      convert hh using 1
      apply Finset.prod_congr rfl
      intro slot _
      unfold centeredFactor
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro selected _
      exact (Finset.prod_coe_sort selected _).symm

end
end AFT.RepresentedPolynomial
