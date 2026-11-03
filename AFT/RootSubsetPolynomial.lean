import AFT.RootPolynomialCutoff
import AFT.RootSourcePolynomial

/-! # Exact finite root integration outside a selected canonical source set -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
variable {Index Source Color : Type*} [Fintype Index] [DecidableEq Index] [Fintype Source]
local instance rootSubsetPolySubtypeDecEq {α : Type*} {p : α → Prop} : DecidableEq (Subtype p) := Classical.decEq _

/-- Full canonicality permits subtracting any source-independent local
polynomial. This cancellation is on the actual joint coefficient. -/
theorem canonical_polynomial_product_centered (reference : Index → FiniteDist Source)
    (kernel : (Index → Source) → ℝ) (hc : Hoeffding.Canonical reference Finset.univ kernel)
    (polynomial : Index → Source → Table Color) (base : Index → Table Color) :
    (∑ word,MvPolynomial.C ((FiniteDist.independent reference).weight word*kernel word)*
      ∏ index,polynomial index (word index))=
    ∑ word,MvPolynomial.C ((FiniteDist.independent reference).weight word*kernel word)*
      ∏ index,(polynomial index (word index)-base index) := by
  have he (word : Index → Source) := Fintype.prod_add
    (fun index => polynomial index (word index)-base index) base
  simp only [sub_add_cancel] at he
  simp_rw [he,Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single (Finset.univ : Finset Index)]
  · simp only [Finset.compl_univ,Finset.prod_empty,mul_one]
  · intro used _ hne
    have hz := canonical_polynomial_support_zero reference Finset.univ used kernel hc
      (fun word => ∏ index ∈ used,(polynomial index (word index)-base index)) (by
        intro first second heq
        apply Finset.prod_congr rfl
        intro index hi
        rw [heq index hi]) (by intro h; exact hne (Finset.Subset.antisymm (Finset.subset_univ _) h))
    simp only [Algebra.smul_def,MvPolynomial.algebraMap_eq] at hz
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul,hz,zero_mul]
  · simp

omit [Fintype Source] in
/-- Products split across a subset and its exact complement. -/
theorem subset_split_prod {R : Type*} [CommMonoid R] (selected : Finset Index)
    (function : Index → Source → R)
    (chosen : selected → Source) (rest : {index : Index // index∉selected} → Source) :
    (∏ index,function index ((Equiv.piEquivPiSubtypeProd (fun index => index∈selected)
      (fun _ : Index => Source)).symm (chosen,rest) index))=
      (∏ index : selected,function index (chosen index))*
        ∏ index : {index : Index // index∉selected},function index (rest index) := by
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun index => index∈selected)]
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr (by ext; simp)
    intro index _
    change function index (if h : (index : Index)∈selected then chosen ⟨index,h⟩ else rest ⟨index,h⟩)=_
    simp only [dif_pos index.property]
  · apply Finset.prod_congr (by ext; simp)
    intro index _
    change function index (if h : (index : Index)∈selected then chosen ⟨index,h⟩ else rest ⟨index,h⟩)=_
    simp only [dif_neg index.property]

/-- Integrate the complement under its genuine independent source law.
Only the selected root word is retained inside the arbitrary joint kernel. -/
theorem subset_polynomial_product (reference : Index → FiniteDist Source)
    (selected : Finset Index) (kernel : (selected → Source) → ℝ)
    (polynomial : Index → Source → Table Color) :
    (∑ word : Index → Source,
      MvPolynomial.C ((FiniteDist.independent reference).weight word*kernel (fun slot => word slot))*
        ∏ index,polynomial index (word index))=
      (∑ chosen : selected → Source,
        MvPolynomial.C ((FiniteDist.independent (fun slot : selected => reference slot)).weight chosen*kernel chosen)*
          ∏ index : selected,polynomial index (chosen index))*
        ∏ index : {index : Index // index ∉ selected},∑ root,
          MvPolynomial.C ((reference index).weight root)*polynomial index root := by
  cases Subsingleton.elim (inferInstance : DecidableEq Index) (Classical.decEq Index)
  let split := Equiv.piEquivPiSubtypeProd (fun index => index∈selected) (fun _ : Index => Source)
  have hrestrict (chosen : selected → Source) (rest : {index : Index // index∉selected} → Source) :
      (fun index : selected => split.symm (chosen,rest) index)=chosen := by
    funext index
    change (if h : (index : Index)∈selected then chosen ⟨index,h⟩ else rest ⟨index,h⟩)=_
    simp only [dif_pos index.property]
  rw [← split.symm.sum_comp,Fintype.sum_prod_type]
  have hbackground : (∑ rest : {index : Index // index∉selected} → Source,
      MvPolynomial.C ((FiniteDist.independent (fun index : {index : Index // index∉selected} => reference index)).weight rest)*
        ∏ index : {index : Index // index∉selected},polynomial index (rest index))=
        ∏ index : {index : Index // index∉selected},∑ root,
          MvPolynomial.C ((reference index).weight root)*polynomial index root := by
    simpa only [Algebra.smul_def,MvPolynomial.algebraMap_eq] using
      independent_polynomial_product (fun index : {index : Index // index∉selected} => reference index)
        (fun index root => polynomial index root)
  rw [← hbackground,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro chosen _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rest _
  simp only [hrestrict,FiniteDist.independent]
  rw [subset_split_prod selected (fun index source => (reference index).weight source),subset_split_prod selected polynomial]
  simp only [map_mul]
  ring
end
end AFT.RepresentedPolynomial
