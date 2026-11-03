import AFT.RootSubsetPolynomial

/-! # Polynomial-valued independence with the original root coordinates retained -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
variable {Index Other Root Color : Type*} [Fintype Index] [Fintype Other] [Fintype Root]
local instance rootPartitionIndexDecEq : DecidableEq Index := Classical.decEq _
local instance rootPartitionOtherDecEq : DecidableEq Other := Classical.decEq _
local instance rootPartitionSubtypeDecEq {α : Type*} {p : α → Prop} : DecidableEq (Subtype p) := Classical.decEq _

/-- Relabel an identical independent root law by an actual equivalence. -/
theorem independent_polynomial_reindex (source : FiniteDist Root) (equiv : Other ≃ Index)
    (polynomial : (Index → Root) → Table Color) :
    (∑ word : Index → Root,MvPolynomial.C ((FiniteDist.independent (fun _ : Index => source)).weight word)*polynomial word)=
      ∑ word : Other → Root,MvPolynomial.C ((FiniteDist.independent (fun _ : Other => source)).weight word)*
        polynomial (fun index => word (equiv.symm index)) := by
  let e : (Other → Root) ≃ (Index → Root) :=
    { toFun := fun word index => word (equiv.symm index)
      invFun := fun word index => word (equiv index)
      left_inv := by intro word; funext index; simp
      right_inv := by intro word; funext index; simp }
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro word _
  congr 2
  exact equiv.symm.prod_comp (fun index => source.weight (word index))

omit [Fintype Other] in
/-- Arbitrary dependence within the selected roots is preserved. Only
roots outside that set are integrated as independent background blocks. -/
theorem independent_partition_polynomial (source : FiniteDist Root) (selected : Finset Index)
    (joint : (selected → Root) → Table Color)
    (outside : {index : Index // index ∉ selected} → Root → Table Color) :
    (∑ word : Index → Root,MvPolynomial.C ((FiniteDist.independent (fun _ : Index => source)).weight word)*
      (joint (fun index => word index)*∏ index : {index : Index // index ∉ selected},outside index (word index)))=
      (∑ chosen : selected → Root,MvPolynomial.C ((FiniteDist.independent (fun _ : selected => source)).weight chosen)*joint chosen)*
        ∏ index : {index : Index // index ∉ selected},∑ root,MvPolynomial.C (source.weight root)*outside index root := by
  let split := Equiv.piEquivPiSubtypeProd (fun index => index ∈ selected) (fun _ : Index => Root)
  have hrestrict (chosen : selected → Root) (rest : {index : Index // index ∉ selected} → Root) :
      (fun index : selected => split.symm (chosen,rest) index)=chosen := by
    funext index
    change (if h : (index : Index) ∈ selected then chosen ⟨index,h⟩ else rest ⟨index,h⟩)=_
    simp only [dif_pos index.property]
  have hrest (chosen : selected → Root) (rest : {index : Index // index ∉ selected} → Root)
      (index : {index : Index // index ∉ selected}) : split.symm (chosen,rest) index=rest index := by
    change (if h : (index : Index) ∈ selected then chosen ⟨index,h⟩ else rest ⟨index,h⟩)=_
    simp only [dif_neg index.property]
  have hbackground := independent_polynomial_product (fun _ : {index : Index // index ∉ selected} => source) outside
  simp only [Algebra.smul_def,MvPolynomial.algebraMap_eq] at hbackground
  rw [← hbackground,← split.symm.sum_comp,Fintype.sum_prod_type]
  simp_rw [hrestrict,hrest]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro chosen _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rest _
  change MvPolynomial.C (∏ index,source.weight (split.symm (chosen,rest) index))*_=_
  rw [subset_split_prod selected (fun _ root => source.weight root)]
  simp only [map_mul,FiniteDist.independent]
  ring
end
end AFT.RepresentedPolynomial
