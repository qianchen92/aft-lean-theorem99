import AFT.FiniteProbability

/-! # Exact finite Fubini for the two roots of every primary role -/
namespace AFT
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Primary Body Root Color : Type*} [Fintype Primary] [Fintype Body] [Fintype Root]

def roleRootGrouping : (((Primary ⊕ Primary) ⊕ Body) → Root) ≃
    (Primary → Root × Root) × (Body → Root) :=
  ((Equiv.sumArrowEquivProdArrow (Primary ⊕ Primary) Body Root).trans
    (Equiv.prodCongr (Equiv.sumArrowEquivProdArrow Primary Primary Root) (Equiv.refl _))).trans
    (Equiv.prodCongr (Equiv.arrowProdEquivProdArrow Primary (fun _ => Root) (fun _ => Root)).symm (Equiv.refl _))

/-- No rank-one assumption on `first index` is used: both roots are retained
inside each arbitrary local polynomial before finite Fubini is applied. -/
theorem independent_role_sources (source : FiniteDist Root)
    (first : Primary → Root → Root → MvPolynomial Color ℝ)
    (second : Body → Root → MvPolynomial Color ℝ) :
    (∑ word : ((Primary ⊕ Primary) ⊕ Body) → Root,
      (∏ index,source.weight (word index)) •
        ((∏ index,first index (word (.inl (.inl index))) (word (.inl (.inr index))))*
          ∏ index,second index (word (.inr index))))=
      (∏ index,∑ a,∑ b,(source.weight a*source.weight b) • first index a b)*
        ∏ index,∑ a,source.weight a • second index a := by
  rw [← (roleRootGrouping (Primary:=Primary) (Body:=Body) (Root:=Root)).symm.sum_comp]
  change (∑ pair : (Primary → Root × Root) × (Body → Root),
    (∏ index : (Primary ⊕ Primary) ⊕ Body,source.weight
      (Sum.elim (Sum.elim (fun i => (pair.1 i).1) (fun i => (pair.1 i).2)) pair.2 index)) •
      ((∏ index,first index (pair.1 index).1 (pair.1 index).2)*∏ index,second index (pair.2 index)))=_
  simp only [Fintype.prod_sum_type,Sum.elim_inl,Sum.elim_inr,Algebra.smul_def,MvPolynomial.algebraMap_eq,
    map_mul,map_prod,Fintype.sum_prod_type]
  calc
    _ = (∑ word : Primary → Root × Root,∏ index,
        (MvPolynomial.C (source.weight (word index).1)*MvPolynomial.C (source.weight (word index).2))*
          first index (word index).1 (word index).2)*
      (∑ word : Body → Root,∏ index,MvPolynomial.C (source.weight (word index))*second index (word index)) := by
      rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro firstWord _
      apply Finset.sum_congr rfl
      intro secondWord _
      simp only [Finset.prod_mul_distrib]
      ring
    _ = _ := by
      rw [← Fintype.prod_sum (fun index (pair : Root × Root) => (MvPolynomial.C (source.weight pair.1)*MvPolynomial.C (source.weight pair.2))*first index pair.1 pair.2),
        ← Fintype.prod_sum (fun index (value : Root) => MvPolynomial.C (source.weight value)*second index value)]
      simp only [Fintype.sum_prod_type]

end
end AFT
