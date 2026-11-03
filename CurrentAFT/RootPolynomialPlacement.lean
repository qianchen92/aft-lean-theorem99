import CurrentAFT.RootGroupedSourceFormula

/-! # Integrating all inactive root polynomials without root-atom inverses -/
namespace CurrentAFT.RootPolynomialPlacement
open AFT CycleRootExpansion
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
local instance classicalSubtypeDecidableEq {Index : Type*} {predicate : Index → Prop} :
    DecidableEq (Subtype predicate) := Classical.decEq _

variable {Selected Pool Color Value : Type*} [Fintype Selected] [Fintype Pool] [Fintype Color]
  [CommRing Value] [Algebra ℝ Value]

theorem independent_product (law : Pool → FiniteDist Color) (physical : Pool → Color → Value) :
    expectationLinear (FiniteDist.independent law) (fun word => ∏ index, physical index (word index)) =
      ∏ index, expectationLinear (law index) (physical index) := by
  simp only [expectationLinear, LinearMap.coe_mk, AddHom.coe_mk, FiniteDist.independent]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro word _
  rw [Finset.prod_smul]

/-- The selected joint polynomial may couple all active roots. Exactly the
unselected root factors are integrated into their actual mean polynomials. -/
theorem placed_product (embedding : Selected ↪ Pool) (law : Pool → FiniteDist Color)
    (score : (Selected → Color) → Value) (physical : Pool → Color → Value) :
    expectationLinear (FiniteDist.independent law)
      (fun word => score (word ∘ embedding) * ∏ index, physical index (word index)) =
      expectationLinear (FiniteDist.independent (fun index => law (embedding index)))
        (fun word => score word * ∏ index, physical (embedding index) (word index)) *
      ∏ index : {index : Pool // index ∉ Finset.univ.map embedding},
        expectationLinear (law index.val) (physical index.val) := by
  let partition := FiniteDist.placementPartition embedding
  let wordEquiv : ((Selected → Color) × ({index : Pool // index ∉ Finset.univ.map embedding} → Color)) ≃
      (Pool → Color) :=
    (Equiv.sumArrowEquivProdArrow Selected {index : Pool // index ∉ Finset.univ.map embedding} Color).symm.trans
      (Equiv.piCongrLeft (fun _ : Pool => Color) partition)
  have heval (word : (Selected → Color) × ({index : Pool // index ∉ Finset.univ.map embedding} → Color))
      (index : Selected ⊕ {index : Pool // index ∉ Finset.univ.map embedding}) :
      wordEquiv word (partition index) = Sum.elim word.1 word.2 index := by
    exact Equiv.piCongrLeft_apply_apply (fun _ : Pool => Color) partition _ index
  have hselected (word : (Selected → Color) × ({index : Pool // index ∉ Finset.univ.map embedding} → Color)) :
      wordEquiv word ∘ embedding = word.1 := by
    funext index
    exact heval word (.inl index)
  rw [← independent_product (fun index : {index : Pool // index ∉ Finset.univ.map embedding} => law index.val)
    (fun index => physical index.val)]
  simp only [expectationLinear, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← wordEquiv.sum_comp, Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro selected _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rest _
  rw [hselected]
  change ((∏ index, (law index).weight (wordEquiv (selected, rest) index)) •
    (score selected * ∏ index, physical index (wordEquiv (selected, rest) index))) = _
  rw [← partition.prod_comp (fun index => (law index).weight (wordEquiv (selected, rest) index)),
    ← partition.prod_comp (fun index => physical index (wordEquiv (selected, rest) index))]
  simp only [heval, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, FiniteDist.independent]
  simp only [partition, FiniteDist.placementPartition_inl, FiniteDist.placementPartition_inr]
  simp only [Algebra.smul_def, map_mul]
  ring

end
end CurrentAFT.RootPolynomialPlacement
