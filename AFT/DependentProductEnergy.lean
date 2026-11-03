import AFT.DependentTensorChannel

/-! # Splitting complete root and old-input energies without splitting their kernels -/
namespace AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Index : Type*} [Fintype Index] [DecidableEq Index]
  {Root Old : Index → Type*} [∀ i,Fintype (Root i)] [∀ i,Fintype (Old i)]

def dependentPairsEquiv : ((i : Index) → Root i × Old i) ≃
    (((i : Index) → Root i) × ((i : Index) → Old i)) where
  toFun word := (fun i => (word i).1,fun i => (word i).2)
  invFun pair i := (pair.1 i,pair.2 i)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The entire vector of roots is independent of the entire vector of old
inputs. This identity does not separate either of the two joint functions. -/
theorem dependentIndependent_prod_expectation (root : ∀ i,FiniteDist (Root i))
    (old : ∀ i,FiniteDist (Old i)) (function : ((i : Index) → Root i × Old i) → ℝ) :
    (dependentIndependent (fun i => (root i).prod (old i))).expectation function=
      (dependentIndependent root).expectation (fun roots =>
        (dependentIndependent old).expectation (fun inputs => function (fun i => (roots i,inputs i)))) := by
  unfold expectation
  rw [← (dependentPairsEquiv (Root:=Root) (Old:=Old)).symm.sum_comp,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro roots _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro inputs _
  simp only [dependentIndependent_weight,prod_weight,Finset.prod_mul_distrib,dependentPairsEquiv]
  change (∏ i,(root i).weight (roots i))*(∏ i,(old i).weight (inputs i))*function (fun i => (roots i,inputs i))=_
  ring

theorem dependentIndependent_prod_energy (root : ∀ i,FiniteDist (Root i))
    (old : ∀ i,FiniteDist (Old i)) (rootKernel : ((i : Index) → Root i) → ℝ)
    (oldKernel : ((i : Index) → Old i) → ℝ) :
    (dependentIndependent (fun i => (root i).prod (old i))).l2Sq
      (fun word => rootKernel (fun i => (word i).1)*oldKernel (fun i => (word i).2))=
      (dependentIndependent root).l2Sq rootKernel*(dependentIndependent old).l2Sq oldKernel := by
  unfold l2Sq
  rw [dependentIndependent_prod_expectation]
  simp only [mul_pow,expectation_const_mul,expectation_mul_const]

/-- Independent finite relabeling in each group preserves the complete
joint energy with no factor depending on the input alphabets. -/
theorem dependentIndependent_equiv_energy {Input : Index → Type*} [∀ i,Fintype (Input i)]
    (input : ∀ i,FiniteDist (Input i)) (root : ∀ i,FiniteDist (Root i)) (old : ∀ i,FiniteDist (Old i))
    (equiv : ∀ i,Input i ≃ Root i × Old i)
    (hweight : ∀ i point,(input i).weight point=(root i).weight (equiv i point).1*(old i).weight (equiv i point).2)
    (rootKernel : ((i : Index) → Root i) → ℝ) (oldKernel : ((i : Index) → Old i) → ℝ) :
    (dependentIndependent input).l2Sq
      (fun word => rootKernel (fun i => (equiv i (word i)).1)*oldKernel (fun i => (equiv i (word i)).2))=
      (dependentIndependent root).l2Sq rootKernel*(dependentIndependent old).l2Sq oldKernel := by
  apply Eq.trans ?_ (dependentIndependent_prod_energy root old rootKernel oldKernel)
  unfold l2Sq expectation
  rw [← (Equiv.piCongrRight equiv).sum_comp]
  apply Finset.sum_congr rfl
  intro word _
  simp only [dependentIndependent_weight,prod_weight,Equiv.piCongrRight_apply,hweight]
  rfl

end
end AFT.FiniteDist
