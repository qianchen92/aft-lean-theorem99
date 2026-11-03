import CurrentAFT.GroupedKernelProduct

/-! # Exact grouped-kernel identity of iterated homogeneous products -/
namespace CurrentAFT.GroupedKernelProduct
open AFT ControlCoordinates ControlProduct ControlNorm GradedControlAlgebra GroupedKernelNorm
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
local instance productImageFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance productImageSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} :
    DecidableEq (Sigma Slots) := Classical.decEq _

variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]

def rawProduct (count : ℕ) (r s : Fin count → ℕ)
    (kernels : (index : Fin count) → DensityKernel (Primary := Primary) (Body := Body) (r index) (s index)) :
    DensityKernel (Primary := Primary) (Body := Body) (∑ index, r index) (∑ index, s index) :=
  reindexKernel (slotsEquiv count r) (slotsEquiv count s)
    (flatten (fun index => Fin (r index)) (fun index => Fin (s index))
      (fun word => ∏ index, kernels index (word index).1 (word index).2))

omit [Fintype Primary] [Fintype Body] in
theorem rawProduct_succ (count : ℕ) (r s : Fin (count + 1) → ℕ)
    (kernels : (index : Fin (count + 1)) → DensityKernel (Primary := Primary) (Body := Body) (r index) (s index)) :
    rawProduct (count + 1) r s kernels =
      reindexKernel (finCongr (Fin.sum_univ_succ r).symm) (finCongr (Fin.sum_univ_succ s).symm)
        (finDisjointTensor (kernels 0)
          (rawProduct count (fun index => r index.succ) (fun index => s index.succ)
            (fun index => kernels index.succ))) := by
  funext colors centers
  simp only [rawProduct, reindexKernel, flatten, wordEquiv, Equiv.coe_fn_mk,
    Fin.prod_univ_succ, slotsEquiv, sigmaHeadEquiv, Equiv.trans_apply,
    Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, Equiv.refl_apply, Fin.cases_zero, Fin.cases_succ,
    finDisjointTensor, disjointTensor, Function.comp_def]

/-- The iterated star product equals one symmetrization of the whole
disjoint product, with every input and output coordinate retained. -/
theorem iteratedProduct_val (primary : FiniteDist Primary) (body : FiniteDist Body)
    (count : ℕ) (r s : Fin count → ℕ)
    (kernels : (index : Fin count) → canonicalKernels primary body (r index) (s index)) :
    (iteratedProduct primary body count r s kernels).val =
      symmetrize (rawProduct count r s (fun index => (kernels index).val)) := by
  induction count with
  | zero =>
    have hraw : rawProduct 0 r s (fun index => (kernels index).val) = fun _ _ => 1 := by
      funext colors centers
      simp only [rawProduct, reindexKernel, flatten, wordEquiv, Equiv.coe_fn_mk, Fin.prod_univ_zero]
    rw [hraw, symmetrize_of_symmetric _ (by intros; rfl)]
    rfl
  | succ count ih =>
    rw [iteratedProduct, transportKernel_val]
    change reindexKernel _ _ (symmetrize (finDisjointTensor (kernels 0).val
      (iteratedProduct primary body count (fun index => r index.succ)
        (fun index => s index.succ) (fun index => kernels index.succ)).val)) = _
    rw [ih, ControlCoherence.symmetrized_fin_tensor_second, reindexKernel_symmetrize, rawProduct_succ]

end
end CurrentAFT.GroupedKernelProduct
