import CurrentAFT.GroupedKernelProductImage

/-! # Arbitrary finite group labels for the actual iterated star product -/
namespace CurrentAFT.GroupedKernelProduct
open AFT ControlCoordinates ControlProduct ControlNorm GradedControlAlgebra GroupedKernelNorm
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
local instance productFiniteFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance productFiniteSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} :
    DecidableEq (Sigma Slots) := Classical.decEq _

variable {Primary Body Group : Type*} [Fintype Primary] [Fintype Body] [Fintype Group]

def finiteProduct (primary : FiniteDist Primary) (body : FiniteDist Body)
    (r s : Group → ℕ) (kernels : (group : Group) → canonicalKernels primary body (r group) (s group)) :
    canonicalKernels primary body (∑ group, r group) (∑ group, s group) :=
  transportKernel primary body ((Fintype.equivFin Group).symm.sum_comp r)
    ((Fintype.equivFin Group).symm.sum_comp s)
    (iteratedProduct primary body (Fintype.card Group)
      (fun index => r ((Fintype.equivFin Group).symm index))
      (fun index => s ((Fintype.equivFin Group).symm index))
      (fun index => kernels ((Fintype.equivFin Group).symm index)))

def finiteSlotsEquiv (sizes : Group → ℕ) :
    Sigma (fun group => Fin (sizes group)) ≃ Fin (∑ group, sizes group) :=
  (Equiv.sigmaCongrLeft (β := fun group => Fin (sizes group)) (Fintype.equivFin Group).symm).symm.trans
    ((slotsEquiv (Fintype.card Group) (fun index => sizes ((Fintype.equivFin Group).symm index))).trans
      (finCongr ((Fintype.equivFin Group).symm.sum_comp sizes)))

theorem finite_product_embed (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (r s : Group → ℕ) (kernels : (group : Group) → canonicalKernels primary body (r group) (s group))
    (hdegree : (∑ group, r group) + (∑ group, s group) ≤ order)
    (hlocal : ∀ group, r group + s group ≤ order) :
    (∏ group, embed primary body order (hlocal group) (kernels group)) =
      embed primary body order hdegree (finiteProduct primary body r s kernels) := by
  unfold finiteProduct
  rw [embed_transport primary body order _ _
    (show (∑ index, r ((Fintype.equivFin Group).symm index)) +
        (∑ index, s ((Fintype.equivFin Group).symm index)) ≤ order by
      simpa only [Equiv.sum_comp] using hdegree) hdegree]
  rw [← product_embed primary body order (Fintype.card Group) _ _ _ _
    (fun index => hlocal ((Fintype.equivFin Group).symm index))]
  exact ((Fintype.equivFin Group).symm.prod_comp
    (fun group => embed primary body order (hlocal group) (kernels group))).symm

theorem finiteProduct_val (primary : FiniteDist Primary) (body : FiniteDist Body)
    (r s : Group → ℕ) (kernels : (group : Group) → canonicalKernels primary body (r group) (s group)) :
    (finiteProduct primary body r s kernels).val =
      canonicalize (fun group => Fin (r group)) (fun group => Fin (s group))
        (finiteSlotsEquiv r) (finiteSlotsEquiv s)
        (fun word => ∏ group, (kernels group).val (word group).1 (word group).2) := by
  let e := (Fintype.equivFin Group).symm
  let ep := Equiv.sigmaCongrLeft (β := fun group => Fin (r group)) e
  let eb := Equiv.sigmaCongrLeft (β := fun group => Fin (s group)) e
  have hflatten :
      flatten (fun index => Fin (r (e index))) (fun index => Fin (s (e index)))
        (fun word => ∏ index, (kernels (e index)).val (word index).1 (word index).2) =
      reindexKernel ep.symm eb.symm
        (flatten (fun group => Fin (r group)) (fun group => Fin (s group))
          (fun word => ∏ group, (kernels group).val (word group).1 (word group).2)) := by
    funext colors centers
    have h := e.prod_comp (fun group => (kernels group).val
      (fun slot => colors (ep.symm ⟨group, slot⟩)) (fun slot => centers (eb.symm ⟨group, slot⟩)))
    change (∏ index, (kernels (e index)).val (fun slot => colors ⟨index, slot⟩)
      (fun slot => centers ⟨index, slot⟩)) = _
    apply Eq.trans ?_ h
    apply Finset.prod_congr rfl
    intro index _
    apply congrArg₂ (kernels (e index)).val
    · funext slot
      exact congrArg colors (ep.symm_apply_apply ⟨index, slot⟩).symm
    · funext slot
      exact congrArg centers (eb.symm_apply_apply ⟨index, slot⟩).symm
  unfold finiteProduct
  rw [transportKernel_val, iteratedProduct_val, reindexKernel_symmetrize]
  apply congrArg ControlProduct.symmetrize
  change reindexKernel _ _ (reindexKernel _ _
    (flatten (fun index => Fin (r (e index))) (fun index => Fin (s (e index))) _)) = _
  rw [hflatten, ControlCoherence.reindexKernel_comp, ControlCoherence.reindexKernel_comp]
  rfl

end
end CurrentAFT.GroupedKernelProduct
