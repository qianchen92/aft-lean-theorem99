import CurrentAFT.ControlProduct

/-!
# Slot coherence of the actual symmetric coefficient product

Changing finite slot labels commutes with tensoring and with the complete
permutation average. These identities convert the proved sum-slot
associativity into the finite ordered labels used by coefficient arrays.
-/

namespace CurrentAFT.ControlCoherence

open AFT ControlCoordinates ControlProduct
open scoped BigOperators Classical

noncomputable section

variable {Primary Body : Type*}
variable {PS BS PT BT PU BU PV BV : Type*}

theorem reindexKernel_refl
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS) :
    reindexKernel (Equiv.refl PS) (Equiv.refl BS) kernel = kernel := rfl

theorem reindexKernel_comp (firstPrimary : PS ≃ PT) (secondPrimary : PT ≃ PU)
    (firstBody : BS ≃ BT) (secondBody : BT ≃ BU)
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS) :
    reindexKernel secondPrimary secondBody (reindexKernel firstPrimary firstBody kernel) =
      reindexKernel (firstPrimary.trans secondPrimary) (firstBody.trans secondBody) kernel := rfl

theorem tensor_reindex (firstPrimary : PS ≃ PU) (secondPrimary : PT ≃ PV)
    (firstBody : BS ≃ BU) (secondBody : BT ≃ BV)
    (first : Kernel (Primary := Primary) (Body := Body) PS BS)
    (second : Kernel (Primary := Primary) (Body := Body) PT BT) :
    reindexKernel (Equiv.sumCongr firstPrimary secondPrimary)
      (Equiv.sumCongr firstBody secondBody) (disjointTensor first second) =
      disjointTensor (reindexKernel firstPrimary firstBody first)
        (reindexKernel secondPrimary secondBody second) := by
  funext colors centers
  rfl

/-- A separately symmetric kernel is independent of which bijections
identify its complete primary and body slot sets with target labels. -/
theorem symmetric_reindex_unique (firstPrimary secondPrimary : PS ≃ PT)
    (firstBody secondBody : BS ≃ BT)
    (kernel : Kernel (Primary := Primary) (Body := Body) PS BS)
    (hsymmetric : ∀ (primaryOrder : Equiv.Perm PS) (bodyOrder : Equiv.Perm BS) colors centers,
      kernel (colors ∘ primaryOrder) (centers ∘ bodyOrder) = kernel colors centers) :
    reindexKernel firstPrimary firstBody kernel = reindexKernel secondPrimary secondBody kernel := by
  funext colors centers
  have hp : colors ∘ firstPrimary = (colors ∘ secondPrimary) ∘
      (firstPrimary.trans secondPrimary.symm) := by
    funext index
    simp only [Function.comp_apply, Equiv.trans_apply, Equiv.apply_symm_apply]
  have hb : centers ∘ firstBody = (centers ∘ secondBody) ∘
      (firstBody.trans secondBody.symm) := by
    funext index
    simp only [Function.comp_apply, Equiv.trans_apply, Equiv.apply_symm_apply]
  unfold reindexKernel
  rw [hp, hb]
  exact hsymmetric _ _ _ _

section FiniteLabels

def leftFlatten (first second third : ℕ) :
    ((Fin first ⊕ Fin second) ⊕ Fin third) ≃ Fin ((first + second) + third) :=
  (Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin third))).trans finSumFinEquiv

def rightFlatten (first second third : ℕ) :
    (Fin first ⊕ (Fin second ⊕ Fin third)) ≃ Fin (first + (second + third)) :=
  (Equiv.sumCongr (Equiv.refl (Fin first)) finSumFinEquiv).trans finSumFinEquiv

def finAssociator (first second third : ℕ) :
    Fin ((first + second) + third) ≃ Fin (first + (second + third)) :=
  (leftFlatten first second third).symm.trans
    ((Equiv.sumAssoc (Fin first) (Fin second) (Fin third)).trans
      (rightFlatten first second third))

variable {r s r' s' r'' s'' : ℕ}

theorem flatten_left_tensor
    (first : DensityKernel (Primary := Primary) (Body := Body) r s)
    (second : DensityKernel (Primary := Primary) (Body := Body) r' s')
    (third : DensityKernel (Primary := Primary) (Body := Body) r'' s'') :
    reindexKernel (leftFlatten r r' r'') (leftFlatten s s' s'')
      (disjointTensor (disjointTensor first second) third) =
        finDisjointTensor (finDisjointTensor first second) third := by
  rw [leftFlatten, leftFlatten, ← reindexKernel_comp,
    tensor_reindex, reindexKernel_refl]
  rfl

theorem flatten_right_tensor
    (first : DensityKernel (Primary := Primary) (Body := Body) r s)
    (second : DensityKernel (Primary := Primary) (Body := Body) r' s')
    (third : DensityKernel (Primary := Primary) (Body := Body) r'' s'') :
    reindexKernel (rightFlatten r r' r'') (rightFlatten s s' s'')
      (disjointTensor first (disjointTensor second third)) =
        finDisjointTensor first (finDisjointTensor second third) := by
  rw [rightFlatten, rightFlatten, ← reindexKernel_comp,
    tensor_reindex, reindexKernel_refl]
  rfl

theorem finDisjointTensor_assoc
    (first : DensityKernel (Primary := Primary) (Body := Body) r s)
    (second : DensityKernel (Primary := Primary) (Body := Body) r' s')
    (third : DensityKernel (Primary := Primary) (Body := Body) r'' s'') :
    reindexKernel (finAssociator r r' r'') (finAssociator s s' s'')
      (finDisjointTensor (finDisjointTensor first second) third) =
        finDisjointTensor first (finDisjointTensor second third) := by
  rw [← flatten_left_tensor]
  unfold finAssociator
  rw [reindexKernel_comp]
  have hp : (leftFlatten r r' r'').trans
      ((leftFlatten r r' r'').symm.trans
        ((Equiv.sumAssoc (Fin r) (Fin r') (Fin r'')).trans (rightFlatten r r' r''))) =
      (Equiv.sumAssoc (Fin r) (Fin r') (Fin r'')).trans (rightFlatten r r' r'') := by
    ext index
    simp
  have hb : (leftFlatten s s' s'').trans
      ((leftFlatten s s' s'').symm.trans
        ((Equiv.sumAssoc (Fin s) (Fin s') (Fin s'')).trans (rightFlatten s s' s''))) =
      (Equiv.sumAssoc (Fin s) (Fin s') (Fin s'')).trans (rightFlatten s s' s'') := by
    ext index
    simp
  rw [hp, hb, ← reindexKernel_comp, disjointTensor_assoc, flatten_right_tensor]

theorem symmetrized_fin_tensor_first
    (first : DensityKernel (Primary := Primary) (Body := Body) r s)
    (second : DensityKernel (Primary := Primary) (Body := Body) r' s') :
    symmetrize (finDisjointTensor (symmetrize first) second) =
      symmetrize (finDisjointTensor first second) := by
  unfold finDisjointTensor
  rw [← reindexKernel_symmetrize, symmetrizedTensor_first_symmetrize,
    reindexKernel_symmetrize]

theorem symmetrized_fin_tensor_second
    (first : DensityKernel (Primary := Primary) (Body := Body) r s)
    (second : DensityKernel (Primary := Primary) (Body := Body) r' s') :
    symmetrize (finDisjointTensor first (symmetrize second)) =
      symmetrize (finDisjointTensor first second) := by
  unfold finDisjointTensor
  rw [← reindexKernel_symmetrize, symmetrizedTensor_second_symmetrize,
    reindexKernel_symmetrize]

variable [Fintype Primary] [Fintype Body]

theorem homogeneousProduct_assoc_route (primary : FiniteDist Primary) (body : FiniteDist Body)
    (first : canonicalKernels primary body r s) (second : canonicalKernels primary body r' s')
    (third : canonicalKernels primary body r'' s'') :
    reindexKernel (finAssociator r r' r'') (finAssociator s s' s'')
      (homogeneousProduct primary body (homogeneousProduct primary body first second) third).val =
      (homogeneousProduct primary body first (homogeneousProduct primary body second third)).val := by
  change reindexKernel _ _
      (symmetrize (finDisjointTensor (symmetrize (finDisjointTensor first.val second.val)) third.val)) =
    symmetrize (finDisjointTensor first.val (symmetrize (finDisjointTensor second.val third.val)))
  rw [symmetrized_fin_tensor_first, symmetrized_fin_tensor_second,
    reindexKernel_symmetrize, finDisjointTensor_assoc]

/-- Associativity in the exact equality-based finite labels needed by
dependent arity arrays, without assuming a multiplication law. -/
theorem homogeneousProduct_assoc (primary : FiniteDist Primary) (body : FiniteDist Body)
    (first : canonicalKernels primary body r s) (second : canonicalKernels primary body r' s')
    (third : canonicalKernels primary body r'' s'') :
    reindexKernel (finCongr (Nat.add_assoc r r' r'')) (finCongr (Nat.add_assoc s s' s''))
      (homogeneousProduct primary body (homogeneousProduct primary body first second) third).val =
      (homogeneousProduct primary body first (homogeneousProduct primary body second third)).val := by
  apply Eq.trans _ (homogeneousProduct_assoc_route primary body first second third)
  exact symmetric_reindex_unique _ _ _ _ _
    (homogeneousProduct primary body (homogeneousProduct primary body first second) third).property.2.2

theorem homogeneousProduct_comm_cast (primary : FiniteDist Primary) (body : FiniteDist Body)
    (first : canonicalKernels primary body r s) (second : canonicalKernels primary body r' s') :
    reindexKernel (finCongr (Nat.add_comm r r')) (finCongr (Nat.add_comm s s'))
      (homogeneousProduct primary body first second).val =
      (homogeneousProduct primary body second first).val := by
  apply Eq.trans _ (homogeneousProduct_comm primary body first second)
  exact symmetric_reindex_unique _ _ _ _ _
    (homogeneousProduct primary body first second).property.2.2

end FiniteLabels

end

end CurrentAFT.ControlCoherence
