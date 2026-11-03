import CurrentAFT.PairedRootInput

/-! # Coordinate centering of the true joint root and control source -/
namespace CurrentAFT.PairedRootCentering
open AFT ActualBlockFock TaggedSelection PairedRootPlacement PairedRootInput
  ControlCoordinates RaisingPatternBudget
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
local instance classicalSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} : DecidableEq (Sigma Slots) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount

def rootDensity {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (roots : Sigma (groupRootSlots selection tagged) → CycleRootExpansion.Root security) : ℝ :=
  CycleRootExpansion.selectedCoefficient security tagged.card (labels tagged layout)
    (roots ∘ sourceEmbedding selection tagged)

theorem rootDensity_centered {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (index : Fin tagged.card) :
    Hoeffding.CenteredAt (fun _ => CycleRootExpansion.rootReference security)
      (sourceEmbedding selection tagged index) (rootDensity selection tagged layout) := by
  intro roots
  change (∑ root, (CycleRootExpansion.rootReference security).weight root *
    CycleRootExpansion.selectedCoefficient security tagged.card (labels tagged layout)
      (Function.update roots (sourceEmbedding selection tagged index) root ∘ sourceEmbedding selection tagged)) = 0
  simp_rw [Function.update_comp_eq_of_injective roots (sourceEmbedding selection tagged).injective]
  have h := SelectedRootComponent.selectedCoefficient_centered security tagged.card (labels tagged layout) index
  convert h (roots ∘ sourceEmbedding selection tagged) using 1

theorem rootDensity_unselected_update {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (slot : Sigma (groupRootSlots selection tagged)) (hslot : slot ∉ Set.range (sourceEmbedding selection tagged))
    (roots : Sigma (groupRootSlots selection tagged) → CycleRootExpansion.Root security)
    (root : CycleRootExpansion.Root security) :
    rootDensity selection tagged layout (Function.update roots slot root) = rootDensity selection tagged layout roots := by
  unfold rootDensity
  rw [Function.update_comp_eq_of_forall_ne roots root]
  intro index hequal
  exact hslot ⟨index, hequal⟩

theorem inputJoint_centered (security : ℕ) {r s : ℕ}
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s)
    (role : Role r s) (word : (other : Role r s) → RoleInput security r s other) :
    (roleReference security r s role).expectation
      (fun control => RaisingPatternKernel.inputJoint security kernel (Function.update word role control)) = 0 := by
  cases role with
  | inl index =>
    have hword (control : ActualControls.Palette security) :
        RaisingPatternKernel.inputJoint security kernel (Function.update word (.inl index) control) =
          kernel.val (Function.update (fun i => word (.inl i)) index control) (fun i => word (.inr i)) := by
      unfold RaisingPatternKernel.inputJoint
      apply congrArg₂ kernel.val
      · funext other
        by_cases hequal : other = index
        · subst other
          simp
        · simp [hequal]
      · funext other
        simp
    simp_rw [hword]
    exact kernel.property.1 index _ _
  | inr index =>
    have hword (control : ActualControls.SafePalette security) :
        RaisingPatternKernel.inputJoint security kernel (Function.update word (.inr index) control) =
          kernel.val (fun i => word (.inl i)) (Function.update (fun i => word (.inr i)) index control) := by
      unfold RaisingPatternKernel.inputJoint
      apply congrArg₂ kernel.val
      · funext other
        simp
      · funext other
        by_cases hequal : other = index
        · subst other
          simp
        · simp [hequal]
    simp_rw [hword]
    exact kernel.property.2.1 index _ _

theorem jointInput_global {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s)
    (roots : Sigma (groupRootSlots selection tagged) → CycleRootExpansion.Root security)
    (controls : (group : ActiveGroup selection tagged) → ControlInput selection tagged group) :
    jointInput selection tagged layout kernel
      (GroupedSourceNorm.wordEquiv (groupRootSlots selection tagged) (ControlInput selection tagged) (roots, controls)) =
      rootDensity selection tagged layout roots * controlKernel selection tagged kernel controls := rfl

theorem jointInput_root_centered {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s)
    (roots : Sigma (groupRootSlots selection tagged) → CycleRootExpansion.Root security)
    (controls : (group : ActiveGroup selection tagged) → ControlInput selection tagged group)
    (index : Fin tagged.card) :
    (CycleRootExpansion.rootReference security).expectation (fun root =>
      jointInput selection tagged layout kernel
        (GroupedSourceNorm.wordEquiv (groupRootSlots selection tagged) (ControlInput selection tagged)
          (Function.update roots (sourceEmbedding selection tagged index) root, controls))) = 0 := by
  simp_rw [jointInput_global]
  unfold FiniteDist.expectation
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul, rootDensity_centered selection tagged layout index roots, zero_mul]

theorem controlKernel_centered {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security))
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s)
    (controls : (group : ActiveGroup selection tagged) → ControlInput selection tagged group)
    (role : Role r s) :
    (roleReference security r s role).expectation (fun control =>
      controlKernel selection tagged kernel (Function.update controls (.inl role) control)) = 0 := by
  have hequal (control : RoleInput security r s role) :
      (fun index => Function.update controls (.inl role) control (.inl index)) =
        Function.update (fun index => controls (.inl index)) role control := by
    funext index
    by_cases hequal : index = role
    · subst index
      simp
    · simp [hequal]
  unfold controlKernel
  simp_rw [hequal]
  exact inputJoint_centered security kernel role _

theorem jointInput_control_centered {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s)
    (roots : Sigma (groupRootSlots selection tagged) → CycleRootExpansion.Root security)
    (controls : (group : ActiveGroup selection tagged) → ControlInput selection tagged group)
    (role : Role r s) :
    (roleReference security r s role).expectation (fun control =>
      jointInput selection tagged layout kernel
        (GroupedSourceNorm.wordEquiv (groupRootSlots selection tagged) (ControlInput selection tagged)
          (roots, Function.update controls (.inl role) control))) = 0 := by
  simp_rw [jointInput_global]
  have h := controlKernel_centered selection tagged kernel controls role
  unfold FiniteDist.expectation at *
  calc
    _ = rootDensity selection tagged layout roots *
        ∑ control, (roleReference security r s role).weight control *
          controlKernel selection tagged kernel (Function.update controls (.inl role) control) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro control _
      ring
    _ = 0 := by rw [h, mul_zero]

end
end CurrentAFT.PairedRootCentering
