import CurrentAFT.PairedRootCentering
import CurrentAFT.DependentTensorFixedInput
import CurrentAFT.DependentTensorComposition

/-! # Control centering fixes the actual full joint source

Only selected public controls are centered. Root words remain joint, and
unselected blocks have an identity control map. Canonicality of the
original coefficient kernel supplies these exact fixed-point identities.
-/
namespace CurrentAFT.RootSelectedControlCenter
open AFT ActualBlockFock TaggedSelection PairedRootPlacement PairedRootInput
  ControlCoordinates GradedControlAlgebra CoefficientHilbert
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
local instance classicalSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} : DecidableEq (Sigma Slots) := Classical.decEq _
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount

section Generic
variable {RootData Control : Type*} [Fintype Control]

def centerControl (law : FiniteDist Control) :
    ((RootData × Control) → ℝ) →ₗ[ℝ] ((RootData × Control) → ℝ) where
  toFun score sample := score sample - law.expectation (fun control => score (sample.1, control))
  map_add' first second := by
    funext sample
    simp only [Pi.add_apply]
    rw [FiniteDist.expectation_add]
    ring
  map_smul' scalar score := by
    funext sample
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [FiniteDist.expectation_const_mul]
    ring

theorem centerControl_fixed (law : FiniteDist Control) (score : (RootData × Control) → ℝ)
    (hcentered : ∀ roots, law.expectation (fun control => score (roots, control)) = 0) :
    centerControl law score = score := by
  funext sample
  change score sample - law.expectation (fun control => score (sample.1, control)) = _
  rw [hcentered, sub_zero]

theorem centerControl_column (law : FiniteDist Control) [DecidableEq RootData] [DecidableEq Control]
    (point : RootData × Control) (sample : RootData × Control) :
    centerControl law (Pi.single point 1) sample =
      (if sample.1 = point.1 then (Pi.single point.2 (1 : ℝ) : Control → ℝ) sample.2 - law.weight point.2 else 0) := by
  classical
  rcases point with ⟨pointRoot, pointControl⟩
  rcases sample with ⟨sampleRoot, sampleControl⟩
  by_cases hroot : sampleRoot = pointRoot
  · subst sampleRoot
    simp [centerControl, FiniteDist.expectation, Pi.single_apply]
  · simp [centerControl, FiniteDist.expectation, hroot]

end Generic

abbrev Input {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (group : ActiveGroup selection tagged) :=
  (groupRootSlots selection tagged group → CycleRootExpansion.Root security) × ControlInput selection tagged group

def projector {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) :
    (group : ActiveGroup selection tagged) → (Input selection tagged group → ℝ) →ₗ[ℝ] (Input selection tagged group → ℝ)
  | .inl role => centerControl (RaisingPatternBudget.roleReference security r s role)
  | .inr _ => LinearMap.id

private theorem wordEquiv_update_control {Group Root : Type*} [Fintype Group] [DecidableEq Group] [Fintype Root]
    (RootSlots Controls : Group → Type*) [∀ group, Fintype (RootSlots group)] [∀ group, Fintype (Controls group)]
    (roots : Sigma RootSlots → Root) (controls : (group : Group) → Controls group)
    (group : Group) (control : Controls group) :
    GroupedSourceNorm.wordEquiv RootSlots Controls (roots, Function.update controls group control) =
      Function.update (GroupedSourceNorm.wordEquiv RootSlots Controls (roots, controls)) group
        ((fun slot => roots ⟨group, slot⟩), control) := by
  funext other
  by_cases hequal : other = group
  · subst other
    simp only [Function.update_self, GroupedSourceNorm.wordEquiv, Equiv.coe_fn_mk]
  · simp only [GroupedSourceNorm.wordEquiv, Equiv.coe_fn_mk, Function.update_of_ne hequal]

theorem projector_fixes_slice {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s)
    (word : GroupInput selection tagged) (group : ActiveGroup selection tagged) :
    projector selection tagged group (fun sample => jointInput selection tagged layout kernel (Function.update word group sample)) =
      fun sample => jointInput selection tagged layout kernel (Function.update word group sample) := by
  rcases group with role | kept
  · apply centerControl_fixed
    intro roots
    let baseWord : GroupInput selection tagged := Function.update word (.inl role) (roots, word (.inl role) |>.2)
    let global := (GroupedSourceNorm.wordEquiv (groupRootSlots selection tagged) (ControlInput selection tagged)).symm baseWord
    have h := PairedRootCentering.jointInput_control_centered selection tagged layout kernel global.1 global.2 role
    have hword (control : RaisingPatternBudget.RoleInput security r s role) :
        GroupedSourceNorm.wordEquiv (groupRootSlots selection tagged) (ControlInput selection tagged)
          (global.1, Function.update global.2 (.inl role) control) =
            Function.update word (.inl role) (roots, control) := by
      rw [wordEquiv_update_control]
      have hequal : GroupedSourceNorm.wordEquiv (groupRootSlots selection tagged) (ControlInput selection tagged) global = baseWord :=
        Equiv.apply_symm_apply _ baseWord
      have hroot : (fun slot => global.1 ⟨.inl role, slot⟩) = roots := by
        change (baseWord (.inl role)).1 = roots
        simp only [baseWord, Function.update_self]
      rw [hroot]
      change Function.update (GroupedSourceNorm.wordEquiv (groupRootSlots selection tagged) (ControlInput selection tagged) global)
        (.inl role) (roots, control) = _
      rw [hequal]
      simp only [baseWord, Function.update_idem]
    simpa only [hword] using h
  · rfl

theorem projected_jointInput {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s) :
    DependentTensorChannel.apply (projector selection tagged) (jointInput selection tagged layout kernel) =
      jointInput selection tagged layout kernel :=
  DependentTensorFixedInput.apply_eq_self _ _ (fun group word => projector_fixes_slice selection tagged layout kernel word group)

end
end CurrentAFT.RootSelectedControlCenter
