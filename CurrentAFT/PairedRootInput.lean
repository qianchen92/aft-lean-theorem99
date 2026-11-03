import CurrentAFT.PairedRootPlacement
import CurrentAFT.GroupedSourceNorm
import CurrentAFT.RaisingPatternKernel
import CurrentAFT.SelectedRootComponent

/-! # The actual joint root coefficient and the one original control kernel

All roots of a selected primary group remain together with its single
control input. Untagged roots and dummy controls integrate out isometrically.
-/
namespace CurrentAFT.PairedRootInput
open AFT ActualBlockFock TaggedSelection PairedRootPlacement RaisingPatternBudget
  GradedControlAlgebra ControlNorm ControlCoordinates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
local instance classicalSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} : DecidableEq (Sigma Slots) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount

abbrev ControlInput {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) : ActiveGroup selection tagged → Type :=
  Sum.elim (RoleInput security r s) (fun _ => Unit)

instance controlInputFintype {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (index : ActiveGroup selection tagged) :
    Fintype (ControlInput selection tagged index) := by
  cases index with
  | inl index => exact roleInputFintype security r s index
  | inr _ => exact inferInstanceAs (Fintype Unit)

def controlReference {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) :
    (index : ActiveGroup selection tagged) → FiniteDist (ControlInput selection tagged index)
  | .inl index => roleReference security r s index
  | .inr _ => FiniteDist.uniform Unit

def controlKernel {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security))
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s)
    (word : (index : ActiveGroup selection tagged) → ControlInput selection tagged index) : ℝ :=
  RaisingPatternKernel.inputJoint security kernel (fun index => word (.inl index))

theorem controlKernel_energy {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security))
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s) :
    (FiniteDist.dependentIndependent (controlReference selection tagged)).l2Sq
      (controlKernel selection tagged kernel) =
      blockEnergy (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) kernel.val := by
  rw [← RaisingPatternKernel.inputJoint_energy security kernel]
  unfold FiniteDist.l2Sq FiniteDist.expectation
  rw [← (Equiv.prodPiEquivSumPi (RoleInput security r s)
    (fun _ : HitKept selection tagged => Unit)).sum_comp]
  simp only [Fintype.sum_prod_type, FiniteDist.dependentIndependent_weight,
    Fintype.prod_sum_type, controlReference, controlKernel, ControlInput,
    Equiv.prodPiEquivSumPi, Equiv.sumPiEquivProdPi, Equiv.coe_fn_symm_mk,
    Sum.elim_inl, Sum.elim_inr]
  simp [FiniteDist.uniform]

def labels {security : ℕ}
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security) :
    CycleSelections.Selection (Parameters.bodySize security) tagged.card :=
  (tagged.equivFin.symm.toEmbedding.trans (Function.Embedding.subtype _)).trans layout.toEmbedding

def sourceEmbedding {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) : Fin tagged.card ↪ Sigma (groupRootSlots selection tagged) :=
  tagged.equivFin.symm.toEmbedding.trans (tagEmbedding selection tagged)

theorem labels_range {security : ℕ} (tagged : Finset (BlockIndex security))
    (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security) :
    Finset.univ.map (labels tagged layout) = tagged.map layout.toEmbedding := by
  simp only [labels, ← Finset.map_map, Finset.map_univ_equiv]
  congr 1
  ext index
  simp

theorem actual_component {Value : Type*} [AddCommGroup Value] [Module ℝ Value]
    {security : ℕ} (tagged : Finset (BlockIndex security))
    (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (test : (CycleRootExpansion.Vertex security → CycleRootExpansion.Root security) → Value) :
    CycleRootExpansion.actualComponent security (tagged.map layout.toEmbedding) test =
      ∑ word, ((FiniteDist.independent (fun _ : CycleRootExpansion.Vertex security =>
          CycleRootExpansion.rootReference security)).weight word *
        CycleRootExpansion.selectedCoefficient security tagged.card (labels tagged layout)
          (word ∘ labels tagged layout)) • test word := by
  rw [← labels_range tagged layout]
  have h := SelectedRootComponent.actualComponent_eq security tagged.card (labels tagged layout) test
  convert h using 1
  congr 3
  exact Subsingleton.elim _ _

theorem labels_eq {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (index : Fin tagged.card) :
    labels tagged layout index =
      layout (rootEmbedding selection tagged (sourceEmbedding selection tagged index)) := by
  simp only [labels, sourceEmbedding, Function.Embedding.trans_apply, Equiv.toEmbedding_apply, tag_image]
  rfl

abbrev GroupInput {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) :=
  GroupedSourceNorm.GroupWord (Root := CycleRootExpansion.Root security)
    (groupRootSlots selection tagged) (ControlInput selection tagged)

def reference {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) :=
  FiniteDist.dependentIndependent
    (GroupedSourceNorm.groupReference (groupRootSlots selection tagged) (ControlInput selection tagged)
      (CycleRootExpansion.rootReference security) (controlReference selection tagged))

def jointInput {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s)
    (word : GroupInput selection tagged) : ℝ :=
  CycleRootExpansion.selectedCoefficient security tagged.card (labels tagged layout)
    (fun index => (word (sourceEmbedding selection tagged index).fst).1
      (sourceEmbedding selection tagged index).snd) *
    controlKernel selection tagged kernel (fun index => (word index).2)

def jointInputLinear {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security) :
    canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s →ₗ[ℝ]
      (GroupInput selection tagged → ℝ) where
  toFun := jointInput selection tagged layout
  map_add' first second := by
    funext word
    simp only [jointInput, controlKernel, RaisingPatternKernel.inputJoint,
      Submodule.coe_add, Pi.add_apply, mul_add]
  map_smul' scalar kernel := by
    funext word
    simp only [jointInput, controlKernel, RaisingPatternKernel.inputJoint,
      Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- This is the full joint input energy, with exactly one copy of the
original canonical control energy even if a group contains two tags. -/
theorem jointInput_energy {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s) :
    (reference selection tagged).l2Sq (jointInput selection tagged layout kernel) =
      (FiniteDist.independent (fun _ : Fin tagged.card => CycleRootExpansion.rootReference security)).l2Sq
        (CycleRootExpansion.selectedCoefficient security tagged.card (labels tagged layout)) *
      blockEnergy (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) kernel.val := by
  unfold reference jointInput
  rw [GroupedSourceNorm.embedded_product_input_energy, controlKernel_energy]

theorem jointInput_norm {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s)
    (hpositive : 1 ≤ tagged.card) (hbody : 2 * tagged.card ≤ Parameters.bodySize security) :
    Real.sqrt ((reference selection tagged).l2Sq (jointInput selection tagged layout kernel)) ≤
      (((2 * (tagged.card + 1) : ℕ) : ℝ) ^ tagged.card) *
        CycleSelections.currentRootTag security ^ tagged.card *
        blockL2 (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) kernel.val := by
  rw [jointInput_energy, Real.sqrt_mul (FiniteDist.l2Sq_nonneg _ _)]
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  have hroot := CycleRootExpansion.selectedCoefficient_norm security tagged.card hpositive hbody
    (labels tagged layout)
  convert hroot using 1
  congr 3 <;> exact Subsingleton.elim _ _

end
end CurrentAFT.PairedRootInput
