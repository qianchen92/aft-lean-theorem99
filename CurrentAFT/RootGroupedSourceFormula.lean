import CurrentAFT.PairedRootCentering
import AFT.EmbeddedCompletion

/-! # Exact Fubini formula for the actual joint tagged-root source

The original canonical control kernel appears once. Every omitted root is
completed by its actual independent reference law; no root atom is divided.
-/
namespace CurrentAFT.RootGroupedSourceFormula
open AFT ActualBlockFock TaggedSelection PairedRootPlacement PairedRootInput
  PairedRootCentering GroupedSourceNorm CycleRootExpansion ControlCoordinates
  RaisingPatternBudget
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
local instance classicalSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} :
    DecidableEq (Sigma Slots) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount

section Generic
variable {Selected Pool Color Value : Type*} [Fintype Selected] [Fintype Pool] [Fintype Color]
  [AddCommGroup Value] [Module ℝ Value]

/-- Vector-valued weighted completion follows from the real finite law,
including all its zero atoms. -/
theorem weighted_completion_sum (embedding : Selected ↪ Pool) (law : Pool → FiniteDist Color)
    (score : (Selected → Color) → ℝ) (test : (Pool → Color) → Value) :
    (∑ word, ((FiniteDist.independent law).weight word * score (word ∘ embedding)) • test word) =
      ∑ selected, ((FiniteDist.independent (fun slot => law (embedding slot))).weight selected * score selected) •
        (∑ word, (FiniteDist.embeddingCompletion embedding law selected).weight word • test word) := by
  have hcoefficient (word : Pool → Color) :
      (FiniteDist.independent law).weight word * score (word ∘ embedding) =
        ∑ selected, ((FiniteDist.independent (fun slot => law (embedding slot))).weight selected *
          score selected) * (FiniteDist.embeddingCompletion embedding law selected).weight word := by
    have hh := FiniteDist.weighted_embedding_completion embedding law score
      (fun output => if output = word then 1 else 0)
    have hpoint (selected : Selected → Color) :
        (FiniteDist.embeddingCompletion embedding law selected).expectation
          (fun output => if output = word then 1 else 0) =
            (FiniteDist.embeddingCompletion embedding law selected).weight word := by
      simp only [FiniteDist.expectation, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
    simp only [hpoint] at hh
    unfold FiniteDist.expectation at hh
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hh
    exact hh.trans (Finset.sum_congr rfl (fun selected _ => by ring))
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro word _
  rw [← Finset.sum_smul, hcoefficient]

end Generic

variable {Value : Type*} [AddCommGroup Value] [Module ℝ Value]

def activeEmbedding {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ Vertex security) :
    Sigma (groupRootSlots selection tagged) ↪ Vertex security :=
  (rootEmbedding selection tagged).trans layout.toEmbedding

theorem rootDensity_restrict {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ Vertex security)
    (roots : Vertex security → Root security) :
    rootDensity selection tagged layout (roots ∘ activeEmbedding selection tagged layout) =
      selectedCoefficient security tagged.card (labels tagged layout) (roots ∘ labels tagged layout) := by
  unfold rootDensity
  congr 1
  funext index
  exact congrArg roots (labels_eq selection tagged layout index).symm

/-- The actual cycle component, with every unused physical root integrated
by its genuine conditional independent completion. -/
theorem actual_component_completion {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ Vertex security)
    (test : (Vertex security → Root security) → Value) :
    actualComponent security (tagged.map layout.toEmbedding) test =
      ∑ roots, ((FiniteDist.independent (fun _ : Sigma (groupRootSlots selection tagged) => rootReference security)).weight roots *
        rootDensity selection tagged layout roots) •
          expectationLinear
            (FiniteDist.embeddingCompletion (activeEmbedding selection tagged layout)
              (fun _ => rootReference security) roots) test := by
  rw [PairedRootInput.actual_component]
  simp_rw [← rootDensity_restrict selection tagged layout]
  exact weighted_completion_sum (activeEmbedding selection tagged layout)
    (fun _ => rootReference security) (rootDensity selection tagged layout) test

/-- Regrouping acts on the full vector-valued source sum, so arbitrary
dependencies of the root density and canonical control kernel are kept. -/
theorem joint_source_regroup {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ Vertex security)
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s)
    (test : GroupInput selection tagged → Value) :
    (∑ word, ((reference selection tagged).weight word * jointInput selection tagged layout kernel word) • test word) =
      ∑ roots, ((FiniteDist.independent (fun _ : Sigma (groupRootSlots selection tagged) => rootReference security)).weight roots *
        rootDensity selection tagged layout roots) •
          ∑ controls, ((FiniteDist.dependentIndependent (controlReference selection tagged)).weight controls *
            controlKernel selection tagged kernel controls) •
              test (wordEquiv (groupRootSlots selection tagged) (ControlInput selection tagged) (roots, controls)) := by
  rw [← (wordEquiv (groupRootSlots selection tagged) (ControlInput selection tagged)).sum_comp]
  simp only [Fintype.sum_prod_type, Finset.smul_sum, smul_smul, jointInput_global]
  apply Finset.sum_congr rfl
  intro roots _
  apply Finset.sum_congr rfl
  intro controls _
  congr 1
  simp only [reference, FiniteDist.dependentIndependent_weight, groupReference,
    FiniteDist.prod_weight, FiniteDist.independent, wordEquiv, Equiv.coe_fn_mk,
    Fintype.prod_sigma, Finset.prod_mul_distrib]
  ring

abbrev RoleWord (security r s : ℕ) := (role : Role r s) → RoleInput security r s role

/-- The dummy controls of hit unselected groups integrate to one, without
altering any of the selected primary or ordinary controls. -/
theorem control_source_eliminate_dummy {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security))
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s)
    (test : RoleWord security r s → Value) :
    (∑ controls, ((FiniteDist.dependentIndependent (controlReference selection tagged)).weight controls *
      controlKernel selection tagged kernel controls) • test (fun role => controls (.inl role))) =
      ∑ controls, ((FiniteDist.dependentIndependent (roleReference security r s)).weight controls *
        RaisingPatternKernel.inputJoint security kernel controls) • test controls := by
  rw [← (Equiv.prodPiEquivSumPi (RoleInput security r s)
    (fun _ : HitKept selection tagged => Unit)).sum_comp]
  simp only [Fintype.sum_prod_type, FiniteDist.dependentIndependent_weight,
    Fintype.prod_sum_type, controlReference, controlKernel, ControlInput,
    Equiv.prodPiEquivSumPi, Equiv.sumPiEquivProdPi, Equiv.coe_fn_symm_mk,
    Sum.elim_inl, Sum.elim_inr]
  simp [FiniteDist.uniform]

def controlWeightedTest {security r s : ℕ}
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s)
    (test : (Vertex security → Root security) → RoleWord security r s → Value)
    (roots : Vertex security → Root security) : Value :=
  ∑ controls, ((FiniteDist.dependentIndependent (roleReference security r s)).weight controls *
    RaisingPatternKernel.inputJoint security kernel controls) • test roots controls

def completedTest {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ Vertex security)
    (test : (Vertex security → Root security) → RoleWord security r s → Value)
    (word : GroupInput selection tagged) : Value :=
  expectationLinear
    (FiniteDist.embeddingCompletion (activeEmbedding selection tagged layout)
      (fun _ => rootReference security) (fun slot => (word slot.fst).1 slot.snd))
    (fun roots => test roots (fun role => (word (.inl role)).2))

/-- Literal cycle-component equals the one actual joint source `rho ⊗ kappa`,
with every inactive root completed independently. This is an exact identity
for arbitrary vector-valued physical tests, not a factorization premise. -/
theorem actual_component_joint_source {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ Vertex security)
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s)
    (test : (Vertex security → Root security) → RoleWord security r s → Value) :
    actualComponent security (tagged.map layout.toEmbedding) (controlWeightedTest kernel test) =
      ∑ word, ((reference selection tagged).weight word * jointInput selection tagged layout kernel word) •
        completedTest selection tagged layout test word := by
  rw [actual_component_completion selection tagged layout,
    joint_source_regroup selection tagged layout kernel]
  apply Finset.sum_congr rfl
  intro roots _
  congr 1
  simp only [completedTest, wordEquiv, Equiv.coe_fn_mk]
  change expectationLinear
    (FiniteDist.embeddingCompletion (activeEmbedding selection tagged layout)
      (fun _ => rootReference security) roots) (controlWeightedTest kernel test) =
    ∑ controls, ((FiniteDist.dependentIndependent (controlReference selection tagged)).weight controls *
      controlKernel selection tagged kernel controls) •
      expectationLinear
        (FiniteDist.embeddingCompletion (activeEmbedding selection tagged layout)
          (fun _ => rootReference security) roots) (fun full => test full (fun role => controls (.inl role)))
  rw [control_source_eliminate_dummy selection tagged kernel
    (fun controls => expectationLinear
      (FiniteDist.embeddingCompletion (activeEmbedding selection tagged layout)
        (fun _ => rootReference security) roots) (fun full => test full controls))]
  simp only [expectationLinear, controlWeightedTest, LinearMap.coe_mk, AddHom.coe_mk,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro controls _
  apply Finset.sum_congr rfl
  intro full _
  congr 1
  ring

end
end CurrentAFT.RootGroupedSourceFormula
