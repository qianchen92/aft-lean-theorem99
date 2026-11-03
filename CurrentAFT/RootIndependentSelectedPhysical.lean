import CurrentAFT.RootConditionalComponent
import CurrentAFT.CompleteRaisingEvaluation

/-! # The true independent-root conditional PGF is the normalized baseline

This identifies the empty root component of the actual selected experiment
with the previously constructed joint normalized coefficient response.
All original control references and the full joint canonical kernel remain
inside the finite source sum.
-/
namespace CurrentAFT.RootIndependentSelectedPhysical
open AFT AFT.RepresentedPolynomial ActualBlockFock TaggedSelection PairedRootPlacement
  PairedRootInput CycleRootExpansion ControlCoordinates ControlProduct GradedControlAlgebra
  LocalCoefficientFamily RaisingPatternBudget FinitePolynomialTensor
  DiffuseProfiles ProposalPrimary ActualControls CompleteRaisingEvaluation
  RootConditionalComponent
open scoped BigOperators Classical
noncomputable section
local instance baselineFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance baselineVertexDecidableEq (security : ℕ) : DecidableEq (Vertex security) :=
  instDecidableEqFin (Parameters.bodySize security)
local instance baselineSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
local instance baselineProdDecidableEq {Left Right : Type*} : DecidableEq (Left × Right) := Classical.decEq _
local instance baselineSubtypeDecidableEq {Index : Type*} {predicate : Index → Prop} : DecidableEq (Subtype predicate) := Classical.decEq _
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount primaryLaw bodyReference

abbrev Palette (security : ℕ) := ActualControls.Palette security

def normalizedRole (security order : ℕ) (horder : 1 ≤ order) (r s : ℕ) :
    (role : Role r s) → (RoleInput security r s role → ℝ) →ₗ[ℝ] Family security order
  | .inl _ => RaisingChannels.primaryLeading security order horder + RaisingChannels.primaryRaised security order horder
  | .inr _ => RaisingChannels.bodyLeading security order horder + RaisingChannels.bodyRaised security order horder

def normalizedPoint (security order : ℕ) (horder : 1 ≤ order) (r s : ℕ) :
    (role : Role r s) → RoleInput security r s role → Family security order
  | .inl _, source => NormalizedLocalPolynomial.independentNormalized security order
      (GlobalRaising.primaryAtom security source).val
  | .inr _, source => OrdinaryRaising.normalizedFamily security order horder
      (CompleteRaising.bodyAtom security source).val (CompleteRaising.bodyAtom security source).property

theorem normalizedRole_column (security order : ℕ) (horder : 1 ≤ order) (r s : ℕ)
    (role : Role r s) (source : RoleInput security r s role) :
    normalizedRole security order horder r s role (Pi.single source 1) =
      (roleReference security r s role).weight source • normalizedPoint security order horder r s role source := by
  cases role with
  | inl index =>
      change RaisingChannels.primaryLeading security order horder (Pi.single source 1) +
        RaisingChannels.primaryRaised security order horder (Pi.single source 1) = _
      rw [RaisingChannels.primaryLeading_single, RaisingChannels.primaryRaised_single, ← smul_add]
      congr 1
      unfold normalizedPoint GlobalRaising.primaryPoint
      change LocalRaisingLinear.primaryEmbeddingLinear security order horder (GlobalRaising.primaryAtom security source) +
        (NormalizedLocalPolynomial.independentNormalized security order (GlobalRaising.primaryAtom security source).val -
          LocalRaisingLinear.primaryEmbeddingLinear security order horder (GlobalRaising.primaryAtom security source)) = _
      abel
  | inr index =>
      change RaisingChannels.bodyLeading security order horder (Pi.single source 1) +
        RaisingChannels.bodyRaised security order horder (Pi.single source 1) = _
      rw [RaisingChannels.bodyLeading_single, RaisingChannels.bodyRaised_single, ← smul_add]
      exact congrArg (fun value : Family security order => (bodyReference security).weight source • value)
        (OrdinaryRaising.normalizedFamily_eq_leading_add security order horder _ _).symm

theorem normalized_synthesis (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (kernel : canonicalKernels (primaryLaw security) (bodyReference security) r s) :
    synthesis (normalizedRole security order horder r s) (RaisingPatternKernel.inputJoint security kernel) =
      normalizedJoint security order horder kernel := by
  unfold synthesis
  simp_rw [normalizedRole_column, Finset.prod_smul, smul_smul]
  rw [← (Equiv.prodPiEquivSumPi (fun _ : Fin r => Palette security)
    (fun _ : Fin s => SafePalette security)).sum_comp, Fintype.sum_prod_type]
  unfold normalizedJoint
  apply Finset.sum_congr rfl
  intro colors _
  apply Finset.sum_congr rfl
  intro centers _
  simp only [Fintype.prod_sum_type, roleReference, normalizedPoint, normalizedSlot,
    Equiv.prodPiEquivSumPi, Equiv.sumPiEquivProdPi, Equiv.coe_fn_symm_mk,
    Sum.elim_inl, Sum.elim_inr, RoleInput, RaisingPatternKernel.inputJoint]
  rw [mul_comm]

private theorem selectedCoefficient_zero (security : ℕ)
    (labels : CycleSelections.Selection (Parameters.bodySize security) 0) (word : Fin 0 → Root security) :
    selectedCoefficient security 0 labels word = 1 := by
  unfold selectedCoefficient CycleSelections.centeredRootDensity
  simp only [Fin.prod_univ_zero, FiniteDist.expectation_const]

theorem jointInput_empty {security r s : ℕ} (selection : Selection security r s)
    (layout : BlockIndex security ≃ Vertex security)
    (kernel : canonicalKernels (primaryLaw security) (bodyReference security) r s)
    (word : GroupInput selection ∅) :
    jointInput selection ∅ layout kernel word = controlKernel selection ∅ kernel (fun group => (word group).2) := by
  unfold jointInput
  have hzero (count : ℕ) (hcount : count = 0)
      (labels : CycleSelections.Selection (Parameters.bodySize security) count) (input : Fin count → Root security) :
      selectedCoefficient security count labels input = 1 := by
    subst count
    exact selectedCoefficient_zero security labels input
  rw [hzero _ Finset.card_empty, one_mul]

private def meanLinear {RootData Control : Type*} [Fintype RootData] (law : FiniteDist RootData) :
    ((RootData × Control) → ℝ) →ₗ[ℝ] (Control → ℝ) where
  toFun score control := law.expectation (fun root => score (root, control))
  map_add' first second := by funext control; exact FiniteDist.expectation_add _ _ _
  map_smul' scalar score := by funext control; exact FiniteDist.expectation_const_mul _ _ _

private theorem average_constant {RootData Control Value : Type*} [Fintype RootData] [CommRing Value] [Algebra ℝ Value]
    (law : FiniteDist RootData) (channel : (Control → ℝ) →ₗ[ℝ] Value) :
    RootPolynomialTensor.averagedChannel (Index := Unit) (fun _ => law) (fun _ _ => channel) () =
      channel.comp (meanLinear law) := by
  apply LinearMap.ext
  intro score
  have hmean : meanLinear law score = ∑ root, law.weight root • (fun control => score (root, control)) := by
    funext control
    simp only [meanLinear, LinearMap.coe_mk, AddHom.coe_mk, FiniteDist.expectation,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [RootPolynomialTensor.averagedChannel, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, RootPolynomialTensor.sliceLinear, LinearMap.coe_mk, AddHom.coe_mk]
  rw [hmean, map_sum]
  simp only [map_smul]


private instance emptyHitKeptIsEmpty {security r s : ℕ} (selection : Selection security r s) :
    IsEmpty (HitKept selection ∅) := ⟨fun index => Finset.notMem_empty index.val.val index.property⟩

private def normalizedActive {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order)
    (selection : Selection security r s) :
    (group : ActiveGroup selection ∅) → (ControlInput selection ∅ group → ℝ) →ₗ[ℝ] Family security order
  | .inl role => normalizedRole security order horder r s role
  | .inr index => isEmptyElim index

private theorem empty_channel_average {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : Selection security r s) :
    ActualRootGroupedChannel.channel order horder queue selection ∅ =
      RootPolynomialTensor.averagedChannel
        (RootTaggedPhysicalFactorization.rootReferenceByGroup selection ∅)
        (fun group _ => normalizedActive order horder selection group) := by
  funext group
  rcases group with (primary | ordinary) | kept
  · apply LinearMap.ext
    intro score
    have hflag : ActualRootGroupedChannel.primaryFlags selection ∅ primary = fun _ => false := by
      funext slot
      simp only [ActualRootGroupedChannel.primaryFlags, Finset.notMem_empty, decide_false]
    change RootPrimaryGroupedChannel.channel security order (ActualRootGroupedChannel.primaryFlags selection ∅ primary) score = _
    rw [hflag, RootPrimaryGroupedChannel.channel_zero,
      RootSelectedZeroTag.zeroChannel_eq_leading_add_raised security order horder]
    exact congrArg (fun map => map score)
      (average_constant (FiniteDist.independent (fun _ : Fin 2 => rootReference security))
        (normalizedRole security order horder r s (.inl primary))).symm
  · apply LinearMap.ext
    intro score
    have hflag : ActualRootGroupedChannel.ordinaryFlag selection ∅ ordinary = false := by
      simp only [ActualRootGroupedChannel.ordinaryFlag, Finset.notMem_empty, decide_false]
    change RootOrdinaryGroupedChannel.channel security order horder (ActualRootGroupedChannel.ordinaryFlag selection ∅ ordinary) score = _
    rw [hflag, RootOrdinaryGroupedChannel.channel_false,
      SelectedOrdinaryHybrid.independentChannel_eq_leading_add_raised]
    have hmean : SelectedOrdinaryMean.rootMean security (RootOrdinaryGroupedChannel.toRaw security score) =
        meanLinear (FiniteDist.independent (fun _ : Fin 1 => rootReference security)) score := by
      funext center
      exact (RootOrdinaryGroupedChannel.oneRoot_expectation security (fun roots => score (roots, center))).symm
    rw [hmean]
    exact congrArg (fun map => map score)
      (average_constant (FiniteDist.independent (fun _ : Fin 1 => rootReference security))
        (normalizedRole security order horder r s (.inr ordinary))).symm
  · exact isEmptyElim kept

private theorem normalizedActive_synthesis {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order)
    (selection : Selection security r s)
    (kernel : canonicalKernels (primaryLaw security) (bodyReference security) r s) :
    synthesis (normalizedActive order horder selection) (controlKernel selection ∅ kernel) =
      synthesis (normalizedRole security order horder r s) (RaisingPatternKernel.inputJoint security kernel) := by
  unfold synthesis controlKernel
  rw [← (Equiv.prodPiEquivSumPi (RoleInput security r s) (fun _ : HitKept selection ∅ => Unit)).sum_comp]
  simp only [Fintype.sum_prod_type, Fintype.prod_sum_type, ControlInput,
    Equiv.prodPiEquivSumPi, Equiv.sumPiEquivProdPi, Equiv.coe_fn_symm_mk,
    Sum.elim_inl, Sum.elim_inr, normalizedActive, Fintype.prod_empty, mul_one,
    Fintype.sum_unique]

theorem response_empty {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : Selection security r s) (layout : BlockIndex security ≃ Vertex security)
    (kernel : canonicalKernels (primaryLaw security) (bodyReference security) r s) :
    ActualRootResponse.response order horder queue selection ∅ layout kernel = normalizedJoint security order horder kernel := by
  rw [ActualRootResponse.response_apply, GroupedFamilyIdentity.response_eq]
  change synthesis (ActualRootGroupedChannel.channel order horder queue selection ∅)
    (jointInput selection ∅ layout kernel) = _
  rw [empty_channel_average, RootPolynomialTensor.synthesis_averaged]
  simp_rw [jointInput_empty]
  rw [← Finset.sum_smul]
  change (∑ roots, (FiniteDist.dependentIndependent
    (RootTaggedPhysicalFactorization.rootReferenceByGroup selection ∅)).weight roots) •
      synthesis (normalizedActive order horder selection) (controlKernel selection ∅ kernel) = _
  rw [FiniteDist.sum_one, one_smul, normalizedActive_synthesis, normalized_synthesis]

/-- True independent integration of all physical roots gives the same
baseline for every actual distinct placement selection. -/
theorem independent_conditional_polynomial {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order)
    (queue : ℤ) (selection : Selection security r s) (layout : BlockIndex security ≃ Vertex security)
    (kernel : canonicalKernels (primaryLaw security) (bodyReference security) r s) :
    TruncatedOutput.quotientMap order
      (expectationLinear (FiniteDist.independent (fun _ : Vertex security => rootReference security))
        (fun roots => TypedTaggedPhysical.conditionalPolynomial selection queue
          (fun block => (roots (layout block)).val) kernel.val)) =
      TruncatedOutput.quotientMap order (BackgroundPolynomialEvaluation.fixedQueueGenerating security queue) *
        BackgroundEvaluation.evaluation security order (normalizedJoint security order horder kernel) := by
  have h := RootConditionalComponent.response_physical_background order horder queue selection ∅ layout kernel
  rw [response_empty, Finset.map_empty] at h
  have hempty : actualComponent (Value := MvPolynomial (Palette security) ℝ) security ∅ =
      expectationLinear (FiniteDist.independent (fun _ : Vertex security => rootReference security)) := by
    unfold actualComponent
    exact componentResponse_empty (Value := MvPolynomial (Palette security) ℝ)
      (CycleRootExpansion.rootLaw security) (fun _ => rootReference security)
  rw [hempty] at h
  exact h.symm.trans (mul_comm _ _)

end
end CurrentAFT.RootIndependentSelectedPhysical
