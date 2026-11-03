import CurrentAFT.ActualRootGroupedChannel
import CurrentAFT.GroupedFamilyComposition

/-! # Actual finite root-subset response on canonical control data

The source is the real selected coefficient of the permuted closed cycle.
The local factors are the actual normalized primary, ordinary, and omitted
block channels. Large root subsets vanish as canonical coefficient data.
-/
namespace CurrentAFT.ActualRootResponse
open AFT ActualBlockFock TaggedSelection PairedRootPlacement PairedRootInput
  GradedControlAlgebra ControlCoordinates LocalCoefficientFamily GradedInverse ControlNorm
open Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
local instance classicalSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} : DecidableEq (Sigma Slots) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount

def response {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security) :
    canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s →ₗ[ℝ]
      Family security order :=
  (GroupedFamilyComposition.responseLinear (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security)
    order (ActualRootGroupedChannel.channel order horder queue selection tagged)).comp
      (jointInputLinear selection tagged layout)

theorem response_apply {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s) :
    response order horder queue selection tagged layout kernel =
      GroupedFamilyTensor.response (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) order
        (ActualRootGroupedChannel.channel order horder queue selection tagged) (jointInput selection tagged layout kernel) := rfl

theorem response_degree {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security)
    (kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s) :
    VanishesBelow (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) order
      (∑ group, PairedRootDegrees.minimumDegree selection tagged group)
      (response order horder queue selection tagged layout kernel) :=
  GroupedFamilyIdentity.response_vanishes _ _ order
    (ActualRootGroupedChannel.channel order horder queue selection tagged) _
    (ActualRootGroupedChannel.channel_degree order horder queue selection tagged) _

theorem response_zero_of_order_lt_card {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (layout : BlockIndex security ≃ CycleRootExpansion.Vertex security) (hlarge : order < tagged.card) :
    response order horder queue selection tagged layout = 0 := by
  apply LinearMap.ext
  intro kernel
  funext arity
  have hcount := PairedRootDegrees.tags_le_degree selection tagged
  have harity := arity.property
  exact response_degree order horder queue selection tagged layout kernel arity (by omega)

/-- The true local Hilbert bounds are tensored against the true joint
root/control density; only finite degree-pattern counting appears. -/
theorem response_norm_eventually (order : ℕ) (horder : 1 ≤ order) :
    ∀ᶠ security : ℕ in atTop,
      2 * LocalRaisingBounds.positiveConstant ≤ (Parameters.base security : ℝ) →
      LocalRaisingBounds.raisingConstant ≤ (Parameters.base security : ℝ)^38 →
      ∀ r s, ∀ selection : Selection security r s, ∀ tagged : Finset (BlockIndex security),
      ∀ layout : BlockIndex security ≃ CycleRootExpansion.Vertex security, ∀ queue : ℤ,
      ∀ kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s,
      1 ≤ tagged.card → 2 * tagged.card ≤ Parameters.bodySize security →
      LocalRaisingBounds.coefficientNorm security order (response order horder queue selection tagged layout kernel) ≤
        (Fintype.card (TruncatedArity order) : ℝ) ^ Fintype.card (ActiveGroup selection tagged) *
          ((∏ group, ActualRootGroupedChannel.cost selection tagged group) *
            ((((2 * (tagged.card + 1) : ℕ) : ℝ)^tagged.card) *
              CycleSelections.currentRootTag security ^ tagged.card *
              blockL2 (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) kernel.val)) := by
  filter_upwards [ActualRootGroupedChannel.channel_norm_eventually order horder] with security hchannels
  intro hlarge hsmall r s selection tagged layout queue kernel hpositive hbody
  have h := GroupedFamilyTensor.response_norm (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security)
    order (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security)
    (RaisingPatternBudget.primaryFactor_pos security) (RaisingPatternBudget.bodyFactor_pos security)
    (GroupedSourceNorm.groupReference (groupRootSlots selection tagged) (ControlInput selection tagged)
      (CycleRootExpansion.rootReference security) (controlReference selection tagged))
    (ActualRootGroupedChannel.channel order horder queue selection tagged)
    (ActualRootGroupedChannel.cost selection tagged) (ActualRootGroupedChannel.cost_nonneg selection tagged)
    (hchannels hlarge hsmall r s selection tagged queue) (jointInput selection tagged layout kernel)
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Nat.cast_nonneg _) _)
  apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun group _ => ActualRootGroupedChannel.cost_nonneg selection tagged group)
  exact jointInput_norm selection tagged layout kernel hpositive hbody

end
end CurrentAFT.ActualRootResponse
