import CurrentAFT.RootPrimaryGroupedChannel
import CurrentAFT.RootOrdinaryGroupedChannel
import CurrentAFT.RootUnselectedGrouped
import CurrentAFT.PairedRootProjection
import CurrentAFT.PairedRootDegrees

/-! # All actual normalized root/control channels at a fixed placement -/
namespace CurrentAFT.ActualRootGroupedChannel
open AFT ActualBlockFock TaggedSelection PairedRootPlacement PairedRootInput
  GradedControlAlgebra ControlCoordinates LocalCoefficientFamily GradedInverse
open Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
local instance classicalSigmaDecidableEq {Index : Type*} {Slots : Index → Type*} : DecidableEq (Sigma Slots) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount

abbrev Input {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (group : ActiveGroup selection tagged) :=
  (groupRootSlots selection tagged group → CycleRootExpansion.Root security) × ControlInput selection tagged group

def primaryFlags {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (index : Fin r) (slot : Fin 2) : Bool :=
  decide (rootEmbedding selection tagged ⟨.inl (.inl index), slot⟩ ∈ tagged)

def ordinaryFlag {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (index : Fin s) : Bool :=
  decide (rootEmbedding selection tagged ⟨.inl (.inr index), (0 : Fin 1)⟩ ∈ tagged)

def channel {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : Selection security r s) (tagged : Finset (BlockIndex security)) :
    (group : ActiveGroup selection tagged) → (Input selection tagged group → ℝ) →ₗ[ℝ] Family security order
  | .inl (.inl index) => RootPrimaryGroupedChannel.channel security order (primaryFlags selection tagged index)
  | .inl (.inr index) => RootOrdinaryGroupedChannel.channel security order horder (ordinaryFlag selection tagged index)
  | .inr index => RootUnselectedGrouped.channel security order horder queue index.val.val

def cost {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) : ActiveGroup selection tagged → ℝ
  | .inl (.inl index) => RootPrimaryGroupedChannel.cost security (primaryFlags selection tagged index)
  | .inl (.inr index) => RootOrdinaryGroupedChannel.cost security (ordinaryFlag selection tagged index)
  | .inr _ => RootUnselectedBlockChannel.channelConstant / (Parameters.base security : ℝ) ^ 94

theorem cost_nonneg {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (group : ActiveGroup selection tagged) :
    0 ≤ cost selection tagged group := by
  rcases group with (primary | ordinary) | unselected
  · exact RootPrimaryGroupedChannel.cost_nonneg security _
  · change 0 ≤ RootOrdinaryGroupedChannel.cost security (ordinaryFlag selection tagged ordinary)
    unfold RootOrdinaryGroupedChannel.cost
    split_ifs
    · positivity
    · exact mul_nonneg (by norm_num) (RaisingPatternBudget.bodyFactor_pos security).le
  · exact div_nonneg RootUnselectedBlockChannel.channelConstant_nonneg (by positivity)

theorem channel_norm_eventually (order : ℕ) (horder : 1 ≤ order) :
    ∀ᶠ security : ℕ in atTop,
      2 * LocalRaisingBounds.positiveConstant ≤ (Parameters.base security : ℝ) →
      LocalRaisingBounds.raisingConstant ≤ (Parameters.base security : ℝ)^38 →
      ∀ r s, ∀ selection : Selection security r s, ∀ tagged : Finset (BlockIndex security),
      ∀ queue : ℤ, ∀ group : ActiveGroup selection tagged, ∀ score : Input selection tagged group → ℝ,
      LocalRaisingBounds.coefficientNorm security order (channel order horder queue selection tagged group score) ≤
        cost selection tagged group * Real.sqrt
          ((GroupedSourceNorm.groupReference (groupRootSlots selection tagged) (ControlInput selection tagged)
            (CycleRootExpansion.rootReference security) (controlReference selection tagged) group).l2Sq score) := by
  filter_upwards [RootUnselectedGrouped.channel_norm_eventually order horder] with security hunselected
  intro hlarge hsmall r s selection tagged queue group score
  rcases group with (primary | ordinary) | unselected
  · exact RootPrimaryGroupedChannel.channel_norm_cost security order horder hlarge hsmall _ score
  · exact RootOrdinaryGroupedChannel.channel_norm security order horder _ score
  · exact hunselected queue unselected.val.val score

theorem channel_degree {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : Selection security r s) (tagged : Finset (BlockIndex security))
    (group : ActiveGroup selection tagged) (score : Input selection tagged group → ℝ) :
    VanishesBelow (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) order
      (PairedRootDegrees.minimumDegree selection tagged group) (channel order horder queue selection tagged group score) := by
  rcases group with (primary | ordinary) | unselected
  · have hbound := PairedRootDegrees.primary_minimumDegree_le_two selection tagged primary
    have hpositive : 1 ≤ PairedRootDegrees.minimumDegree selection tagged (.inl (.inl primary)) := le_max_left _ _
    by_cases hone : PairedRootDegrees.minimumDegree selection tagged (.inl (.inl primary)) = 1
    · rw [hone]
      exact RootPrimaryGroupedChannel.channel_vanishesBelow_one security order _ score
    · have htwo : PairedRootDegrees.minimumDegree selection tagged (.inl (.inl primary)) = 2 := by omega
      rw [htwo]
      apply RootPrimaryGroupedChannel.channel_vanishesBelow_two security order horder _ _ score
      apply decide_eq_true
      exact PairedRootDegrees.primary_minimumDegree_two_requires_attachment selection tagged primary htwo
  · rw [PairedRootDegrees.ordinary_minimumDegree]
    exact RootOrdinaryGroupedChannel.channel_vanishesBelow_one security order horder _ score
  · rw [PairedRootDegrees.kept_minimumDegree]
    exact RootUnselectedGrouped.channel_degree security order horder queue unselected.val.val score

end
end CurrentAFT.ActualRootGroupedChannel
