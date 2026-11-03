import CurrentAFT.ActualRootDefect
import CurrentAFT.RootGroupCostBudget
import CurrentAFT.RootSubsetNormSum

/-! # Stability of the complete root defect under actual control selection -/
namespace CurrentAFT.ActualRootDefectNorm
open AFT ActualBlockFock TaggedSelection PairedRootPlacement ControlCoordinates
  ControlNorm GradedControlAlgebra LocalCoefficientFamily LocalRaisingBounds
  RootActivityBudget GradedInverseNorm
open Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
local instance finDecEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance sumDecEq {First Second : Type*} : DecidableEq (First ⊕ Second) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount

def degreeConstant (order : ℕ) : ℝ :=
  (Fintype.card (TruncatedArity order) : ℝ) ^ (2 * order) *
    (((2 * (order + 1) : ℕ) : ℝ) ^ order) * 2 ^ order

def activityConstant (order : ℕ) : ℝ := commonConstant * (((2 * order : ℕ) : ℝ) + 131074)

def stabilityConstant (order : ℕ) : ℝ :=
  degreeConstant order * ((order + 1 : ℕ) : ℝ) * activityConstant order ^ order

theorem degreeConstant_nonneg (order : ℕ) : 0 ≤ degreeConstant order := by
  unfold degreeConstant
  positivity

theorem activityConstant_one (order : ℕ) : 1 ≤ activityConstant order :=
  one_le_mul_of_one_le_of_one_le commonConstant_one (by have := Nat.cast_nonneg (α := ℝ) (2 * order); linarith)

theorem stabilityConstant_nonneg (order : ℕ) : 0 ≤ stabilityConstant order := by
  exact mul_nonneg (mul_nonneg (degreeConstant_nonneg order) (Nat.cast_nonneg _))
    (pow_nonneg (zero_le_one.trans (activityConstant_one order)) _)

theorem response_norm_activity_eventually (order : ℕ) (horder : 1 ≤ order) :
    ∀ᶠ security : ℕ in atTop,
      2 * positiveConstant ≤ (Parameters.base security : ℝ) →
      raisingConstant ≤ (Parameters.base security : ℝ)^38 →
      ∀ r s, r + s ≤ order → ∀ selection : Selection security r s,
      ∀ tagged : Finset (BlockIndex security), 1 ≤ tagged.card → tagged.card ≤ order →
      2 * tagged.card ≤ Parameters.bodySize security →
      ∀ layout : BlockIndex security ≃ CycleRootExpansion.Vertex security, ∀ queue : ℤ,
      ∀ kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s,
      coefficientNorm security order (ActualRootResponse.response order horder queue selection tagged layout kernel) ≤
        degreeConstant order *
          (gradeWeight (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security) r s *
            blockL2 (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) kernel.val) *
          ∏ vertex ∈ tagged, activity selection commonConstant vertex * CycleSelections.currentRootTag security := by
  filter_upwards [ActualRootResponse.response_norm_eventually order horder] with security hresponse
  intro hlarge hsmall r s hdegree selection tagged hpositive hcard hbody layout queue kernel
  have hp := (RaisingPatternBudget.primaryFactor_pos security).le
  have hb := (RaisingPatternBudget.bodyFactor_pos security).le
  have ha := activity_nonneg selection commonConstant (zero_le_one.trans commonConstant_one)
  have ht : 0 ≤ CycleSelections.currentRootTag security := by rw [CycleSelections.currentRootTag_eq]; positivity
  have hc : 1 ≤ (Fintype.card (TruncatedArity order) : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr (show Nonempty (TruncatedArity order) from ⟨zeroArity order⟩)
  have hg : Fintype.card (ActiveGroup selection tagged) ≤ 2 * order := by
    have hgroup : Fintype.card (ActiveGroup selection tagged) ≤ r + s + tagged.card := by
      convert activeGroup_card_le selection tagged using 1
      congr 3
      exact Subsingleton.elim _ _
    omega
  have hpattern := pow_le_pow_right₀ hc hg
  have hroot : (((2 * (tagged.card + 1) : ℕ) : ℝ) ^ tagged.card) ≤
      (((2 * (order + 1) : ℕ) : ℝ) ^ order) := by
    have hbase : (((2 * (tagged.card + 1) : ℕ) : ℝ)) ≤ (((2 * (order + 1) : ℕ) : ℝ)) := by
      exact_mod_cast (show 2 * (tagged.card + 1) ≤ 2 * (order + 1) by omega)
    apply (pow_le_pow_left₀ (Nat.cast_nonneg _) hbase tagged.card).trans
    exact pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ 2 * (order + 1) by omega)) hcard
  have htwo := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hdegree
  have hcost := RootGroupCostBudget.product_cost_le selection tagged commonConstant le_rfl
  have hweight := gradeWeight_nonneg _ _ hp hb r s
  have hl2 := blockL2_nonneg (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) kernel.val
  have hprod : 0 ≤ ∏ vertex ∈ tagged, activity selection commonConstant vertex :=
    Finset.prod_nonneg (fun vertex _ => ha vertex)
  have hcost0 : 0 ≤ ∏ group, ActualRootGroupedChannel.cost selection tagged group :=
    Finset.prod_nonneg (fun group _ => ActualRootGroupedChannel.cost_nonneg selection tagged group)
  apply (hresponse hlarge hsmall r s selection tagged layout queue kernel hpositive hbody).trans
  calc
    _ ≤ (Fintype.card (TruncatedArity order) : ℝ) ^ (2 * order) *
        (((2 : ℝ) ^ order * gradeWeight (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security) r s *
          ∏ vertex ∈ tagged, activity selection commonConstant vertex) *
        ((((2 * (order + 1) : ℕ) : ℝ) ^ order) * CycleSelections.currentRootTag security ^ tagged.card *
          blockL2 (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) kernel.val)) := by
      apply mul_le_mul hpattern _ (by positivity) (by positivity)
      apply mul_le_mul _ (by gcongr) (by positivity) (by positivity)
      exact hcost.trans (by gcongr)
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const]
      unfold degreeConstant
      ring

theorem selectedDefect_norm_eventually (order : ℕ) (horder : 1 ≤ order) :
    ∀ᶠ security : ℕ in atTop,
      2 * positiveConstant ≤ (Parameters.base security : ℝ) →
      raisingConstant ≤ (Parameters.base security : ℝ)^38 →
      2 * order ≤ Parameters.bodySize security →
      ∀ r s, r + s ≤ order → ∀ selection : Selection security r s,
      ∀ layout : BlockIndex security ≃ CycleRootExpansion.Vertex security, ∀ queue : ℤ,
      ∀ kernel : canonicalKernels (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) r s,
      coefficientNorm security order (ActualRootDefect.selectedDefect order horder queue selection layout kernel) ≤
        (stabilityConstant order / (Parameters.base security : ℝ)^26) *
          (gradeWeight (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security) r s *
            blockL2 (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) kernel.val) := by
  filter_upwards [response_norm_activity_eventually order horder] with security hresponse
  intro hlarge hsmall hbody r s hdegree selection layout queue kernel
  let inputNorm := gradeWeight (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security) r s *
    blockL2 (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) kernel.val
  let vertexActivity := fun vertex => activity selection commonConstant vertex * CycleSelections.currentRootTag security
  have hinput : 0 ≤ inputNorm := mul_nonneg
    (gradeWeight_nonneg _ _ (RaisingPatternBudget.primaryFactor_pos security).le
      (RaisingPatternBudget.bodyFactor_pos security).le r s) (blockL2_nonneg _ _ _)
  have ht : 0 ≤ CycleSelections.currentRootTag security := by rw [CycleSelections.currentRootTag_eq]; positivity
  have ha : ∀ vertex, 0 ≤ vertexActivity vertex := fun vertex =>
    mul_nonneg (activity_nonneg selection commonConstant (zero_le_one.trans commonConstant_one) vertex) ht
  have hbase : (1 : ℝ) ≤ Parameters.base security := by
    exact_mod_cast (show 1 ≤ Parameters.base security from (by have := Parameters.base_ge_two security; omega))
  have hsum : (∑ vertex, vertexActivity vertex) ≤ activityConstant order / (Parameters.base security : ℝ)^13 := by
    dsimp only [vertexActivity]
    rw [← Finset.sum_mul]
    apply (sum_activity_tag_le selection commonConstant (zero_le_one.trans commonConstant_one)).trans
    unfold activityConstant
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans commonConstant_one)
    gcongr
    exact_mod_cast (show 2 * r + s ≤ 2 * order by omega)
  have hsubsets := RootSubsetNormSum.subset_sum_decay Finset.univ vertexActivity (fun vertex _ => ha vertex)
    (Parameters.base security : ℝ) (activityConstant order) hbase (activityConstant_one order) hsum order
  have hpowerset : (Finset.univ : Finset (BlockIndex security)).powerset = Finset.univ := by ext; simp
  rw [hpowerset] at hsubsets
  rw [ActualRootDefect.selectedDefect_eq_small]
  simp only [LinearMap.sum_apply]
  apply (familyNorm_sum_le _ _ order _ _ (RaisingPatternBudget.primaryFactor_pos security).le
    (RaisingPatternBudget.bodyFactor_pos security).le _ _).trans
  calc
    _ ≤ ∑ tagged ∈ (Finset.univ : Finset (Finset (BlockIndex security))).filter
        (fun tagged => 2 ≤ tagged.card ∧ tagged.card ≤ order),
        degreeConstant order * inputNorm * ∏ vertex ∈ tagged, vertexActivity vertex := by
      apply Finset.sum_le_sum
      intro tagged htagged
      have hh := (Finset.mem_filter.mp htagged).2
      exact hresponse hlarge hsmall r s hdegree selection tagged (by omega) hh.2 (by omega) layout queue kernel
    _ = degreeConstant order * inputNorm *
        ∑ tagged ∈ (Finset.univ : Finset (Finset (BlockIndex security))).filter
          (fun tagged => 2 ≤ tagged.card ∧ tagged.card ≤ order), ∏ vertex ∈ tagged, vertexActivity vertex :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ degreeConstant order * inputNorm *
        (((order + 1 : ℕ) : ℝ) * activityConstant order ^ order / (Parameters.base security : ℝ)^26) :=
      mul_le_mul_of_nonneg_left hsubsets (mul_nonneg (degreeConstant_nonneg order) hinput)
    _ = _ := by unfold stabilityConstant; ring

end
end CurrentAFT.ActualRootDefectNorm
