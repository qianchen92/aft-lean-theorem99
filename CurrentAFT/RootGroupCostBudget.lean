import CurrentAFT.RootActivityBudget

/-! # The actual grouped channel cost is a product of vertex activities -/
namespace CurrentAFT.RootGroupCostBudget
open AFT ActualBlockFock TaggedSelection PairedRootPlacement RootActivityBudget BackgroundRates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance finDecEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance sumDecEq {First Second : Type*} : DecidableEq (First ⊕ Second) := Classical.decEq _
local instance sigmaDecEq {Index : Type*} {Fiber : Index → Type*} : DecidableEq (Sigma Fiber) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount

def taggedActivity {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (constant : ℝ) (vertex : BlockIndex security) : ℝ :=
  if vertex ∈ tagged then activity selection constant vertex else 1

def leadingCost {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) : ActiveGroup selection tagged → ℝ
  | .inl (.inl _) => 2 * primaryFactor security
  | .inl (.inr _) => 2 * bodyFactor security
  | .inr _ => 1

theorem primary_cost_activity (security : ℕ) (constant : ℝ) (hconstant : commonConstant ≤ constant)
    (flags : Fin 2 → Bool) :
    RootPrimaryGroupedChannel.cost security flags ≤ (2 * primaryFactor security) *
      ∏ slot : Fin 2, if flags slot then selectedActivity security constant else 1 := by
  have hone := selectedActivity_one security constant (commonConstant_one.trans hconstant)
  have hprimary := (RaisingPatternBudget.primaryFactor_pos security).le
  have hrelative := primary_tag_cost_relative security constant (commonConstant_primary.trans hconstant)
  have hnonneg : 0 ≤ selectedActivity security constant := by linarith
  have hscaled : primaryFactor security * selectedActivity security constant ≤
      primaryFactor security * (selectedActivity security constant * selectedActivity security constant) :=
    mul_le_mul_of_nonneg_left (by nlinarith : selectedActivity security constant ≤
      selectedActivity security constant * selectedActivity security constant) hprimary
  rw [Fin.prod_univ_two]
  cases hfirst : flags 0 <;> cases hsecond : flags 1 <;>
    simp only [RootPrimaryGroupedChannel.cost, hfirst, hsecond, Bool.or_false,
      Bool.or_true, Bool.false_eq_true, if_false, if_true, mul_one, one_mul]
  all_goals nlinarith [mul_nonneg hprimary hnonneg,
    mul_nonneg hprimary (mul_nonneg hnonneg hnonneg)]

theorem ordinary_cost_activity (security : ℕ) (constant : ℝ) (hconstant : commonConstant ≤ constant)
    (flag : Bool) :
    RootOrdinaryGroupedChannel.cost security flag ≤ (2 * bodyFactor security) *
      (if flag then selectedActivity security constant else 1) := by
  have hrelative := ordinary_tag_cost_relative security constant (commonConstant_ordinary.trans hconstant)
  have hone := selectedActivity_one security constant (commonConstant_one.trans hconstant)
  have hbody := (RaisingPatternBudget.bodyFactor_pos security).le
  cases flag <;> simp only [RootOrdinaryGroupedChannel.cost, Bool.false_eq_true, if_false, if_true, mul_one]
  all_goals nlinarith [mul_nonneg hbody (by linarith : 0 ≤ selectedActivity security constant)]

theorem selected_root_removed {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (role : Fin r ⊕ Fin s) (slot : selectedRootSlots r s role) :
    rootEmbedding selection tagged ⟨.inl role, slot⟩ ∈ selection.removed := by
  have hequal : rootEmbedding selection tagged ⟨.inl role, slot⟩ =
      selection.removedEmbedding (selectedRootEquiv r s ⟨role, slot⟩) := rfl
  rw [hequal]
  exact Finset.mem_map.mpr ⟨_, Finset.mem_univ _, rfl⟩

theorem group_cost_le {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (constant : ℝ) (hconstant : commonConstant ≤ constant)
    (group : ActiveGroup selection tagged) :
    ActualRootGroupedChannel.cost selection tagged group ≤ leadingCost selection tagged group *
      ∏ slot : groupRootSlots selection tagged group,
        taggedActivity selection tagged constant (rootEmbedding selection tagged ⟨group, slot⟩) := by
  rcases group with (primary | ordinary) | kept
  · have hfactor (slot : Fin 2) : taggedActivity selection tagged constant
        (rootEmbedding selection tagged ⟨.inl (.inl primary), slot⟩) =
        if ActualRootGroupedChannel.primaryFlags selection tagged primary slot then selectedActivity security constant else 1 := by
      unfold taggedActivity
      rw [activity, if_pos (selected_root_removed selection tagged (.inl primary) slot)]
      simp only [ActualRootGroupedChannel.primaryFlags, decide_eq_true_eq]
    change RootPrimaryGroupedChannel.cost security (ActualRootGroupedChannel.primaryFlags selection tagged primary) ≤
      (2 * primaryFactor security) * ∏ slot : Fin 2, _
    simp_rw [hfactor]
    exact primary_cost_activity security constant hconstant _
  · have hfactor : taggedActivity selection tagged constant
        (rootEmbedding selection tagged ⟨.inl (.inr ordinary), (0 : Fin 1)⟩) =
        if ActualRootGroupedChannel.ordinaryFlag selection tagged ordinary then selectedActivity security constant else 1 := by
      unfold taggedActivity
      rw [activity, if_pos (selected_root_removed selection tagged (.inr ordinary) (0 : Fin 1))]
      simp only [ActualRootGroupedChannel.ordinaryFlag, decide_eq_true_eq]
    change RootOrdinaryGroupedChannel.cost security (ActualRootGroupedChannel.ordinaryFlag selection tagged ordinary) ≤
      (2 * bodyFactor security) * ∏ slot : Fin 1, _
    rw [Fin.prod_univ_one, hfactor]
    exact ordinary_cost_activity security constant hconstant _
  · change RootUnselectedBlockChannel.channelConstant / (Parameters.base security : ℝ) ^ 94 ≤
      1 * ∏ slot : Fin 1, _
    rw [Fin.prod_univ_one, one_mul]
    change RootUnselectedBlockChannel.channelConstant / (Parameters.base security : ℝ) ^ 94 ≤
      taggedActivity selection tagged constant kept.val.val
    have hnot : kept.val.val ∉ selection.removed := by
      rw [← selection.removed_complement]
      simp only [OmittedBlockMean.removed, Finset.mem_filter, Finset.mem_univ, true_and, not_not]
      exact kept.val.property
    unfold taggedActivity activity
    rw [if_pos kept.property, if_neg hnot]
    exact div_le_div_of_nonneg_right (commonConstant_background.trans hconstant) (by positivity)

theorem tagged_root_product {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (constant : ℝ) :
    (∏ group : ActiveGroup selection tagged, ∏ slot : groupRootSlots selection tagged group,
      taggedActivity selection tagged constant (rootEmbedding selection tagged ⟨group, slot⟩)) =
      ∏ vertex ∈ tagged, activity selection constant vertex := by
  have hsigma := Fintype.prod_sigma (fun point : Sigma (groupRootSlots selection tagged) =>
    taggedActivity selection tagged constant (rootEmbedding selection tagged point))
  apply Eq.trans hsigma.symm
  unfold taggedActivity
  rw [← Finset.prod_filter]
  apply Finset.prod_bij (fun source _ => rootEmbedding selection tagged source)
  · intro source hsource
    exact (Finset.mem_filter.mp hsource).2
  · intro first _ second _ hequal
    exact (rootEmbedding selection tagged).injective hequal
  · intro vertex hvertex
    refine ⟨tagEmbedding selection tagged ⟨vertex, hvertex⟩, ?_, tag_image selection tagged ⟨vertex, hvertex⟩⟩
    simp only [Finset.mem_filter, Finset.mem_univ, tag_image, true_and]
    exact hvertex
  · intro source _
    rfl

theorem leading_cost_product {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) :
    (∏ group : ActiveGroup selection tagged, leadingCost selection tagged group) =
      (2 : ℝ) ^ (r + s) * ControlNorm.gradeWeight (primaryFactor security) (bodyFactor security) r s := by
  simp only [Fintype.prod_sum_type, leadingCost, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    mul_pow, pow_add, ControlNorm.gradeWeight]
  ring

/-- Every actual grouped channel contributes its sharp leading pool factor
and at most one activity for each tagged physical root vertex. -/
theorem product_cost_le {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (constant : ℝ) (hconstant : commonConstant ≤ constant) :
    (∏ group : ActiveGroup selection tagged, ActualRootGroupedChannel.cost selection tagged group) ≤
      (2 : ℝ) ^ (r + s) * ControlNorm.gradeWeight (primaryFactor security) (bodyFactor security) r s *
        ∏ vertex ∈ tagged, activity selection constant vertex := by
  apply (Finset.prod_le_prod (fun group _ => ActualRootGroupedChannel.cost_nonneg selection tagged group)
    (fun group _ => group_cost_le selection tagged constant hconstant group)).trans_eq
  rw [Finset.prod_mul_distrib, leading_cost_product, tagged_root_product]

end
end CurrentAFT.RootGroupCostBudget
