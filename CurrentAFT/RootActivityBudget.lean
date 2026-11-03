import CurrentAFT.WeightedSubsetSum
import CurrentAFT.ActualRootGroupedChannel

/-! # Actual selected and unselected root activity at the current parameters -/
namespace CurrentAFT.RootActivityBudget
open AFT ActualBlockFock TaggedSelection BackgroundRates CycleSelections
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance finDecEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  ordinaryPool

def commonConstant : ℝ := max 1 (max RootTaggedSelectedNorm.selectedConstant
  (max (48 * Real.sqrt 131074) RootUnselectedBlockChannel.channelConstant))

theorem commonConstant_one : 1 ≤ commonConstant := le_max_left _ _
theorem commonConstant_primary : RootTaggedSelectedNorm.selectedConstant ≤ commonConstant :=
  (le_max_left _ _).trans (le_max_right _ _)
theorem commonConstant_ordinary : 48 * Real.sqrt 131074 ≤ commonConstant :=
  (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
theorem commonConstant_background : RootUnselectedBlockChannel.channelConstant ≤ commonConstant :=
  (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))

def selectedActivity (security : ℕ) (constant : ℝ) : ℝ := constant * (Parameters.base security : ℝ) ^ 17
def backgroundActivity (security : ℕ) (constant : ℝ) : ℝ := constant / (Parameters.base security : ℝ) ^ 94
def activity {security r s : ℕ} (selection : Selection security r s) (constant : ℝ)
    (vertex : BlockIndex security) : ℝ :=
  if vertex ∈ selection.removed then selectedActivity security constant else backgroundActivity security constant

theorem selectedActivity_one (security : ℕ) (constant : ℝ) (hone : 1 ≤ constant) :
    1 ≤ selectedActivity security constant := by
  have hb : (1 : ℝ) ≤ Parameters.base security := by exact_mod_cast (Parameters.base_ge_two security).trans' (by norm_num)
  exact (one_le_mul_of_one_le_of_one_le hone (one_le_pow₀ hb))

theorem bodyFactor_lower (security : ℕ) :
    1 / (Real.sqrt 131074 * (Parameters.base security : ℝ) ^ 80) ≤ bodyFactor security := by
  have hb : (0 : ℝ) < Parameters.base security := by exact_mod_cast Parameters.base_pos security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by exact_mod_cast (Parameters.base_ge_two security).trans' (by norm_num)
  have hpool : (ordinaryPool security : ℝ) ≤ 131074 * (Parameters.base security : ℝ) ^ 160 := by
    have hnat : ordinaryPool security ≤ Parameters.dimension security := by
      unfold ordinaryPool Parameters.dimension
      omega
    exact_mod_cast hnat.trans (Parameters.dimension_bounds security).2
  have hpoolPos : (0 : ℝ) < ordinaryPool security := by exact_mod_cast ordinaryPool_pos security
  have hsqrt : Real.sqrt (ordinaryPool security : ℝ) ≤ Real.sqrt 131074 * (Parameters.base security : ℝ) ^ 80 := by
    apply (Real.sqrt_le_sqrt hpool).trans_eq
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 131074),
      show (Parameters.base security : ℝ) ^ 160 = ((Parameters.base security : ℝ) ^ 80) ^ 2 by rw [← pow_mul],
      Real.sqrt_sq (pow_nonneg hb.le _)]
  have hradius : 1 ≤ radius security := Real.one_le_rpow hb1 (by norm_num : (0 : ℝ) ≤ 1 / 4)
  calc
    _ ≤ 1 / Real.sqrt (ordinaryPool security : ℝ) := one_div_le_one_div_of_le (Real.sqrt_pos.mpr hpoolPos) hsqrt
    _ ≤ radius security / Real.sqrt (ordinaryPool security : ℝ) :=
      div_le_div_of_nonneg_right hradius (Real.sqrt_nonneg _)
    _ = _ := rfl

theorem primary_tag_cost_relative (security : ℕ) (constant : ℝ)
    (hconstant : RootTaggedSelectedNorm.selectedConstant ≤ constant) :
    RootTaggedSelectedNorm.selectedConstant / (Parameters.base security : ℝ) ^ 47 ≤
      primaryFactor security * selectedActivity security constant := by
  have hb : (0 : ℝ) < Parameters.base security := by exact_mod_cast Parameters.base_pos security
  rw [primaryFactor_eq, selectedActivity]
  calc
    _ ≤ constant / (Parameters.base security : ℝ) ^ 47 := div_le_div_of_nonneg_right hconstant (pow_nonneg hb.le _)
    _ = _ := by field_simp

theorem ordinary_tag_cost_relative (security : ℕ) (constant : ℝ)
    (hconstant : 48 * Real.sqrt 131074 ≤ constant) :
    48 / (Parameters.base security : ℝ) ^ 63 ≤ bodyFactor security * selectedActivity security constant := by
  have hb : (0 : ℝ) < Parameters.base security := by exact_mod_cast Parameters.base_pos security
  have hsqrt : (0 : ℝ) < Real.sqrt 131074 := Real.sqrt_pos.mpr (by norm_num)
  calc
    _ = (1 / (Real.sqrt 131074 * (Parameters.base security : ℝ) ^ 80)) *
        ((48 * Real.sqrt 131074) * (Parameters.base security : ℝ) ^ 17) := by field_simp
    _ ≤ bodyFactor security * ((48 * Real.sqrt 131074) * (Parameters.base security : ℝ) ^ 17) :=
      mul_le_mul_of_nonneg_right (bodyFactor_lower security) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hconstant (pow_nonneg hb.le _))
      (RaisingPatternBudget.bodyFactor_pos security).le

theorem activity_nonneg {security r s : ℕ} (selection : Selection security r s) (constant : ℝ)
    (hconstant : 0 ≤ constant) (vertex : BlockIndex security) : 0 ≤ activity selection constant vertex := by
  unfold activity selectedActivity backgroundActivity
  split_ifs <;> positivity

theorem block_card (security : ℕ) : Fintype.card (BlockIndex security) = Parameters.bodySize security := by
  have hroom := ProposalPrimary.population_room security
  simp only [BlockIndex, Fintype.card_sum, Fintype.card_fin]
  unfold centerCount
  omega

theorem sum_activity_le {security r s : ℕ} (selection : Selection security r s) (constant : ℝ)
    (hconstant : 0 ≤ constant) :
    (∑ vertex, activity selection constant vertex) ≤
      ((2 * r + s : ℕ) : ℝ) * selectedActivity security constant +
        (Parameters.bodySize security : ℝ) * backgroundActivity security constant := by
  have hb : 0 ≤ backgroundActivity security constant := by unfold backgroundActivity; positivity
  have hpoint (vertex : BlockIndex security) : activity selection constant vertex ≤
      (if vertex ∈ selection.removed then selectedActivity security constant else 0) + backgroundActivity security constant := by
    unfold activity
    split_ifs <;> linarith
  have h := Finset.sum_le_sum (fun vertex (_ : vertex ∈ (Finset.univ : Finset (BlockIndex security))) => hpoint vertex)
  simpa only [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const_zero,
    add_zero, Finset.sum_const, Finset.card_univ, block_card, Selection.removed_card, nsmul_eq_mul] using h

theorem sum_activity_tag_le {security r s : ℕ} (selection : Selection security r s) (constant : ℝ)
    (hconstant : 0 ≤ constant) :
    (∑ vertex, activity selection constant vertex) * currentRootTag security ≤
      constant * (((2 * r + s : ℕ) : ℝ) + 131074) / (Parameters.base security : ℝ) ^ 13 := by
  have hb : (0 : ℝ) < Parameters.base security := by exact_mod_cast Parameters.base_pos security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by exact_mod_cast (Parameters.base_ge_two security).trans' (by norm_num)
  have hbody : (Parameters.bodySize security : ℝ) ≤ 131074 * (Parameters.base security : ℝ) ^ 160 := by
    have hnat : Parameters.bodySize security ≤ Parameters.dimension security := by unfold Parameters.dimension; omega
    exact_mod_cast hnat.trans (Parameters.dimension_bounds security).2
  have hpower : (Parameters.base security : ℝ) ^ 17 ≤ (Parameters.base security : ℝ) ^ 66 :=
    pow_le_pow_right₀ hb1 (by omega)
  have hbackground : (131074 * (Parameters.base security : ℝ) ^ 160) *
      (constant / (Parameters.base security : ℝ) ^ 94) =
      131074 * constant * (Parameters.base security : ℝ) ^ 66 := by field_simp
  have hsum : (∑ vertex, activity selection constant vertex) ≤
      constant * (((2 * r + s : ℕ) : ℝ) + 131074) * (Parameters.base security : ℝ) ^ 66 := by
    calc
      _ ≤ (((2 * r + s : ℕ) : ℝ) * (constant * (Parameters.base security : ℝ) ^ 17)) +
          (Parameters.bodySize security : ℝ) * (constant / (Parameters.base security : ℝ) ^ 94) :=
        sum_activity_le selection constant hconstant
      _ ≤ (((2 * r + s : ℕ) : ℝ) * (constant * (Parameters.base security : ℝ) ^ 66)) +
          (131074 * (Parameters.base security : ℝ) ^ 160) * (constant / (Parameters.base security : ℝ) ^ 94) :=
        add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpower hconstant) (Nat.cast_nonneg _))
          (mul_le_mul_of_nonneg_right hbody (div_nonneg hconstant (pow_nonneg hb.le _)))
      _ = _ := by rw [hbackground]; ring
  have htag : 0 ≤ currentRootTag security := by rw [currentRootTag_eq]; positivity
  calc
    _ ≤ (constant * (((2 * r + s : ℕ) : ℝ) + 131074) * (Parameters.base security : ℝ) ^ 66) * currentRootTag security :=
      mul_le_mul_of_nonneg_right hsum htag
    _ = _ := by rw [currentRootTag_eq]; field_simp

theorem subset_activity_tag_le {security r s : ℕ} (selection : Selection security r s) (constant : ℝ)
    (hconstant : 0 ≤ constant) (degree : ℕ) :
    (∑ selected ∈ Finset.univ.powersetCard degree,
      (∏ vertex ∈ selected, activity selection constant vertex) * currentRootTag security ^ degree) ≤
      (constant * (((2 * r + s : ℕ) : ℝ) + 131074) / (Parameters.base security : ℝ) ^ 13) ^ degree := by
  have htag : 0 ≤ currentRootTag security := by rw [currentRootTag_eq]; positivity
  apply (WeightedSubsetSum.tagged_sum_le_power Finset.univ (activity selection constant)
    (fun vertex _ => activity_nonneg selection constant hconstant vertex) (currentRootTag security) htag degree).trans
  apply pow_le_pow_left₀ _ (sum_activity_tag_le selection constant hconstant) degree
  exact mul_nonneg (Finset.sum_nonneg (fun vertex _ => activity_nonneg selection constant hconstant vertex)) htag

theorem sum_activity_tag_order_le {security r s : ℕ} (selection : Selection security r s) (constant : ℝ)
    (hconstant : 0 ≤ constant) (maximum : ℕ) (hdegree : r + s ≤ maximum) :
    (∑ vertex, activity selection constant vertex) * currentRootTag security ≤
      constant * ((2 * maximum : ℕ) + 131074 : ℝ) / (Parameters.base security : ℝ) ^ 13 := by
  apply (sum_activity_tag_le selection constant hconstant).trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ hconstant
  have hnat : 2 * r + s ≤ 2 * maximum := by omega
  exact_mod_cast Nat.add_le_add_right hnat 131074

theorem budget_power_small (security maximum degree : ℕ) (constant : ℝ) (hconstant : 1 ≤ constant)
    (hdegree : 2 ≤ degree) (hmaximum : degree ≤ maximum) :
    (constant / (Parameters.base security : ℝ) ^ 13) ^ degree ≤
      constant ^ maximum / (Parameters.base security : ℝ) ^ 26 := by
  have hb : (0 : ℝ) < Parameters.base security := by exact_mod_cast Parameters.base_pos security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by exact_mod_cast (Parameters.base_ge_two security).trans' (by norm_num)
  have hdenominator : (Parameters.base security : ℝ) ^ 26 ≤ ((Parameters.base security : ℝ) ^ 13) ^ degree := by
    have h := pow_le_pow_right₀ (one_le_pow₀ hb1 : 1 ≤ (Parameters.base security : ℝ) ^ 13) hdegree
    simpa only [← pow_mul] using h
  rw [div_pow]
  calc
    _ ≤ constant ^ maximum / ((Parameters.base security : ℝ) ^ 13) ^ degree :=
      div_le_div_of_nonneg_right (pow_le_pow_right₀ hconstant hmaximum) (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left (pow_nonneg (by linarith : 0 ≤ constant) _) (pow_pos hb _) hdenominator

end
end CurrentAFT.RootActivityBudget
