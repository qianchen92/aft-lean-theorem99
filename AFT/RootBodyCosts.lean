import AFT.RootBodyInput
import AFT.IndependentResponseCost
import AFT.PairedRootCost
import AFT.ActualQueueBudget

/-! # Summable actual V7 costs of ordinary and queued root sources -/
namespace AFT.V7Calibration
open GaussianSource Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance rootBodyCostsFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance rootBodyCostsSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _

theorem sqrt_div_rpow_round (constant x exponent : ℝ) (power : ℕ)
    (hc : 0 ≤ constant) (hx : 1 ≤ x) (he : (2*power : ℕ) ≤ exponent) :
    Real.sqrt (constant/x^exponent) ≤ Real.sqrt constant/x^power := by
  have hx0 : 0<x := zero_lt_one.trans_le hx
  have hden : x^(2*power) ≤ x^exponent := by
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hx he
  have hh := Real.sqrt_le_sqrt (div_le_div_of_nonneg_left hc (pow_pos hx0 _) hden)
  apply hh.trans_eq
  rw [Real.sqrt_div hc]
  congr 1
  rw [show 2*power=power*2 by omega,pow_mul,Real.sqrt_sq (pow_nonneg hx0.le _)]

theorem rootBodyFullCost_ordinary_le (n : ℕ) (hn : 1 ≤ n) :
    rootBodyFullCost n 0 ≤ Real.sqrt ordinaryRootEnergyConstant/(n : ℝ)^36 := by
  rw [rootBodyFullCost,if_pos rfl]
  exact sqrt_div_rpow_round _ _ _ _ (by unfold ordinaryRootEnergyConstant ordinaryRootDeltaConstant; positivity)
    (by exact_mod_cast hn) (by norm_num)

theorem rootBodyRowCost_ordinary_le (n : ℕ) (hn : 1 ≤ n) :
    rootBodyRowCost n 0 ≤ Real.sqrt ordinaryRootRowConstant/(n : ℝ)^17 := by
  rw [rootBodyRowCost,if_pos rfl]
  exact sqrt_div_rpow_round _ _ _ _ (by unfold ordinaryRootRowConstant ordinaryRootDeltaConstant; positivity)
    (by exact_mod_cast hn) (by norm_num)

def rootBodyOrdinaryConstant (C : ℝ) : ℝ :=
  16*activationConstant C*(Real.sqrt ordinaryRootEnergyConstant+2*Real.sqrt ordinaryRootRowConstant)

def rootBodyShiftedConstant (C : ℝ) : ℝ :=
  16*activationConstant C*(Real.sqrt 175104+32)

/-- The exact local calibrated input cost with one genuine ANOVA source
allocation. The allocation is used once per source, not per output fiber. -/
def rootBodyAllocatedCost (C : ℝ) (n pool : ℕ) (offset : ℤ) : ℝ :=
  (1/Real.sqrt (Parameters.bodies n : ℝ))*independentCoordinateCost C n pool*
    (rootBodyFullCost n offset+(1/Real.sqrt (pool : ℝ))*rootBodyRowCost n offset)

theorem rootBodyAllocatedCost_nonneg (C : ℝ) (n pool : ℕ) (offset : ℤ)
    (hrho : 0 ≤ v7Activation C n) : 0 ≤ rootBodyAllocatedCost C n pool offset := by
  unfold rootBodyAllocatedCost independentCoordinateCost
  exact mul_nonneg (by positivity)
    (add_nonneg (rootBodyFullCost_nonneg n offset) (mul_nonneg (by positivity) (rootBodyRowCost_nonneg n offset)))

/-- Every realized local source cost is polynomially small. The ordinary
bound uses its actual calibrated variance; the shifted bound is uniform. -/
theorem rootBodyAllocatedCost_bounds_eventually (C : ℝ) (hC : 1 ≤ C)
    (pool : ℕ → ℕ) (hpool : ∀ᶠ n in atTop,Parameters.legs n ≤ 2*pool n) :
    ∀ᶠ n in atTop,
      rootBodyAllocatedCost C n (pool n) 0 ≤ rootBodyOrdinaryConstant C/(n : ℝ)^72 ∧
      ∀ offset : ℤ,offset ≠ 0 →
        rootBodyAllocatedCost C n (pool n) offset ≤ rootBodyShiftedConstant C/(n : ℝ)^55 := by
  filter_upwards [root_allocation_le_eventually,hpool,eventually_ge_atTop 2]
    with n hroot hp hn
  have hx : (0 : ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hx1 : (1 : ℝ)≤n := by exact_mod_cast (by omega : 1≤n)
  have ha := activationConstant_pos C hC
  have hrho : 0<v7Activation C n := activation_positive _ _ _ _ (legFeatureCount_positive C n hC (by omega))
  have hrate : 1/Real.sqrt (pool n : ℝ) ≤ 2/(n : ℝ)^15 := by
    simpa only [Parameters.security_eq n hn] using (v7_primary_pool_rate_bound n (pool n) hp).2
  have hcoord : independentCoordinateCost C n (pool n) ≤ 8*activationConstant C/(n : ℝ)^10 := by
    apply (independentCoordinateCost_le C hC n (pool n) hn hp).trans
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hx1
      (by norm_num : ((10 : ℕ) : ℝ) ≤ 43/4)
  have hcoord0 : 0 ≤ independentCoordinateCost C n (pool n) := by unfold independentCoordinateCost; positivity
  have hord : rootBodyFullCost n 0+(1/Real.sqrt (pool n : ℝ))*rootBodyRowCost n 0 ≤
      (Real.sqrt ordinaryRootEnergyConstant+2*Real.sqrt ordinaryRootRowConstant)/(n : ℝ)^32 := by
    have hf : rootBodyFullCost n 0 ≤ Real.sqrt ordinaryRootEnergyConstant/(n : ℝ)^32 :=
      (rootBodyFullCost_ordinary_le n (by omega)).trans
        (div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by positivity) (pow_le_pow_right₀ hx1 (by omega)))
    have hr := mul_le_mul hrate (rootBodyRowCost_ordinary_le n (by omega))
      (rootBodyRowCost_nonneg n 0) (by positivity)
    apply (add_le_add hf hr).trans_eq
    field_simp
  constructor
  · unfold rootBodyAllocatedCost
    have hh := mul_le_mul (mul_le_mul hroot hcoord hcoord0 (by positivity)) hord
      (add_nonneg (rootBodyFullCost_nonneg n 0) (mul_nonneg (by positivity) (rootBodyRowCost_nonneg n 0)))
      (by positivity)
    exact hh.trans_eq (by unfold rootBodyOrdinaryConstant; field_simp; ring)
  · intro offset hoff
    have hf : rootBodyFullCost n offset ≤ Real.sqrt 175104/(n : ℝ)^15 := by
      rw [rootBodyFullCost,if_neg hoff]
      have he : Real.sqrt (175104/(n : ℝ)^38)=Real.sqrt 175104/(n : ℝ)^19 := by
        rw [Real.sqrt_div (by norm_num : (0 : ℝ)≤175104)]
        congr 1
        rw [show (n : ℝ)^38=((n : ℝ)^19)^2 by ring,Real.sqrt_sq (by positivity)]
      rw [he]
      exact div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by positivity)
        (pow_le_pow_right₀ hx1 (by omega))
    have hs : rootBodyFullCost n offset+(1/Real.sqrt (pool n : ℝ))*rootBodyRowCost n offset ≤
        (Real.sqrt 175104+32)/(n : ℝ)^15 := by
      rw [rootBodyRowCost,if_neg hoff]
      exact (add_le_add hf (mul_le_mul_of_nonneg_right hrate (by norm_num : (0 : ℝ)≤16))).trans_eq (by ring)
    unfold rootBodyAllocatedCost
    have hh := mul_le_mul (mul_le_mul hroot hcoord hcoord0 (by positivity)) hs
      (add_nonneg (rootBodyFullCost_nonneg n offset) (mul_nonneg (by positivity) (rootBodyRowCost_nonneg n offset)))
      (by positivity)
    exact hh.trans_eq (by unfold rootBodyShiftedConstant; field_simp; ring)

/-- Summing all genuine queue placements pays only the q selected blocks;
the remaining N blocks keep the ordinary-root variance. -/
theorem actual_root_body_source_sum_eventually (C : ℝ) (hC : 1 ≤ C)
    (pool : ℕ → ℕ) (hpool : ∀ᶠ n in atTop,Parameters.legs n ≤ 2*pool n) :
    ∀ᶠ n in atTop, ∀ sample : Window (queueCutoff n) × Equiv.Perm (blockIndex n),
      (∑ index : blockIndex n,rootBodyAllocatedCost C n (pool n) (actualQueueShifts n sample index)) ≤
        (2*rootBodyOrdinaryConstant C+2*rootBodyShiftedConstant C)/(n : ℝ)^12 := by
  filter_upwards [rootBodyAllocatedCost_bounds_eventually C hC pool hpool,eventually_ge_atTop 2]
    with n h hn sample
  have hx : (0 : ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hx1 : (1 : ℝ)≤n := by exact_mod_cast (by omega : 1≤n)
  have ha := activationConstant_pos C hC
  have hO : 0≤rootBodyOrdinaryConstant C := by unfold rootBodyOrdinaryConstant; positivity
  have hS : 0≤rootBodyShiftedConstant C := by unfold rootBodyShiftedConstant; positivity
  have hi (index : blockIndex n) : rootBodyAllocatedCost C n (pool n) (actualQueueShifts n sample index) ≤
      rootBodyOrdinaryConstant C/(n : ℝ)^72+
        if sample.2 index ∈ actualQueueSelection n then rootBodyShiftedConstant C/(n : ℝ)^55 else 0 := by
    by_cases hz : actualQueueShifts n sample index=0
    · rw [hz]
      exact h.1.trans (le_add_of_nonneg_right (by split_ifs <;> positivity))
    · have hsel : sample.2 index ∈ actualQueueSelection n := by
        by_contra hnsel
        apply hz
        simp only [actualQueueShifts,FiniteDist.sharedQueueShift,if_neg hnsel]
      rw [if_pos hsel]
      exact (h.2 _ hz).trans (le_add_of_nonneg_left (by positivity))
  have hN : (Parameters.bodies n : ℝ) ≤ 2*(n : ℝ)^60 := by
    have hb : Parameters.bodies n ≤ Parameters.dimension n := by unfold Parameters.bodies; omega
    exact_mod_cast hb.trans (by simpa only [Parameters.security_eq n hn] using (Parameters.dimension_bounds n).2)
  have hq : (Parameters.modulus n : ℝ) ≤ 2*(n : ℝ)^40 := by
    exact_mod_cast (by simpa only [Parameters.security_eq n hn] using (Parameters.modulus_bounds n).2)
  calc
    _ ≤ ∑ index : blockIndex n,(rootBodyOrdinaryConstant C/(n : ℝ)^72+
        if sample.2 index ∈ actualQueueSelection n then rootBodyShiftedConstant C/(n : ℝ)^55 else 0) :=
      Finset.sum_le_sum fun index _ => hi index
    _ = (Parameters.bodies n : ℝ)*(rootBodyOrdinaryConstant C/(n : ℝ)^72)+
        (Parameters.modulus n : ℝ)*(rootBodyShiftedConstant C/(n : ℝ)^55) := by
      rw [Finset.sum_add_distrib]
      rw [Equiv.sum_comp sample.2 (fun index => if index ∈ actualQueueSelection n then rootBodyShiftedConstant C/(n : ℝ)^55 else 0)]
      simp only [Finset.sum_ite_mem,Finset.univ_inter,Finset.sum_const,Finset.card_univ,
        blockIndex_card,actualQueueSelection_card,nsmul_eq_mul]
    _ ≤ (2*(n : ℝ)^60)*(rootBodyOrdinaryConstant C/(n : ℝ)^72)+
        (2*(n : ℝ)^40)*(rootBodyShiftedConstant C/(n : ℝ)^55) := by gcongr
    _ = 2*rootBodyOrdinaryConstant C/(n : ℝ)^12+2*rootBodyShiftedConstant C/(n : ℝ)^15 := by field_simp
    _ ≤ 2*rootBodyOrdinaryConstant C/(n : ℝ)^12+2*rootBodyShiftedConstant C/(n : ℝ)^12 := by
      exact add_le_add le_rfl (div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hS) (by positivity)
        (pow_le_pow_right₀ hx1 (by omega : 12≤15)))
    _ = _ := by ring

end
end AFT.V7Calibration
