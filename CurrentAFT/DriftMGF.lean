import CurrentAFT.HistogramMean
import CurrentAFT.ActualCycleMeanMGF

/-! # Actual current queue-drift square-exponential budget -/

namespace CurrentAFT.DriftMGF

open AFT ProposalPrimary HistogramMean UniformBodyProfiles
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension BackgroundRates.radius

theorem modulus_sq_le_dimension (security : ℕ) : Parameters.modulus security ^ 2 ≤ Parameters.dimension security := by
  have hpower : 131072 ≤ Parameters.base security ^ 32 := by
    have h := Nat.pow_le_pow_left (Parameters.base_ge_two security) 32
    norm_num at h
    omega
  have hq := (Parameters.modulus_bounds security).2
  have hq96 : Parameters.modulus security ≤ Parameters.base security ^ 96 := by
    apply hq.trans
    calc
      _ ≤ Parameters.base security ^ 32 * Parameters.base security ^ 64 := Nat.mul_le_mul_right _ hpower
      _ = _ := by rw [← pow_add]
  have hbody := Nat.mul_le_mul_left (Parameters.modulus security) hq96
  rw [← Parameters.bodySize_eq] at hbody
  have hsq : Parameters.modulus security ^ 2 ≤ Parameters.bodySize security := by
    simpa only [pow_two] using hbody
  exact hsq.trans (ActualCycleMeanMGF.bodySize_le_dimension security)

theorem drift_norm_coarse (security : ℕ) (queue : ℤ) : ‖drift security queue‖ ≤ 2 * deviation security := by
  have hd : (0 : ℝ) < Parameters.dimension security := by
    have hb := Parameters.base_pos security
    have h := (Parameters.dimension_bounds security).1
    exact_mod_cast (lt_of_lt_of_le (by positivity : 0 < 65536 * Parameters.base security ^ 160) h)
  have hq : (Parameters.modulus security : ℝ) ≤ Real.sqrt (Parameters.dimension security : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    exact_mod_cast modulus_sq_le_dimension security
  apply (drift_norm_le security queue).trans
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hd)).mpr
  have h := mul_le_mul_of_nonneg_left hq (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (deviation_nonneg security))
  nlinarith only [h]

theorem radius_drift_budget (security : ℕ) (queue : ℤ) (constant : ℝ) (hconstant : 0 ≤ constant) :
    (constant * BackgroundRates.radius security ^ 2) * ‖drift security queue‖ ^ 2 ≤
      66564 * constant / (Parameters.base security : ℝ) ^ 60 := by
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) (drift_norm_coarse security queue) 2
  calc
    _ ≤ (constant * BackgroundRates.radius security ^ 2) * (2 * deviation security) ^ 2 :=
      mul_le_mul_of_nonneg_left hsquare (mul_nonneg hconstant (sq_nonneg _))
    _ = 4 * ((constant * BackgroundRates.radius security ^ 2) * deviation security ^ 2) := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left (ActualCycleMeanMGF.radius_deviation_budget security constant hconstant)
      (by norm_num : (0 : ℝ) ≤ 4)).trans_eq (by ring)

theorem drift_exp_eventually (constant : ℝ) (hconstant : 0 ≤ constant) :
    ∃ threshold : ℕ, ∀ security ≥ threshold, ∀ queue : ℤ,
      Real.exp ((constant * BackgroundRates.radius security ^ 2) * ‖drift security queue‖ ^ 2) ≤ Real.exp 1 := by
  refine ⟨Nat.ceil (66564 * constant) + 1, ?_⟩
  intro security hsecurity queue
  have hb := FirstResponse.base_pos security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by
    exact_mod_cast (Parameters.base_ge_two security).trans' (by norm_num : 1 ≤ 2)
  have hlarge : 66564 * constant ≤ (Parameters.base security : ℝ) := by
    have hn : Nat.ceil (66564 * constant) ≤ Parameters.base security := by rw [Parameters.base]; omega
    exact (Nat.le_ceil _).trans (by exact_mod_cast hn)
  apply Real.exp_le_exp.mpr
  apply (radius_drift_budget security queue constant hconstant).trans
  apply (div_le_one (pow_pos hb 60)).mpr
  exact hlarge.trans (le_self_pow₀ hb1 (by decide))

end

end CurrentAFT.DriftMGF
