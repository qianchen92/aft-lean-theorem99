import CurrentAFT.BackgroundRates
import CurrentAFT.FiniteAtomMoments

/-! # Actual population and atom budgets for fixed public-control moments -/

namespace CurrentAFT.FiniteAtomMoments

open AFT
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount BackgroundRates.ordinaryPool

def currentAtomLower (security : ℕ) : ℝ := 1 / (4 * (Parameters.modulus security : ℝ) ^ 2)

theorem currentAtomLower_positive (security : ℕ) : 0 < currentAtomLower security := by
  have hq := FirstResponse.modulus_pos security
  unfold currentAtomLower
  positivity

theorem currentAtomLower_sqrt (security : ℕ) :
    Real.sqrt (currentAtomLower security) = 1 / (2 * (Parameters.modulus security : ℝ)) := by
  have hq := FirstResponse.modulus_pos security
  unfold currentAtomLower
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one,
    show 4 * (Parameters.modulus security : ℝ) ^ 2 = (2 * (Parameters.modulus security : ℝ)) ^ 2 by ring,
    Real.sqrt_sq (by positivity)]

/-- The exact current modulus-square-to-primary-population budget is a
constant, because `q≤131072 base^64` and `L=base^128`. -/
theorem modulus_square_primary_budget (security : ℕ) :
    (Parameters.modulus security : ℝ) ^ 2 / Parameters.legCount security ≤ (131072 : ℝ) ^ 2 := by
  have hb := FirstResponse.base_pos security
  have hq : (Parameters.modulus security : ℝ) ≤ 131072 * (Parameters.base security : ℝ) ^ 64 := by
    exact_mod_cast (Parameters.modulus_bounds security).2
  have hsq := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ Parameters.modulus security) hq 2
  rw [Parameters.legCount_eq, Nat.cast_pow]
  apply (div_le_iff₀ (pow_pos hb 128)).mpr
  convert hsq using 1; ring

theorem modulus_square_body_budget (security : ℕ) :
    (Parameters.modulus security : ℝ) ^ 2 / BackgroundRates.ordinaryPool security ≤ (131072 : ℝ) ^ 2 := by
  have hb := FirstResponse.base_pos security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by
    exact_mod_cast (show 1 ≤ Parameters.base security by have := Parameters.base_ge_two security; omega)
  have hpool : Parameters.legCount security ≤ BackgroundRates.ordinaryPool security := by
    rw [Parameters.legCount_eq]
    exact (Nat.pow_le_pow_right (by have := Parameters.base_ge_two security; omega) (by omega)).trans
      (BackgroundRates.ordinaryPool_lower security)
  have hlegPositive : (0 : ℝ) < Parameters.legCount security := by
    rw [Parameters.legCount_eq, Nat.cast_pow]
    positivity
  have hpoolReal : (Parameters.legCount security : ℝ) ≤ BackgroundRates.ordinaryPool security := by
    exact_mod_cast hpool
  apply (div_le_div_of_nonneg_left (sq_nonneg _) hlegPositive hpoolReal).trans
  exact modulus_square_primary_budget security

/-- Any population of at least `base^128` pays a bounded atom/fixed-fiber
ratio. This covers both actual unequal pools. -/
theorem current_population_atom_ratio (security population : ℕ)
    (hpopulation : Parameters.base security ^ 128 ≤ population) :
    (1 / Real.sqrt (population : ℝ)) / Real.sqrt (currentAtomLower security) ≤ 262144 := by
  have hb := FirstResponse.base_pos security
  have hq := FirstResponse.modulus_pos security
  have hpop : (0 : ℝ) < population := by
    exact_mod_cast (pow_pos (Parameters.base_pos security) 128).trans_le hpopulation
  have hsqrt : (Parameters.base security : ℝ) ^ 64 ≤ Real.sqrt (population : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    have hh : (Parameters.base security : ℝ) ^ 128 ≤ population := by exact_mod_cast hpopulation
    convert hh using 1; ring
  have hqu : (Parameters.modulus security : ℝ) ≤ 131072 * (Parameters.base security : ℝ) ^ 64 := by
    exact_mod_cast (Parameters.modulus_bounds security).2
  rw [currentAtomLower_sqrt]
  have hequal : (1 / Real.sqrt (population : ℝ)) / (1 / (2 * (Parameters.modulus security : ℝ))) =
      2 * (Parameters.modulus security : ℝ) / Real.sqrt (population : ℝ) := by field_simp
  rw [hequal]
  calc
    _ ≤ 2 * (131072 * (Parameters.base security : ℝ) ^ 64) / Real.sqrt (population : ℝ) :=
      div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
    _ ≤ 2 * (131072 * (Parameters.base security : ℝ) ^ 64) / (Parameters.base security : ℝ) ^ 64 :=
      div_le_div_of_nonneg_left (by positivity) (pow_pos hb 64) hsqrt
    _ = _ := by field_simp; norm_num

theorem current_primary_atom_ratio (security : ℕ) :
    (1 / Real.sqrt (Parameters.legCount security : ℝ)) / Real.sqrt (currentAtomLower security) ≤ 262144 :=
  current_population_atom_ratio security _ (by rw [Parameters.legCount_eq])

theorem current_body_atom_ratio (security : ℕ) :
    (1 / Real.sqrt (BackgroundRates.ordinaryPool security : ℝ)) / Real.sqrt (currentAtomLower security) ≤ 262144 := by
  apply current_population_atom_ratio
  exact (Nat.pow_le_pow_right (by have := Parameters.base_ge_two security; omega) (by omega)).trans
    (BackgroundRates.ordinaryPool_lower security)

/-- A common explicit threshold supplies both distinct-index moment
normalizers at all arities up to the fixed calibration order. -/
theorem current_pool_room (security maximum : ℕ) (hsecurity : 2 * maximum ≤ security) :
    ∀ primaryOrder bodyOrder, primaryOrder + bodyOrder ≤ maximum →
      2 * primaryOrder ≤ Parameters.legCount security ∧
        2 * bodyOrder ≤ BackgroundRates.ordinaryPool security := by
  intro primaryOrder bodyOrder horders
  have hprimary : Parameters.base security ≤ Parameters.legCount security := by
    rw [Parameters.legCount_eq]
    exact Nat.le_self_pow (by decide) _
  have hbody : Parameters.base security ≤ BackgroundRates.ordinaryPool security :=
    (Nat.le_self_pow (by decide) _).trans (BackgroundRates.ordinaryPool_lower security)
  have hbase : security ≤ Parameters.base security := by simp [Parameters.base]
  omega

end

end CurrentAFT.FiniteAtomMoments
