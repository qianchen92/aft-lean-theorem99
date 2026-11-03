import CurrentAFT.BackgroundTranslations

/-!
# Current graded population bounds for the free and queue atoms

These envelopes are explicit upper bounds on the graded norms of the
actual primary/body density components already constructed. The body
factor uses the actual ordinary-control population and the manuscript's
analysis radius. Population-multiplied linear and quadratic budgets are
proved below; no small-background premise is supplied.
-/

namespace CurrentAFT.BackgroundRates

open AFT DiffuseProfiles ProposalPrimary FringeCertificate BackgroundCertificates BackgroundTranslations
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount
  Parameters.safeMargin DiffuseProfiles.activation

def ordinaryPool (security : ℕ) : ℕ :=
  Parameters.bodySize security - Parameters.modulus security - 2 * Parameters.legCount security

def radius (security : ℕ) : ℝ := (Parameters.base security : ℝ) ^ (1 / 4 : ℝ)
def primaryFactor (security : ℕ) : ℝ := (Real.sqrt (Parameters.legCount security : ℝ))⁻¹
def bodyFactor (security : ℕ) : ℝ := radius security * (Real.sqrt (ordinaryPool security : ℝ))⁻¹

theorem ordinaryPool_lower (security : ℕ) : Parameters.base security ^ 160 ≤ ordinaryPool security := by
  have hb : 1 ≤ Parameters.base security := by have := Parameters.base_ge_two security; omega
  have hqLower := (Parameters.modulus_bounds security).1
  have h32 : Parameters.base security ^ 32 ≤ Parameters.base security ^ 64 := Nat.pow_le_pow_right hb (by omega)
  have hqEight : 8 * Parameters.base security ^ 32 ≤ Parameters.modulus security := by omega
  have hlegs : 8 * Parameters.legCount security ≤ Parameters.bodySize security := by
    have h := Nat.mul_le_mul_right (Parameters.base security ^ 96) hqEight
    simpa only [Parameters.legCount_eq, Parameters.bodySize_eq, mul_assoc, ← pow_add] using h
  have h96 : 4 ≤ Parameters.base security ^ 96 := by
    have h := Nat.pow_le_pow_left (Parameters.base_ge_two security) 96
    norm_num at h
    omega
  have hqFour : 4 * Parameters.modulus security ≤ Parameters.bodySize security := by
    have h := Nat.mul_le_mul_left (Parameters.modulus security) h96
    simpa only [Parameters.bodySize_eq, mul_comm _ 4] using h
  have hbody : 65536 * Parameters.base security ^ 160 ≤ Parameters.bodySize security := by
    have h := Nat.mul_le_mul_right (Parameters.base security ^ 96) hqLower
    simpa only [Parameters.bodySize_eq, mul_assoc, ← pow_add] using h
  unfold ordinaryPool
  omega

theorem ordinaryPool_pos (security : ℕ) : 0 < ordinaryPool security :=
  (pow_pos (Parameters.base_pos security) _).trans_le (ordinaryPool_lower security)

theorem primaryFactor_eq (security : ℕ) :
    primaryFactor security = 1 / (Parameters.base security : ℝ) ^ 64 := by
  have hb := FirstResponse.base_pos security
  unfold primaryFactor
  rw [Parameters.legCount_eq, Nat.cast_pow,
    show 128 = 64 * 2 by omega, pow_mul, Real.sqrt_sq (pow_nonneg hb.le _)]
  simp only [one_div]

theorem radius_le_base (security : ℕ) : radius security ≤ Parameters.base security := by
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by exact_mod_cast (show 1 ≤ Parameters.base security by
    have := Parameters.base_ge_two security; omega)
  simpa only [radius, Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hb1 (show (1 / 4 : ℝ) ≤ 1 by norm_num)

theorem bodyFactor_le (security : ℕ) : bodyFactor security ≤ 1 / (Parameters.base security : ℝ) ^ 79 := by
  have hb := FirstResponse.base_pos security
  have hpool : (Parameters.base security : ℝ) ^ 160 ≤ ordinaryPool security := by exact_mod_cast ordinaryPool_lower security
  have hsqrt : (Parameters.base security : ℝ) ^ 80 ≤ Real.sqrt (ordinaryPool security : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith only [hpool]
  have hpoolPos : (0 : ℝ) < ordinaryPool security := Nat.cast_pos.mpr (ordinaryPool_pos security)
  calc
    _ = radius security / Real.sqrt (ordinaryPool security : ℝ) := by rfl
    _ ≤ (Parameters.base security : ℝ) / Real.sqrt (ordinaryPool security : ℝ) :=
      div_le_div_of_nonneg_right (radius_le_base security) (Real.sqrt_nonneg _)
    _ ≤ (Parameters.base security : ℝ) / (Parameters.base security : ℝ) ^ 80 :=
      div_le_div_of_nonneg_left hb.le (pow_pos hb _) hsqrt
    _ = _ := by field_simp

def freeAtomEnvelope (security : ℕ) : ℝ :=
  primaryFactor security * Real.sqrt (∑ color, (primaryLaw security).weight color * primaryCertificateDensity security color ^ 2) +
  bodyFactor security * Real.sqrt (∑ color, (centerLaw security).weight color * bodyCertificateDensity security color ^ 2)

def translationAtomEnvelope (security : ℕ) (shift : ℤ) : ℝ :=
  primaryFactor security *
    (Real.sqrt (∑ color, (primaryLaw security).weight color * primaryCertificateDensity security color ^ 2) +
      Real.sqrt (∑ color, (primaryLaw security).weight color * residualCertificateDensity security shift color ^ 2)) +
  bodyFactor security * Real.sqrt (∑ color, (centerLaw security).weight color * safeSeedDensity security shift color ^ 2)

theorem freeAtomEnvelope_nonneg (security : ℕ) : 0 ≤ freeAtomEnvelope security := by
  unfold freeAtomEnvelope primaryFactor bodyFactor radius
  positivity

theorem translationAtomEnvelope_nonneg (security : ℕ) (shift : ℤ) : 0 ≤ translationAtomEnvelope security shift := by
  unfold translationAtomEnvelope primaryFactor bodyFactor radius
  positivity

theorem freeAtomEnvelope_decay (security : ℕ) :
    freeAtomEnvelope security ≤ 84 / (Parameters.base security : ℝ) ^ 110 := by
  have hb := FirstResponse.base_pos security
  have hfirst := mul_le_mul (le_of_eq (primaryFactor_eq security)) (primaryCertificateDensity_norm_decay security)
    (Real.sqrt_nonneg _) (by positivity : (0 : ℝ) ≤ 1 / (Parameters.base security : ℝ) ^ 64)
  have hsecond := mul_le_mul (bodyFactor_le security) (bodyCertificateDensity_norm_decay security)
    (Real.sqrt_nonneg _) (by positivity : (0 : ℝ) ≤ 1 / (Parameters.base security : ℝ) ^ 79)
  calc
    _ ≤ (1 / (Parameters.base security : ℝ) ^ 64) * (20 / (Parameters.base security : ℝ) ^ 46) +
      (1 / (Parameters.base security : ℝ) ^ 79) * (64 / (Parameters.base security : ℝ) ^ 31) := add_le_add hfirst hsecond
    _ = _ := by ring

theorem translationAtomEnvelope_decay (security : ℕ) (shift : ℤ) :
    translationAtomEnvelope security shift ≤ 56 / (Parameters.base security : ℝ) ^ 79 := by
  have hb := FirstResponse.base_pos security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by exact_mod_cast (show 1 ≤ Parameters.base security by
    have := Parameters.base_ge_two security; omega)
  have hsum := add_le_add (primaryCertificateDensity_norm_decay security) (residualCertificateDensity_norm_decay security shift)
  have hfirst := mul_le_mul (le_of_eq (primaryFactor_eq security)) hsum
    (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (by positivity : (0 : ℝ) ≤ 1 / (Parameters.base security : ℝ) ^ 64)
  have hsecond := mul_le_mul (bodyFactor_le security) (safeSeedDensity_norm_le_four security shift)
    (Real.sqrt_nonneg _) (by positivity : (0 : ℝ) ≤ 1 / (Parameters.base security : ℝ) ^ 79)
  have hpower : 52 / (Parameters.base security : ℝ) ^ 110 ≤ 52 / (Parameters.base security : ℝ) ^ 79 :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos hb _) (pow_le_pow_right₀ hb1 (by omega))
  calc
    _ ≤ (1 / (Parameters.base security : ℝ) ^ 64) *
        (20 / (Parameters.base security : ℝ) ^ 46 + 32 / (Parameters.base security : ℝ) ^ 46) +
      (1 / (Parameters.base security : ℝ) ^ 79) * 4 := add_le_add hfirst hsecond
    _ = 52 / (Parameters.base security : ℝ) ^ 110 + 4 / (Parameters.base security : ℝ) ^ 79 := by ring
    _ ≤ 52 / (Parameters.base security : ℝ) ^ 79 + 4 / (Parameters.base security : ℝ) ^ 79 :=
      add_le_add hpower le_rfl
    _ = _ := by ring

theorem free_population_quadratic_budget (security : ℕ) :
    (Parameters.bodySize security : ℝ) * freeAtomEnvelope security ^ 2 ≤
      924844032 / (Parameters.base security : ℝ) ^ 60 := by
  have hb := FirstResponse.base_pos security
  have hbody : (Parameters.bodySize security : ℝ) ≤ 131072 * (Parameters.base security : ℝ) ^ 160 := by
    have h := Nat.mul_le_mul_right (Parameters.base security ^ 96) (Parameters.modulus_bounds security).2
    exact_mod_cast (by simpa only [Parameters.bodySize_eq, mul_assoc, ← pow_add] using h)
  have hsquare := pow_le_pow_left₀ (freeAtomEnvelope_nonneg security) (freeAtomEnvelope_decay security) 2
  calc
    _ ≤ (131072 * (Parameters.base security : ℝ) ^ 160) * (84 / (Parameters.base security : ℝ) ^ 110) ^ 2 :=
      mul_le_mul hbody hsquare (sq_nonneg _) (by positivity)
    _ = _ := by field_simp; ring

theorem queue_population_quadratic_budget (security : ℕ) (shift : ℤ) :
    (Parameters.modulus security : ℝ) * translationAtomEnvelope security shift ^ 2 ≤
      411041792 / (Parameters.base security : ℝ) ^ 94 := by
  have hb := FirstResponse.base_pos security
  have hq : (Parameters.modulus security : ℝ) ≤ 131072 * (Parameters.base security : ℝ) ^ 64 := by
    exact_mod_cast (Parameters.modulus_bounds security).2
  have hsquare := pow_le_pow_left₀ (translationAtomEnvelope_nonneg security shift)
    (translationAtomEnvelope_decay security shift) 2
  calc
    _ ≤ (131072 * (Parameters.base security : ℝ) ^ 64) * (56 / (Parameters.base security : ℝ) ^ 79) ^ 2 :=
      mul_le_mul hq hsquare (sq_nonneg _) (by positivity)
    _ = _ := by field_simp; ring

theorem queue_population_linear_budget (security : ℕ) (shift : ℤ) :
    (Parameters.modulus security : ℝ) * translationAtomEnvelope security shift ≤
      7340032 / (Parameters.base security : ℝ) ^ 15 := by
  have hb := FirstResponse.base_pos security
  have hq : (Parameters.modulus security : ℝ) ≤ 131072 * (Parameters.base security : ℝ) ^ 64 := by
    exact_mod_cast (Parameters.modulus_bounds security).2
  calc
    _ ≤ (131072 * (Parameters.base security : ℝ) ^ 64) * (56 / (Parameters.base security : ℝ) ^ 79) :=
      mul_le_mul hq (translationAtomEnvelope_decay security shift)
        (translationAtomEnvelope_nonneg security shift) (by positivity)
    _ = _ := by field_simp; ring

end

end CurrentAFT.BackgroundRates
