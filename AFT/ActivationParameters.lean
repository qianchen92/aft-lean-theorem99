import AFT.ClippedSource

/-!
# The actual activation at the reference V7 cutoff

The mark probability and both clipped Gaussian zero atoms are included in
the definition. The eventual inverse-fifth-power lower bound is proved,
rather than supplied as a parameter hypothesis to the primary inverse.
-/

namespace AFT.GaussianSource

open Filter
open scoped Topology

noncomputable section

def legCutoff (cutoffScale : ℝ) (parameter : ℕ) : ℕ :=
  ⌈cutoffScale * (parameter : ℝ) ^ (9 / 8 : ℝ)⌉₊

def legFeatureCount (cutoffScale : ℝ) (parameter : ℕ) : ℕ :=
  (2 * legCutoff cutoffScale parameter - 1) ^ 2

def v7Activation (cutoffScale : ℝ) (parameter : ℕ) : ℝ :=
  activation (parameter : ℝ) (10 * parameter)
    (legCutoff cutoffScale parameter - 1) (legFeatureCount cutoffScale parameter)

theorem legCutoff_positive (cutoffScale : ℝ) (parameter : ℕ)
    (hscale : 1 ≤ cutoffScale) (hp : 1 ≤ parameter) : 0 < legCutoff cutoffScale parameter := by
  have hp' : (1 : ℝ) ≤ parameter := by exact_mod_cast hp
  have hr : 1 ≤ (parameter : ℝ) ^ (9 / 8 : ℝ) :=
    Real.one_le_rpow hp' (by norm_num)
  have hceil := Nat.le_ceil (cutoffScale * (parameter : ℝ) ^ (9 / 8 : ℝ))
  have hh : (1 : ℝ) ≤ legCutoff cutoffScale parameter := by
    dsimp [legCutoff]
    nlinarith
  have : 1 ≤ legCutoff cutoffScale parameter := by exact_mod_cast hh
  omega

theorem legFeatureCount_positive (cutoffScale : ℝ) (parameter : ℕ)
    (hscale : 1 ≤ cutoffScale) (hp : 1 ≤ parameter) : 0 < legFeatureCount cutoffScale parameter := by
  have h := legCutoff_positive cutoffScale parameter hscale hp
  exact pow_pos (by omega) _

theorem legFeatureCount_upper (cutoffScale : ℝ) (parameter : ℕ)
    (hscale : 1 ≤ cutoffScale) (hp : 1 ≤ parameter) :
    (legFeatureCount cutoffScale parameter : ℝ) ≤
      4 * (cutoffScale + 1) ^ 2 * (parameter : ℝ) ^ (9 / 4 : ℝ) := by
  have hp' : (1 : ℝ) ≤ parameter := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < parameter := lt_of_lt_of_le zero_lt_one hp'
  have hr : 1 ≤ (parameter : ℝ) ^ (9 / 8 : ℝ) := Real.one_le_rpow hp' (by norm_num)
  have hceil := (Nat.ceil_lt_add_one (show 0 ≤ cutoffScale *
    (parameter : ℝ) ^ (9 / 8 : ℝ) by positivity)).le
  have hc : (legCutoff cutoffScale parameter : ℝ) ≤
      (cutoffScale + 1) * (parameter : ℝ) ^ (9 / 8 : ℝ) := by
    dsimp [legCutoff]
    nlinarith
  have hpow : ((parameter : ℝ) ^ (9 / 8 : ℝ)) ^ 2 =
      (parameter : ℝ) ^ (9 / 4 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
    norm_num
  calc
    _ = ((2 * legCutoff cutoffScale parameter - 1 : ℕ) : ℝ) ^ 2 := by
      simp only [legFeatureCount, Nat.cast_pow]
    _ ≤ (2 * (legCutoff cutoffScale parameter : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by exact_mod_cast (Nat.sub_le
        (2 * legCutoff cutoffScale parameter) 1)) _
    _ ≤ (2 * ((cutoffScale + 1) * (parameter : ℝ) ^ (9 / 8 : ℝ))) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hc (by norm_num)) _
    _ = _ := by rw [mul_pow, mul_pow, hpow]; ring

theorem v7Activation_lower_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) :
    ∀ᶠ parameter : ℕ in atTop, ((parameter : ℝ) ^ 5)⁻¹ ≤ v7Activation cutoffScale parameter := by
  let constant : ℝ := 4000 * (cutoffScale + 1) ^ 2 * (1 + 2 / Real.pi) ^ 2
  have ht : Tendsto (fun parameter : ℕ => (parameter : ℝ) ^ (3 / 4 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 4)).comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ parameter : ℕ in atTop, constant ≤ (parameter : ℝ) ^ (3 / 4 : ℝ) :=
    ht.eventually (eventually_ge_atTop constant)
  filter_upwards [hlarge, eventually_ge_atTop 1] with parameter hlarge hp
  have hp' : (1 : ℝ) ≤ parameter := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < parameter := lt_of_lt_of_le zero_lt_one hp'
  have hf := legFeatureCount_upper cutoffScale parameter hscale hp
  have hf0 := legFeatureCount_positive cutoffScale parameter hscale hp
  have ha := activation_lower (parameter : ℝ) (10 * parameter)
    (legCutoff cutoffScale parameter - 1) (legFeatureCount cutoffScale parameter)
    hp' (by linarith) hf0
  have hpower : (parameter : ℝ) ^ (9 / 4 : ℝ) * (parameter : ℝ) ^ 2 =
      (parameter : ℝ) ^ (17 / 4 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hp0]
    norm_num
  have hpower' : (parameter : ℝ) ^ (3 / 4 : ℝ) * (parameter : ℝ) ^ (17 / 4 : ℝ) =
      (parameter : ℝ) ^ 5 := by
    rw [← Real.rpow_add hp0]
    norm_num
    exact Real.rpow_natCast _ 5
  have hden : 100 * (legFeatureCount cutoffScale parameter : ℝ) * (1 + 2 / Real.pi) ^ 2 *
      (parameter : ℝ) * (10 * parameter) ≤ (parameter : ℝ) ^ 5 := by
    calc
      _ ≤ 100 * (4 * (cutoffScale + 1) ^ 2 * (parameter : ℝ) ^ (9 / 4 : ℝ)) *
          (1 + 2 / Real.pi) ^ 2 * (parameter : ℝ) * (10 * parameter) := by gcongr
      _ = constant * (parameter : ℝ) ^ (17 / 4 : ℝ) := by
        dsimp [constant]
        rw [← hpower]
        ring
      _ ≤ (parameter : ℝ) ^ (3 / 4 : ℝ) * (parameter : ℝ) ^ (17 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right hlarge (Real.rpow_nonneg hp0.le _)
      _ = _ := hpower'
  change ((parameter : ℝ) ^ 5)⁻¹ ≤ _
  simpa only [one_div, v7Activation] using
    (one_div_le_one_div_of_le (by positivity) hden).trans ha

end

end AFT.GaussianSource
