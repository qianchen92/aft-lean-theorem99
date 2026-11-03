import AFT.ActivationParameters

namespace AFT.GaussianSource

open Filter

noncomputable section

def activationConstant (cutoffScale : ℝ) : ℝ :=
  4000 * (cutoffScale + 1) ^ 2 * (1 + 2 / Real.pi) ^ 2

theorem activationConstant_pos (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) :
    0 < activationConstant cutoffScale := by
  unfold activationConstant
  have hh : 0 < cutoffScale + 1 := by linarith
  positivity

/-- The sharp inverse-activation exponent required by the background
certificate, with an explicit cutoff-dependent constant. -/
theorem v7Activation_lower_rpow (cutoffScale : ℝ) (parameter : ℕ)
    (hscale : 1 ≤ cutoffScale) (hp : 1 ≤ parameter) :
    1 / (activationConstant cutoffScale * (parameter : ℝ) ^ (17 / 4 : ℝ)) ≤
      v7Activation cutoffScale parameter := by
  have hp' : (1 : ℝ) ≤ parameter := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < parameter := zero_lt_one.trans_le hp'
  have hf := legFeatureCount_upper cutoffScale parameter hscale hp
  have hf0 := legFeatureCount_positive cutoffScale parameter hscale hp
  have ha := activation_lower (parameter : ℝ) (10 * parameter)
    (legCutoff cutoffScale parameter - 1) (legFeatureCount cutoffScale parameter)
    hp' (by linarith) hf0
  have hpower : (parameter : ℝ) ^ (9 / 4 : ℝ) * (parameter : ℝ) ^ 2 =
      (parameter : ℝ) ^ (17 / 4 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hp0]
    norm_num
  have hden : 100 * (legFeatureCount cutoffScale parameter : ℝ) * (1 + 2 / Real.pi) ^ 2 *
      (parameter : ℝ) * (10 * parameter) ≤ activationConstant cutoffScale *
        (parameter : ℝ) ^ (17 / 4 : ℝ) := by
    calc
      _ ≤ 100 * (4 * (cutoffScale + 1) ^ 2 * (parameter : ℝ) ^ (9 / 4 : ℝ)) *
          (1 + 2 / Real.pi) ^ 2 * (parameter : ℝ) * (10 * parameter) := by gcongr
      _ = _ := by rw [← hpower]; unfold activationConstant; ring
  exact (one_div_le_one_div_of_le (by positivity) hden).trans ha

theorem v7Activation_inverse_upper (cutoffScale : ℝ) (parameter : ℕ)
    (hscale : 1 ≤ cutoffScale) (hp : 1 ≤ parameter) :
    (v7Activation cutoffScale parameter)⁻¹ ≤
      activationConstant cutoffScale * (parameter : ℝ) ^ (17 / 4 : ℝ) := by
  have hc := activationConstant_pos cutoffScale hscale
  have hp0 : (0 : ℝ) < parameter := by exact_mod_cast (by omega : 0 < parameter)
  have h := one_div_le_one_div_of_le (by positivity : 0 <
    1 / (activationConstant cutoffScale * (parameter : ℝ) ^ (17 / 4 : ℝ)))
      (v7Activation_lower_rpow cutoffScale parameter hscale hp)
  simpa only [one_div, inv_inv] using h

theorem v7Activation_lower_rpow_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) :
    ∀ᶠ parameter : ℕ in atTop,
      1 / (activationConstant cutoffScale * (parameter : ℝ) ^ (17 / 4 : ℝ)) ≤
        v7Activation cutoffScale parameter := by
  filter_upwards [eventually_ge_atTop 1] with parameter hp
  exact v7Activation_lower_rpow cutoffScale parameter hscale hp

end

end AFT.GaussianSource
