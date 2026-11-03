import AFT.ActualPairSmoothing

/-! # The actual V7 powers in the complete integer-pair smoothing bound -/

namespace AFT.GaussianSource

open Filter
open scoped BigOperators Classical Topology
open AFT.SafeConvolution

noncomputable section

attribute [local instance] actualModulusNeZero

/-- With q in the actual lambda^40 interval, W=lambda^32, and compact
radius lambda^3, all three retained terms have their claimed powers. -/
theorem scaled_pair_smoothing_power (parameter modulus : ℝ) (hp : 1 ≤ parameter)
    (hq : parameter ^ 40 ≤ modulus) (hq' : modulus ≤ 2 * parameter ^ 40) :
    modulus ^ 2 *
      (16 * modulus * parameter ^ 3 / ((modulus / 2) ^ 2 * (parameter ^ 32) ^ 2) +
      16 * modulus * (parameter ^ 3) ^ 2 / ((modulus / 2) ^ 4 * parameter ^ 32) +
      8 * parameter ^ 3 / ((modulus / 2) ^ 2 * parameter ^ 32)) ≤
      416 / parameter ^ 21 := by
  have hp0 : 0 < parameter := by linarith
  have hq0 : 0 < modulus := lt_of_lt_of_le (by positivity) hq
  have heq : modulus ^ 2 *
      (16 * modulus * parameter ^ 3 / ((modulus / 2) ^ 2 * (parameter ^ 32) ^ 2) +
      16 * modulus * (parameter ^ 3) ^ 2 / ((modulus / 2) ^ 4 * parameter ^ 32) +
      8 * parameter ^ 3 / ((modulus / 2) ^ 2 * parameter ^ 32)) =
      64 * modulus * parameter ^ 3 / parameter ^ 64 +
      256 * parameter ^ 6 / (modulus * parameter ^ 32) + 32 / parameter ^ 29 := by
    field_simp
    ring
  rw [heq]
  have hfirst : 64 * modulus * parameter ^ 3 / parameter ^ 64 ≤ 128 / parameter ^ 21 := by
    calc
      _ ≤ 64 * (2 * parameter ^ 40) * parameter ^ 3 / parameter ^ 64 := by gcongr
      _ = _ := by field_simp; ring
  have hsecond : 256 * parameter ^ 6 / (modulus * parameter ^ 32) ≤ 256 / parameter ^ 66 := by
    calc
      _ ≤ 256 * parameter ^ 6 / (parameter ^ 40 * parameter ^ 32) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (mul_le_mul_of_nonneg_right hq (by positivity))
      _ = _ := by field_simp
  have h66 : 256 / parameter ^ 66 ≤ 256 / parameter ^ 21 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_right₀ hp (by decide))
  have h29 : 32 / parameter ^ 29 ≤ 32 / parameter ^ 21 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_right₀ hp (by decide))
  calc
    _ ≤ 128 / parameter ^ 21 + 256 / parameter ^ 21 + 32 / parameter ^ 21 :=
      add_le_add (add_le_add hfirst (hsecond.trans h66)) h29
    _ = _ := by ring

/-- This eventual estimate applies uniformly to every actual source/sign
mixture obeying the physical windows. The mixture law itself is arbitrary:
in particular conditioning the inactive source introduces no reciprocal
activation probability in the bound. -/
theorem actual_pair_smoothing_square_eventually {σ : ℕ → Type*} [∀ parameter, Fintype (σ parameter)]
    (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (depth : ℕ)
    (boundary : ℕ → ℤ) (starts sources : (parameter : ℕ) → σ parameter → ℤ)
    (sourceLaw : (parameter : ℕ) → FiniteDist (σ parameter))
    (hphysical : ∀ᶠ parameter : ℕ in atTop,
      (0 ≤ boundary parameter ∧ boundary parameter ≤ Parameters.safeMargin parameter) ∧
      (∀ sample shift, shift ∈ anchorInterval (starts parameter sample) (Parameters.anchorWidth parameter) →
        |shift| ≤ 3 * (Parameters.anchorWidth parameter : ℤ)) ∧
      (∀ sample, |sources parameter sample| ≤ legCutoff cutoffScale parameter)) :
    ∀ᶠ parameter : ℕ in atTop,
      let mass : Fin (Parameters.modulus parameter) × Fin (Parameters.modulus parameter) → ℝ :=
        fun color => SafePair.restrictPair (pairCore parameter depth)
          (TrimmedSlice.mixedPair (Parameters.modulus parameter) (boundary parameter) (starts parameter) (sources parameter)
            (sourceLaw parameter).weight (Parameters.anchorWidth parameter)) color.1 color.2
      (Parameters.modulus parameter : ℝ) ^ 2 *
        (∑ color, (convolution (actualCompactBox parameter).weight mass color - mass color) ^ 2) ≤
          416 / (parameter : ℝ) ^ 21 := by
  have hclear := v7_primaryCalibration_clearance_eventually cutoffScale hscale boundary
    (hphysical.mono fun _ h => h.1)
  filter_upwards [hphysical, hclear, pairCore_nonempty_eventually depth, eventually_ge_atTop 2]
    with parameter hs hc hcore hp
  have hcard : 2 * pairCoreDepth parameter depth < Parameters.modulus parameter := by
    have hh := Finset.card_pos.mpr hcore
    change 0 < (TrimmedSlice.paletteSlice (Parameters.modulus parameter) (pairCoreDepth parameter depth) 0).card at hh
    rw [TrimmedSlice.paletteSlice_card _ _ _ (by positivity)] at hh
    simp only [abs_zero, sub_zero] at hh
    omega
  have hboundary : boundary parameter ≤ pairCoreDepth parameter depth := by
    have hh := hs.1.2
    unfold pairCoreDepth
    omega
  have hradius : parameter ^ 3 ≤ pairCoreDepth parameter depth := by
    unfold pairCoreDepth
    simp only [Nat.add_mul, one_mul]
    omega
  have hq : 0 < (Parameters.modulus parameter : ℝ) := by exact_mod_cast (Parameters.modulus_prime parameter).pos
  have hD : (Parameters.modulus parameter : ℝ) / 2 ≤ (Parameters.modulus parameter : ℝ) - 2 * boundary parameter -
      3 * Parameters.anchorWidth parameter - legCutoff cutoffScale parameter := by
    have hh : 2 * (3 * (Parameters.anchorWidth parameter : ℝ) + 2 * boundary parameter + legCutoff cutoffScale parameter) ≤
        Parameters.modulus parameter := by exact_mod_cast hc.2
    linarith
  have hh := restrictedMixedPair_box_square_le parameter (pairCoreDepth parameter depth) (parameter ^ 3)
    (boundary parameter) (3 * Parameters.anchorWidth parameter) (legCutoff cutoffScale parameter)
    (starts parameter) (sources parameter) (sourceLaw parameter) (Parameters.anchorWidth parameter)
    ((Parameters.modulus parameter : ℝ) / 2) (by positivity) hcard.le hboundary hradius hs.2.1 hs.2.2 (by simpa only [Int.cast_mul, Int.cast_ofNat, Int.cast_natCast] using hD)
  have hscaled := mul_le_mul_of_nonneg_left hh (sq_nonneg (Parameters.modulus parameter : ℝ))
  have hlow : (parameter : ℝ) ^ 40 ≤ Parameters.modulus parameter := by
    exact_mod_cast (show parameter ^ 40 ≤ Parameters.modulus parameter by simpa only [Parameters.security_eq parameter hp] using (Parameters.modulus_bounds parameter).1)
  have hupp : (Parameters.modulus parameter : ℝ) ≤ 2 * (parameter : ℝ) ^ 40 := by
    exact_mod_cast (show Parameters.modulus parameter ≤ 2 * parameter ^ 40 by simpa only [Parameters.security_eq parameter hp] using (Parameters.modulus_bounds parameter).2)
  have hbound := scaled_pair_smoothing_power (parameter : ℝ) (Parameters.modulus parameter) (by exact_mod_cast (by omega : 1 ≤ parameter)) hlow hupp
  exact hscaled.trans (by simpa only [Parameters.anchorWidth, Parameters.security_eq parameter hp, Nat.cast_pow] using hbound)

end
end AFT.GaussianSource
