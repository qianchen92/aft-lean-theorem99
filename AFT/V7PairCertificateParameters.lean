import AFT.PairCertificatePower

/-! # The complete safe-pair residual at the actual V7 parameters -/

namespace AFT.GaussianSource

open Filter
open scoped BigOperators Classical Topology
open SafeConvolution

attribute [local instance] actualModulusNeZero

theorem pairCore_fourteen_size_eventually :
    ∀ᶠ parameter : ℕ in atTop,
      pairCoreDepth parameter 14 ≤ 77 * parameter ^ 3 ∧
      4 * pairCoreDepth parameter 14 ≤ Parameters.modulus parameter ∧
      ((pairCore parameter 14).card : ℝ) =
        (Parameters.modulus parameter : ℝ) - 2 * pairCoreDepth parameter 14 := by
  filter_upwards [eventually_ge_atTop 308] with parameter hp
  have hp2 : 2 ≤ parameter := by omega
  have hp1 : 1 ≤ parameter := by omega
  have h23 : parameter ^ 2 ≤ parameter ^ 3 := Nat.pow_le_pow_right hp1 (by decide)
  have hd : pairCoreDepth parameter 14 ≤ 77 * parameter ^ 3 := by
    unfold pairCoreDepth Parameters.safeMargin v7RootCutoff
    rw [Parameters.security_eq parameter hp2]
    nlinarith [Nat.sub_le (3 * parameter ^ 2) 1]
  have hlarge : 4 * pairCoreDepth parameter 14 ≤ parameter ^ 40 := by
    calc
      _ ≤ 4 * (77 * parameter ^ 3) := Nat.mul_le_mul_left _ hd
      _ ≤ parameter * parameter ^ 3 := by nlinarith
      _ = parameter ^ 4 := by ring
      _ ≤ _ := Nat.pow_le_pow_right hp1 (by decide)
  have hq : parameter ^ 40 ≤ Parameters.modulus parameter := by
    simpa only [Parameters.security_eq parameter hp2] using (Parameters.modulus_bounds parameter).1
  refine ⟨hd, hlarge.trans hq, ?_⟩
  have hnonneg : (0 : ℤ) ≤ (Parameters.modulus parameter : ℤ) - 2 * pairCoreDepth parameter 14 := by omega
  have hh : ((pairCore parameter 14).card : ℤ) = (Parameters.modulus parameter : ℤ) - 2 * pairCoreDepth parameter 14 := by
    unfold pairCore
    rw [TrimmedSlice.paletteSlice_card _ _ _ (by positivity)]
    simp only [abs_zero, sub_zero]
    exact Int.toNat_of_nonneg hnonneg
  exact_mod_cast hh

/-- Choosing fifteen finite Neumann terms gives the full squared uniform
pair residual O(lambda^-21), with the true safe core and integer pair. -/
theorem actual_pair_certificate_square_eventually {σ : ℕ → Type*} [∀ parameter, Fintype (σ parameter)]
    (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (boundary : ℕ → ℤ) (starts sources : (parameter : ℕ) → σ parameter → ℤ)
    (sourceLaw : (parameter : ℕ) → FiniteDist (σ parameter))
    (hphysical : ∀ᶠ parameter : ℕ in atTop,
      (0 ≤ boundary parameter ∧ boundary parameter ≤ Parameters.safeMargin parameter) ∧
      (∀ sample shift, shift ∈ anchorInterval (starts parameter sample) (Parameters.anchorWidth parameter) →
        |shift| ≤ 3 * (Parameters.anchorWidth parameter : ℤ)) ∧
      (∀ sample, |sources parameter sample| ≤ legCutoff cutoffScale parameter)) :
    ∀ᶠ parameter : ℕ in atTop,
      let mass := TrimmedSlice.mixedPair (Parameters.modulus parameter) (boundary parameter)
        (starts parameter) (sources parameter) (sourceLaw parameter).weight (Parameters.anchorWidth parameter)
      let seed := actualPairCoreSeed parameter 14 mass
      let bodyImage := convolution (actualRootPair parameter).weight (actualCompactRootInput parameter 14 seed)
      let target := uniformCanonical (fun color => mass color.1 color.2)
      ((Parameters.modulus parameter : ℝ) * countingL2 (bodyImage - target)) ^ 2 ≤
        pairCertificateConstant / (parameter : ℝ) ^ 21 := by
  have hbound := actual_pair_certificate_bound_eventually cutoffScale hscale 14 boundary starts sources sourceLaw hphysical
  have hclear := v7_primaryCalibration_clearance_eventually cutoffScale hscale boundary
    (hphysical.mono fun _ h => h.1)
  filter_upwards [hbound, hclear, pairCore_fourteen_size_eventually, eventually_ge_atTop 2]
    with parameter hb hc hs hp
  have hlow : (parameter : ℝ) ^ 40 ≤ Parameters.modulus parameter := by
    exact_mod_cast (show parameter ^ 40 ≤ Parameters.modulus parameter by
      simpa only [Parameters.security_eq parameter hp] using (Parameters.modulus_bounds parameter).1)
  have hupp : (Parameters.modulus parameter : ℝ) ≤ 2 * (parameter : ℝ) ^ 40 := by
    exact_mod_cast (show Parameters.modulus parameter ≤ 2 * parameter ^ 40 by
      simpa only [Parameters.security_eq parameter hp] using (Parameters.modulus_bounds parameter).2)
  have hden : (Parameters.modulus parameter : ℝ) / 2 ≤ (Parameters.modulus parameter : ℝ) -
      2 * boundary parameter - 3 * (parameter : ℝ) ^ 32 - legCutoff cutoffScale parameter := by
    have hh : 2 * (3 * (parameter : ℝ) ^ 32 + 2 * boundary parameter + legCutoff cutoffScale parameter) ≤
        Parameters.modulus parameter := by
      exact_mod_cast (by simpa only [Parameters.anchorWidth, Parameters.security_eq parameter hp] using hc.2)
    linarith
  have hsize : (Parameters.modulus parameter : ℝ) / 2 ≤ (pairCore parameter 14).card := by
    have hh : 4 * (pairCoreDepth parameter 14 : ℝ) ≤ Parameters.modulus parameter := by exact_mod_cast hs.2.1
    rw [hs.2.2]
    linarith
  have hscalar := pair_certificate_scalar_square (parameter : ℝ) (Parameters.modulus parameter)
    ((Parameters.modulus parameter : ℝ) - 2 * boundary parameter - 3 * (parameter : ℝ) ^ 32 - legCutoff cutoffScale parameter)
    (pairCore parameter 14).card (pairCoreDepth parameter 14) (by exact_mod_cast (by omega : 1 ≤ parameter))
    hlow hupp hden (by positivity) (by exact_mod_cast hs.1) hsize hs.2.2
  dsimp only at hb ⊢
  simp only [Parameters.anchorWidth, Parameters.security_eq parameter hp, Nat.cast_pow] at hb
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hb
  have hbsq := pow_le_pow_left₀ (mul_nonneg (show (0 : ℝ) ≤ Parameters.modulus parameter from Nat.cast_nonneg _) (countingL2_nonneg _)) hb 2
  simpa only [Parameters.anchorWidth, Parameters.security_eq parameter hp, Nat.cast_pow] using hbsq.trans hscalar

/-- The complete true pair residual retains the sharp activation cost. -/
theorem actual_pair_certificate_activated_square_eventually {σ : ℕ → Type*} [∀ parameter, Fintype (σ parameter)]
    (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (boundary : ℕ → ℤ) (starts sources : (parameter : ℕ) → σ parameter → ℤ)
    (sourceLaw : (parameter : ℕ) → FiniteDist (σ parameter))
    (hphysical : ∀ᶠ parameter : ℕ in atTop,
      (0 ≤ boundary parameter ∧ boundary parameter ≤ Parameters.safeMargin parameter) ∧
      (∀ sample shift, shift ∈ anchorInterval (starts parameter sample) (Parameters.anchorWidth parameter) →
        |shift| ≤ 3 * (Parameters.anchorWidth parameter : ℤ)) ∧
      (∀ sample, |sources parameter sample| ≤ legCutoff cutoffScale parameter)) :
    ∀ᶠ parameter : ℕ in atTop,
      let mass := TrimmedSlice.mixedPair (Parameters.modulus parameter) (boundary parameter)
        (starts parameter) (sources parameter) (sourceLaw parameter).weight (Parameters.anchorWidth parameter)
      let seed := actualPairCoreSeed parameter 14 mass
      let bodyImage := convolution (actualRootPair parameter).weight (actualCompactRootInput parameter 14 seed)
      let target := uniformCanonical (fun color => mass color.1 color.2)
      ((v7Activation cutoffScale parameter ^ 2)⁻¹ *
        ((Parameters.modulus parameter : ℝ) * countingL2 (bodyImage - target))) ^ 2 ≤
        (activationConstant cutoffScale ^ 4 * pairCertificateConstant) / (parameter : ℝ) ^ 4 := by
  filter_upwards [actual_pair_certificate_square_eventually cutoffScale hscale boundary starts sources sourceLaw hphysical,
    eventually_ge_atTop 1] with parameter hh hp
  exact pair_certificate_activation_square cutoffScale hscale parameter hp _ hh

end AFT.GaussianSource
