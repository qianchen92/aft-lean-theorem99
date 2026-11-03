import AFT.TrimmedPairCoreBounds
import AFT.PairSmoothingParameters

/-! # Actual finite safe-pair certificate with every error term retained -/

namespace AFT.GaussianSource

open Filter
open scoped BigOperators Classical Topology
open SafeConvolution

attribute [local instance] actualModulusNeZero

/-- Uniform over the physical source mixture, including inactive-source
conditioning: the actual finite safe root input has this complete bound. -/
theorem actual_pair_certificate_bound_eventually {σ : ℕ → Type*} [∀ parameter, Fintype (σ parameter)]
    (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (depth : ℕ)
    (boundary : ℕ → ℤ) (starts sources : (parameter : ℕ) → σ parameter → ℤ)
    (sourceLaw : (parameter : ℕ) → FiniteDist (σ parameter))
    (hphysical : ∀ᶠ parameter : ℕ in atTop,
      (0 ≤ boundary parameter ∧ boundary parameter ≤ Parameters.safeMargin parameter) ∧
      (∀ sample shift, shift ∈ anchorInterval (starts parameter sample) (Parameters.anchorWidth parameter) →
        |shift| ≤ 3 * (Parameters.anchorWidth parameter : ℤ)) ∧
      (∀ sample, |sources parameter sample| ≤ legCutoff cutoffScale parameter)) :
    ∀ᶠ parameter : ℕ in atTop,
      let modulus : ℝ := Parameters.modulus parameter
      let width : ℝ := Parameters.anchorWidth parameter
      let denominator := modulus - 2 * boundary parameter - 3 * width - legCutoff cutoffScale parameter
      let mass := TrimmedSlice.mixedPair (Parameters.modulus parameter) (boundary parameter)
        (starts parameter) (sources parameter) (sourceLaw parameter).weight (Parameters.anchorWidth parameter)
      let seed := actualPairCoreSeed parameter depth mass
      let bodyImage := convolution (actualRootPair parameter).weight (actualCompactRootInput parameter depth seed)
      let target := uniformCanonical (fun color => mass color.1 color.2)
      modulus * countingL2 (bodyImage - target) ≤
        modulus * (12 / (parameter : ℝ)) ^ (depth + 1) * Real.sqrt (1 / (width * denominator)) +
        modulus * Real.sqrt (1 / ((pairCore parameter depth).card : ℝ) - 1 / modulus) *
          (2 * Real.sqrt (1 / denominator) + Real.sqrt (1 / ((pairCore parameter depth).card : ℝ)) + Real.sqrt (1 / modulus)) +
        (depth + 1 : ℕ) * Real.sqrt (416 / (parameter : ℝ) ^ 21) +
        modulus * Real.sqrt (4 * (pairCoreDepth parameter depth : ℝ) / (width * denominator ^ 2)) := by
  have hsmooth := actual_pair_smoothing_square_eventually cutoffScale hscale depth boundary starts sources sourceLaw hphysical
  have hclear := v7_primaryCalibration_clearance_eventually cutoffScale hscale boundary
    (hphysical.mono fun _ h => h.1)
  filter_upwards [hphysical, hclear, hsmooth, pairCore_nonempty_eventually depth, eventually_ge_atTop 2]
    with parameter hs hc hsm hcore hp
  dsimp only at hsm ⊢
  let mass := TrimmedSlice.mixedPair (Parameters.modulus parameter) (boundary parameter)
    (starts parameter) (sources parameter) (sourceLaw parameter).weight (Parameters.anchorWidth parameter)
  let core := pairCore parameter depth
  let restricted := fun color : Fin (Parameters.modulus parameter) × Fin (Parameters.modulus parameter) =>
    SafePair.restrictPair core mass color.1 color.2
  have hq : 0 < (Parameters.modulus parameter : ℝ) := by exact_mod_cast (Parameters.modulus_prime parameter).pos
  have hcoreSmall : 2 * (pairCoreDepth parameter depth : ℤ) < Parameters.modulus parameter := by
    have hh := Finset.card_pos.mpr hcore
    change 0 < (TrimmedSlice.paletteSlice (Parameters.modulus parameter) (pairCoreDepth parameter depth) 0).card at hh
    rw [TrimmedSlice.paletteSlice_card _ _ _ (by positivity)] at hh
    simp only [abs_zero, sub_zero] at hh
    omega
  have hh := TrimmedSlice.mixedPair_core_bounds (Parameters.modulus parameter) (boundary parameter)
    (3 * Parameters.anchorWidth parameter) (legCutoff cutoffScale parameter) (pairCoreDepth parameter depth)
    (Parameters.anchorWidth parameter) (by simp only [Parameters.anchorWidth, Parameters.security_eq parameter hp]; positivity)
    (starts parameter) (sources parameter) (sourceLaw parameter) hs.1.1 (by positivity) hcoreSmall hs.2.1 hs.2.2 (by have hqNat := (Parameters.modulus_prime parameter).pos; omega)
  dsimp only at hh
  have hsmnorm : (Parameters.modulus parameter : ℝ) *
      countingL2 (convolution (actualCompactBox parameter).weight restricted - restricted) ≤
      Real.sqrt (416 / (parameter : ℝ) ^ 21) := by
    apply Real.le_sqrt_of_sq_le
    rw [mul_pow, countingL2, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    exact hsm
  have hbound := mul_le_mul_of_nonneg_left (actualPairInput_error_le parameter depth (by omega) mass) hq.le
  have hseed := mul_le_mul_of_nonneg_left hh.1
    (show 0 ≤ (Parameters.modulus parameter : ℝ) * (12 / (parameter : ℝ)) ^ (depth + 1) by positivity)
  have hreference := mul_le_mul_of_nonneg_left hh.2.1 hq.le
  have hedge := mul_le_mul_of_nonneg_left hh.2.2 hq.le
  have hsmoothing := mul_le_mul_of_nonneg_left hsmnorm (Nat.cast_nonneg (depth + 1))
  change (Parameters.modulus parameter : ℝ) * (12 / (parameter : ℝ)) ^ (depth + 1) *
    countingL2 (actualPairCoreSeed parameter depth mass) ≤ _ at hseed
  have hcanonical : uniformCanonical restricted = fun color => SafePair.canonicalPair
      (fun _ => 1 / (Parameters.modulus parameter : ℝ)) (SafePair.restrictPair core mass) color.1 color.2 := by
    funext color
    simp only [uniformCanonical_apply, Fintype.card_fin]
    rfl
  rw [show (fun color => SafePair.restrictPair (pairCore parameter depth) mass color.1 color.2) = restricted from rfl, hcanonical] at hbound
  change (Parameters.modulus parameter : ℝ) * countingL2
    (actualPairCoreSeed parameter depth mass - fun color => SafePair.canonicalPair
      (fun _ => 1 / (Parameters.modulus parameter : ℝ)) (SafePair.restrictPair core mass) color.1 color.2) ≤ _ at hreference
  change (Parameters.modulus parameter : ℝ) * countingL2
    (restricted - fun color => mass color.1 color.2) ≤ _ at hedge
  have hresult := add_le_add (add_le_add (add_le_add hseed hreference) hsmoothing) hedge
  apply hbound.trans
  convert hresult using 1 <;>
    (try simp only [pairCore, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]) <;> ring

end AFT.GaussianSource
