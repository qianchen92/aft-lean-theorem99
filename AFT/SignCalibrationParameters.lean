import AFT.SignCalibration
import AFT.PrimaryCalibrationParameters

/-!
# Actual V7 calibrated sign estimates with all asymptotic losses discharged
-/

namespace AFT

open Filter
open scoped BigOperators Topology

theorem GaussianSource.activation_le_one_hundredth (firstWidth secondWidth : ℝ)
    (cutoff featureCount : ℕ) :
    GaussianSource.activation firstWidth secondWidth cutoff featureCount ≤ 1 / 100 := by
  by_cases hfeatures : featureCount = 0
  · simp [GaussianSource.activation, hfeatures]
  have hfeatureReal : (1 : ℝ) ≤ featureCount := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hfeatures
  let distribution := (GaussianSource.windowGaussian firstWidth cutoff).prod
    (GaussianSource.windowGaussian secondWidth cutoff)
  have hpair : distribution.weight
      (GaussianSource.windowZero cutoff, GaussianSource.windowZero cutoff) ≤ 1 := by
    have hh := Finset.single_le_sum (fun index (_ : index ∈ Finset.univ) => distribution.nonneg index)
      (Finset.mem_univ (GaussianSource.windowZero cutoff, GaussianSource.windowZero cutoff))
    simpa only [distribution.sum_one] using hh
  have hmark : 1 / (100 * (featureCount : ℝ)) ≤ 1 / 100 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    linarith
  unfold GaussianSource.activation
  exact (mul_le_mul_of_nonneg_left hpair (by positivity)).trans (by simpa only [mul_one] using hmark)

namespace V7Calibration

noncomputable def basePrimary {σ τ : Type*} [Fintype σ] [Fintype τ]
    (parameter : ℕ) (cutoffScale : ℝ) (boundary : ℤ)
    (bodyShifts : σ → ℤ) (bodyLaw : FiniteDist σ)
    (startsPlus startsMinus sources : τ → ℤ) (sourceLaw : FiniteDist τ) :
    Fin (Parameters.modulus parameter) → ℝ := fun color =>
  TrimmedSlice.actualFairBasePrimary (Parameters.modulus parameter) (Parameters.safeMargin parameter)
    boundary (Parameters.anchorWidth parameter) (Parameters.bodies parameter) (Parameters.legs parameter)
    (GaussianSource.v7Activation cutoffScale parameter) bodyShifts bodyLaw.weight
    startsPlus startsMinus sources sourceLaw.weight color.val

noncomputable def signResponse {τ : Type*} [Fintype τ]
    (parameter : ℕ) (cutoffScale : ℝ) (boundary : ℤ)
    (startsPlus startsMinus sources : τ → ℤ) (sourceLaw : FiniteDist τ) :
    Fin (Parameters.modulus parameter) → ℝ := fun color =>
  TrimmedSlice.actualSignResponse (Parameters.modulus parameter) boundary startsPlus startsMinus sources
    sourceLaw.weight (Parameters.anchorWidth parameter) (GaussianSource.v7Activation cutoffScale parameter) color.val

def PhysicalSupports {τ : Type*} (parameter : ℕ) (cutoffScale : ℝ) (boundary : ℤ)
    (startsPlus startsMinus sources : τ → ℤ) : Prop :=
  (0 ≤ boundary ∧ boundary ≤ Parameters.safeMargin parameter) ∧
  (∀ index shift, shift ∈ anchorInterval (startsPlus index) (Parameters.anchorWidth parameter) →
    |shift| ≤ 3 * (Parameters.anchorWidth parameter : ℤ)) ∧
  (∀ index shift, shift ∈ anchorInterval (startsMinus index) (Parameters.anchorWidth parameter) →
    |shift| ≤ 3 * (Parameters.anchorWidth parameter : ℤ)) ∧
  (∀ index, |sources index| ≤ GaussianSource.legCutoff cutoffScale parameter)

/-- The actual finite clipped source and the two physical anchor intervals
satisfy all primary inverse estimates, with explicit constants. -/
theorem base_sign_estimates_eventually {σ τ : ℕ → Type*}
    [∀ parameter, Fintype (σ parameter)] [∀ parameter, Fintype (τ parameter)]
    (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (boundary : ℕ → ℤ)
    (bodyShifts : (parameter : ℕ) → σ parameter → ℤ)
    (bodyLaw : (parameter : ℕ) → FiniteDist (σ parameter))
    (startsPlus startsMinus sources : (parameter : ℕ) → τ parameter → ℤ)
    (sourceLaw : (parameter : ℕ) → FiniteDist (τ parameter))
    (hsupport : ∀ᶠ parameter in atTop,
      PhysicalSupports parameter cutoffScale (boundary parameter)
        (startsPlus parameter) (startsMinus parameter) (sources parameter)) :
    ∀ᶠ parameter in atTop,
      let primary := basePrimary parameter cutoffScale (boundary parameter)
        (bodyShifts parameter) (bodyLaw parameter) (startsPlus parameter) (startsMinus parameter)
        (sources parameter) (sourceLaw parameter)
      let response := signResponse parameter cutoffScale (boundary parameter)
        (startsPlus parameter) (startsMinus parameter) (sources parameter) (sourceLaw parameter)
      (∀ color, 1 / (2 * (Parameters.modulus parameter : ℝ)) ≤ primary color) ∧
      (∀ color, |response color| ≤ GaussianSource.v7Activation cutoffScale parameter * primary color) ∧
      (∑ color, |response color|) ≤ 32 * ((Parameters.anchorWidth parameter : ℝ) / Parameters.modulus parameter) ∧
      (∑ color, response color) = 0 := by
  have hb := hsupport.mono fun _ h => h.1
  have hp := hsupport.mono fun _ h => And.intro h.1 (And.intro h.2.1 h.2.2.2)
  have hm := hsupport.mono fun _ h => And.intro h.1 (And.intro h.2.2.1 h.2.2.2)
  have hlowerPlus := v7_actualBasePrimary_lower_eventually cutoffScale hscale boundary bodyShifts bodyLaw
    startsPlus sources sourceLaw hp
  have hlowerMinus := v7_actualBasePrimary_lower_eventually cutoffScale hscale boundary bodyShifts bodyLaw
    startsMinus sources sourceLaw hm
  filter_upwards [hsupport, hlowerPlus, hlowerMinus,
    v7_primaryCalibrationLoss_eventually cutoffScale hscale boundary hb,
    v7_primaryCalibration_clearance_eventually cutoffScale hscale boundary hb,
    v7_anchor_margin_eventually (21 + cutoffScale), eventually_ge_atTop 2]
    with parameter hs hp hm hloss hclear hanchor hlarge
  dsimp only
  have hx : 0 < Parameters.security parameter := lt_of_lt_of_le (by decide : 0 < 2) (Parameters.security_ge_two parameter)
  have hwidth : Parameters.anchorWidth parameter ≠ 0 := pow_ne_zero _ (ne_of_gt hx)
  have hq : (0 : ℤ) < Parameters.modulus parameter := by exact_mod_cast (Parameters.modulus_prime parameter).pos
  have hlegs : 0 < (Parameters.legs parameter : ℝ) := by unfold Parameters.legs; positivity
  have ha : 0 < GaussianSource.v7Activation cutoffScale parameter :=
    GaussianSource.activation_positive _ _ _ _ (GaussianSource.legFeatureCount_positive cutoffScale parameter hscale (by omega))
  have haUpper : GaussianSource.v7Activation cutoffScale parameter ≤ 1 / 2 :=
    (GaussianSource.activation_le_one_hundredth _ _ _ _).trans (by norm_num)
  have hpopulation : (Parameters.bodies parameter : ℝ) + 2 * Parameters.legs parameter = Parameters.dimension parameter := by
    exact_mod_cast Parameters.population_identity parameter
  have hclearance : 2 * boundary parameter + 3 * (Parameters.anchorWidth parameter : ℤ) +
      GaussianSource.legCutoff cutoffScale parameter < Parameters.modulus parameter := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro color
    unfold basePrimary
    rw [TrimmedSlice.actualFairBasePrimary_eq_average]
    linarith [hp color.val, hm color.val]
  · intro color
    have hh := TrimmedSlice.actualSignResponse_domination (Parameters.modulus parameter)
      (Parameters.safeMargin parameter) (boundary parameter) (3 * Parameters.anchorWidth parameter)
      (GaussianSource.legCutoff cutoffScale parameter) (Parameters.anchorWidth parameter)
      (Parameters.bodies parameter) (Parameters.legs parameter) (GaussianSource.v7Activation cutoffScale parameter)
      (bodyShifts parameter) (bodyLaw parameter).weight (startsPlus parameter) (startsMinus parameter)
      (sources parameter) (sourceLaw parameter).weight hq hlegs (Nat.cast_nonneg _) ha haUpper
      (by positivity) hs.1.1 (by positivity) (by positivity) hwidth
      (by have hh := Parameters.anchor_clearance parameter; omega) hclear.1 hclear.2
      (bodyLaw parameter).nonneg (bodyLaw parameter).sum_one (sourceLaw parameter).nonneg
      (sourceLaw parameter).sum_one hs.2.1 hs.2.2.1 hs.2.2.2
      (by simpa only [Int.cast_natCast, Int.cast_mul, Int.cast_ofNat, hpopulation] using hloss) color.val
    simpa only [basePrimary, signResponse, Int.cast_natCast] using hh
  · have hh := TrimmedSlice.actualSignResponse_palette_l1_le (Parameters.modulus parameter)
      (boundary parameter) (3 * Parameters.anchorWidth parameter) (GaussianSource.legCutoff cutoffScale parameter)
      (Parameters.anchorWidth parameter) hwidth (startsPlus parameter) (startsMinus parameter)
      (sources parameter) (sourceLaw parameter).weight (GaussianSource.v7Activation cutoffScale parameter)
      (sourceLaw parameter).nonneg (sourceLaw parameter).sum_one hs.1.1 (by positivity) (by positivity)
      ha.le (haUpper.trans (by norm_num)) hs.2.1 hs.2.2.1 hs.2.2.2 hclearance
    have hcutoff : (GaussianSource.legCutoff cutoffScale parameter : ℝ) ≤
        (cutoffScale + 1) * (Parameters.security parameter : ℝ) ^ 2 := by
      simpa only [Parameters.security_eq parameter hlarge] using
        GaussianSource.legCutoff_le_quadratic cutoffScale parameter hscale (by omega)
    have hbUpper : (boundary parameter : ℝ) ≤ 20 * (Parameters.security parameter : ℝ) ^ 2 := by exact_mod_cast hs.1.2
    have hsmall : (GaussianSource.legCutoff cutoffScale parameter : ℝ) + 2 * boundary parameter ≤
        Parameters.anchorWidth parameter := by
      simp only [Parameters.safeMargin, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] at hanchor
      nlinarith only [hanchor, hcutoff, hbUpper]
    calc
      _ ≤ 8 * ((3 * (Parameters.anchorWidth parameter : ℤ) : ℝ) +
        GaussianSource.legCutoff cutoffScale parameter + 2 * boundary parameter) / Parameters.modulus parameter := by
        simpa only [signResponse, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast] using hh
      _ ≤ 32 * ((Parameters.anchorWidth parameter : ℝ) / Parameters.modulus parameter) := by
        simp only [Int.cast_natCast]
        apply (div_le_div_of_nonneg_right (by linarith :
          8 * (3 * (Parameters.anchorWidth parameter : ℝ) + GaussianSource.legCutoff cutoffScale parameter + 2 * boundary parameter) ≤
          32 * (Parameters.anchorWidth parameter : ℝ)) (Nat.cast_nonneg _)).trans_eq
        ring
  · exact TrimmedSlice.actualSignResponse_palette_mass (Parameters.modulus parameter)
      (boundary parameter) (3 * Parameters.anchorWidth parameter) (GaussianSource.legCutoff cutoffScale parameter)
      (Parameters.anchorWidth parameter) hwidth (startsPlus parameter) (startsMinus parameter)
      (sources parameter) (sourceLaw parameter).weight (GaussianSource.v7Activation cutoffScale parameter)
      (sourceLaw parameter).sum_one hs.1.1 (by positivity) hs.2.1 hs.2.2.1 hs.2.2.2 hclearance

end V7Calibration
end AFT
