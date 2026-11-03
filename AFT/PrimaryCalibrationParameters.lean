import AFT.PrimaryCalibration
import AFT.PrimaryParameterBounds

/-!
# Actual V7 powers discharge the primary positivity losses
-/

namespace AFT

open Filter
open scoped Topology BigOperators

noncomputable def primaryCalibrationEnvelope (cutoffConstant security : ℝ) : ℝ :=
  92 / security ^ 3 + 160 / security ^ 33 + 4 * cutoffConstant / security ^ 25

/-- A coarse inverse-fifth-power activation estimate already suffices for
all three primary-positivity losses. -/
theorem primaryCalibrationLoss_power_bound
    (security modulus activation deleted cutoff cutoffConstant : ℝ)
    (hsecurity : 0 < security) (hmodulus : security ^ 40 ≤ modulus)
    (hactivation : 1 / security ^ 5 ≤ activation)
    (hdeleted : deleted ≤ 3 * security ^ 32 + 40 * security ^ 2)
    (hcutoff : cutoff ≤ cutoffConstant * security ^ 2)
    (hconstant : 0 ≤ cutoffConstant) :
    primaryCalibrationLoss modulus (modulus * security ^ 20) (security ^ 30) activation
      (20 * security ^ 2) deleted cutoff (security ^ 32) ≤ primaryCalibrationEnvelope cutoffConstant security := by
  have hmodulusPos : 0 < modulus := lt_of_lt_of_le (by positivity) hmodulus
  have hactivationPos : 0 < activation := lt_of_lt_of_le (by positivity) hactivation
  have hinv : 1 / activation ≤ security ^ 5 := by
    have hh := one_div_le_one_div_of_le (by positivity : 0 < 1 / security ^ 5) hactivation
    simpa only [one_div_one_div] using hh
  have hfirst : 4 * (modulus * security ^ 20) * (20 * security ^ 2) /
      (security ^ 30 * activation * modulus) ≤ 80 / security ^ 3 := by
    calc
      _ = (80 / security ^ 8) * (1 / activation) := by field_simp; ring
      _ ≤ (80 / security ^ 8) * security ^ 5 := mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = _ := by field_simp
  have hdeletedRatio : 4 * deleted / modulus ≤
      4 * (3 * security ^ 32 + 40 * security ^ 2) / security ^ 40 := by
    calc
      _ ≤ 4 * (3 * security ^ 32 + 40 * security ^ 2) / modulus :=
        div_le_div_of_nonneg_right (by linarith) hmodulusPos.le
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) hmodulus
  have hsecond : 4 * deleted / (activation * modulus) ≤
      12 / security ^ 3 + 160 / security ^ 33 := by
    calc
      _ = (4 * deleted / modulus) * (1 / activation) := by ring
      _ ≤ (4 * (3 * security ^ 32 + 40 * security ^ 2) / security ^ 40) * security ^ 5 :=
        mul_le_mul hdeletedRatio hinv (by positivity) (by positivity)
      _ = _ := by field_simp; ring
  have hthird : 4 * cutoff / (activation * security ^ 32) ≤
      4 * cutoffConstant / security ^ 25 := by
    calc
      _ = (4 * cutoff / security ^ 32) * (1 / activation) := by ring
      _ ≤ (4 * (cutoffConstant * security ^ 2) / security ^ 32) * security ^ 5 :=
        mul_le_mul (div_le_div_of_nonneg_right (by linarith) (by positivity)) hinv
          (by positivity) (by positivity)
      _ = _ := by field_simp
  unfold primaryCalibrationLoss primaryCalibrationEnvelope
  exact (add_le_add (add_le_add hfirst hsecond) hthird).trans_eq (by ring)

theorem primaryCalibrationEnvelope_tendsto (cutoffConstant : ℝ) :
    Tendsto (fun parameter => primaryCalibrationEnvelope cutoffConstant (Parameters.security parameter))
      atTop (𝓝 0) := by
  have hfirst := (tendsto_const_div_pow (92 : ℝ) 3 (by decide)).comp Parameters.security_tendsto
  have hsecond := (tendsto_const_div_pow (160 : ℝ) 33 (by decide)).comp Parameters.security_tendsto
  have hthird := (tendsto_const_div_pow (4 * cutoffConstant) 25 (by decide)).comp Parameters.security_tendsto
  simpa only [primaryCalibrationEnvelope, zero_add] using (hfirst.add hsecond).add hthird

/-- The actual clipped source's activation is at most its mark probability. -/
theorem GaussianSource.activation_le_one (firstWidth secondWidth : ℝ) (cutoff featureCount : ℕ) :
    GaussianSource.activation firstWidth secondWidth cutoff featureCount ≤ 1 := by
  by_cases hfeatures : featureCount = 0
  · simp [GaussianSource.activation, hfeatures]
  have hfeatureReal : (1 : ℝ) ≤ featureCount := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hfeatures
  have hpair : ((GaussianSource.windowGaussian firstWidth cutoff).prod
      (GaussianSource.windowGaussian secondWidth cutoff)).weight
      (GaussianSource.windowZero cutoff, GaussianSource.windowZero cutoff) ≤ 1 := by
    let distribution := (GaussianSource.windowGaussian firstWidth cutoff).prod
      (GaussianSource.windowGaussian secondWidth cutoff)
    have hh := Finset.single_le_sum (fun index (_ : index ∈ Finset.univ) => distribution.nonneg index)
      (Finset.mem_univ (GaussianSource.windowZero cutoff, GaussianSource.windowZero cutoff))
    simpa only [distribution.sum_one] using hh
  have hmark : 1 / (100 * (featureCount : ℝ)) ≤ 1 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  unfold GaussianSource.activation
  exact (mul_le_mul_of_nonneg_left hpair (by positivity)).trans (by simpa only [mul_one] using hmark)

/-- The strict integer cutoff grows more slowly than the coarse quadratic
source-shift scale used in the calibration estimates. -/
theorem GaussianSource.legCutoff_le_quadratic (cutoffScale : ℝ) (parameter : ℕ)
    (hscale : 1 ≤ cutoffScale) (hp : 1 ≤ parameter) :
    (GaussianSource.legCutoff cutoffScale parameter : ℝ) ≤ (cutoffScale + 1) * (parameter : ℝ) ^ 2 := by
  have hpReal : (1 : ℝ) ≤ parameter := by exact_mod_cast hp
  have hpow : (parameter : ℝ) ^ (9 / 8 : ℝ) ≤ (parameter : ℝ) ^ 2 := by
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hpReal (by norm_num : (9 / 8 : ℝ) ≤ (2 : ℕ))
  have hceil := (Nat.ceil_lt_add_one (show 0 ≤ cutoffScale *
    (parameter : ℝ) ^ (9 / 8 : ℝ) by positivity)).le
  change (⌈cutoffScale * (parameter : ℝ) ^ (9 / 8 : ℝ)⌉₊ : ℝ) ≤ _
  have hmul := mul_le_mul_of_nonneg_left hpow (by linarith : 0 ≤ cutoffScale)
  have hsq : 1 ≤ (parameter : ℝ) ^ 2 := one_le_pow₀ hpReal
  nlinarith

/-- With the actual q,m,d,W, safe margin, source cutoff, and Gaussian
activation, the displayed positivity loss is eventually at most one half.
Only the boundary half-width's prescribed safe-margin bound remains explicit. -/
theorem v7_primaryCalibrationLoss_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (boundary : ℕ → ℤ)
    (hboundary : ∀ᶠ parameter in atTop,
      0 ≤ boundary parameter ∧ boundary parameter ≤ Parameters.safeMargin parameter) :
    ∀ᶠ parameter in atTop,
      primaryCalibrationLoss (Parameters.modulus parameter) (Parameters.dimension parameter)
        (Parameters.legs parameter) (GaussianSource.v7Activation cutoffScale parameter)
        (Parameters.safeMargin parameter)
        (3 * (Parameters.anchorWidth parameter : ℝ) + 2 * boundary parameter)
        (GaussianSource.legCutoff cutoffScale parameter) (Parameters.anchorWidth parameter) ≤ 1 / 2 := by
  have hsmall := (primaryCalibrationEnvelope_tendsto (cutoffScale + 1)).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hboundary, GaussianSource.v7Activation_lower_eventually cutoffScale hscale,
    hsmall, eventually_ge_atTop 2] with parameter hb hactivation hsmall hlarge
  have hsecurity : 0 < (Parameters.security parameter : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2) (Parameters.security_ge_two parameter)
  have hmodulus : (Parameters.security parameter : ℝ) ^ 40 ≤ Parameters.modulus parameter := by
    exact_mod_cast (Parameters.modulus_bounds parameter).1
  have hactivation' : 1 / (Parameters.security parameter : ℝ) ^ 5 ≤
      GaussianSource.v7Activation cutoffScale parameter := by
    simpa only [Parameters.security_eq parameter hlarge, one_div] using hactivation
  have hbNonneg : 0 ≤ (boundary parameter : ℝ) := by exact_mod_cast hb.1
  have hbUpper : (boundary parameter : ℝ) ≤ 20 * (Parameters.security parameter : ℝ) ^ 2 := by
    exact_mod_cast hb.2
  have hcutoff : (GaussianSource.legCutoff cutoffScale parameter : ℝ) ≤
      (cutoffScale + 1) * (Parameters.security parameter : ℝ) ^ 2 := by
    simpa only [Parameters.security_eq parameter hlarge] using
      GaussianSource.legCutoff_le_quadratic cutoffScale parameter hscale (by omega)
  have hh := primaryCalibrationLoss_power_bound (Parameters.security parameter) (Parameters.modulus parameter)
    (GaussianSource.v7Activation cutoffScale parameter)
    (3 * (Parameters.anchorWidth parameter : ℝ) + 2 * boundary parameter)
    (GaussianSource.legCutoff cutoffScale parameter) (cutoffScale + 1)
    hsecurity hmodulus hactivation'
    (by simp only [Parameters.anchorWidth, Nat.cast_pow]; linarith)
    hcutoff (by linarith)
  have hdim : (Parameters.dimension parameter : ℝ) =
      (Parameters.modulus parameter : ℝ) * (Parameters.security parameter : ℝ) ^ 20 := by
    simp [Parameters.dimension, Parameters.meanDensity]
  rw [← hdim] at hh
  simpa only [Parameters.legs, Parameters.safeMargin, Parameters.anchorWidth,
    Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using hh.trans hsmall.le

/-- The actual parameter powers give room for both the body margin and
all trimmed slices, including the exact clipped source cutoff. -/
theorem v7_primaryCalibration_clearance_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (boundary : ℕ → ℤ)
    (hboundary : ∀ᶠ parameter in atTop,
      0 ≤ boundary parameter ∧ boundary parameter ≤ Parameters.safeMargin parameter) :
    ∀ᶠ parameter in atTop,
      (4 * (Parameters.safeMargin parameter : ℤ) ≤ Parameters.modulus parameter) ∧
      2 * (3 * (Parameters.anchorWidth parameter : ℤ) + 2 * boundary parameter +
        GaussianSource.legCutoff cutoffScale parameter) ≤ Parameters.modulus parameter := by
  have hfirst := (tendsto_const_div_pow (6 : ℝ) 8 (by decide)).comp Parameters.security_tendsto
  have hsecond := (tendsto_const_div_pow (80 + 2 * (cutoffScale + 1)) 38 (by decide)).comp Parameters.security_tendsto
  have hsmall := (hfirst.add hsecond).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) + 0 < 1))
  filter_upwards [hboundary, hsmall, eventually_ge_atTop 2] with parameter hb hsmall hlarge
  have hx : 0 < (Parameters.security parameter : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2) (Parameters.security_ge_two parameter)
  have hq : (Parameters.security parameter : ℝ) ^ 40 ≤ Parameters.modulus parameter := by
    exact_mod_cast (Parameters.modulus_bounds parameter).1
  have hbUpper : (boundary parameter : ℝ) ≤ 20 * (Parameters.security parameter : ℝ) ^ 2 := by exact_mod_cast hb.2
  have hcutoff : (GaussianSource.legCutoff cutoffScale parameter : ℝ) ≤
      (cutoffScale + 1) * (Parameters.security parameter : ℝ) ^ 2 := by
    simpa only [Parameters.security_eq parameter hlarge] using
      GaussianSource.legCutoff_le_quadratic cutoffScale parameter hscale (by omega)
  have hpoly : 6 * (Parameters.security parameter : ℝ) ^ 32 +
      (80 + 2 * (cutoffScale + 1)) * (Parameters.security parameter : ℝ) ^ 2 ≤
        (Parameters.security parameter : ℝ) ^ 40 := by
    have hh := mul_le_mul_of_nonneg_right hsmall.le
      (by positivity : 0 ≤ (Parameters.security parameter : ℝ) ^ 40)
    have heq : (6 / (Parameters.security parameter : ℝ) ^ 8 +
        (80 + 2 * (cutoffScale + 1)) / (Parameters.security parameter : ℝ) ^ 38) *
        (Parameters.security parameter : ℝ) ^ 40 =
        6 * (Parameters.security parameter : ℝ) ^ 32 +
          (80 + 2 * (cutoffScale + 1)) * (Parameters.security parameter : ℝ) ^ 2 := by
      field_simp
    simpa only [Function.comp_apply, heq, one_mul] using hh
  have hmargin : 4 * (Parameters.safeMargin parameter : ℝ) ≤ Parameters.modulus parameter := by
    simp only [Parameters.safeMargin, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
    nlinarith [show 0 ≤ (cutoffScale + 1) * (Parameters.security parameter : ℝ) ^ 2 by positivity,
      show 0 ≤ (Parameters.security parameter : ℝ) ^ 32 by positivity]
  have hslice : 2 * (3 * (Parameters.anchorWidth parameter : ℝ) + 2 * boundary parameter +
      GaussianSource.legCutoff cutoffScale parameter) ≤ Parameters.modulus parameter := by
    simp only [Parameters.anchorWidth, Nat.cast_pow]
    linarith
  exact ⟨by exact_mod_cast hmargin, by exact_mod_cast hslice⟩

/-- For the actual V7 populations, cutoff, activation, and finite source
laws, the base primary calibration is eventually uniformly positive.
The premises specify only the physical source supports. -/
theorem v7_actualBasePrimary_lower_eventually {σ τ : ℕ → Type*}
    [∀ parameter, Fintype (σ parameter)] [∀ parameter, Fintype (τ parameter)]
    (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (boundary : ℕ → ℤ)
    (bodyShifts : (parameter : ℕ) → σ parameter → ℤ)
    (bodyLaw : (parameter : ℕ) → FiniteDist (σ parameter))
    (starts sources : (parameter : ℕ) → τ parameter → ℤ)
    (sourceLaw : (parameter : ℕ) → FiniteDist (τ parameter))
    (hmodel : ∀ᶠ parameter in atTop,
      (0 ≤ boundary parameter ∧ boundary parameter ≤ Parameters.safeMargin parameter) ∧
      (∀ index shift, shift ∈ anchorInterval (starts parameter index) (Parameters.anchorWidth parameter) →
        |shift| ≤ 3 * (Parameters.anchorWidth parameter : ℤ)) ∧
      (∀ index, |sources parameter index| ≤ GaussianSource.legCutoff cutoffScale parameter)) :
    ∀ᶠ parameter in atTop, ∀ color : ℤ,
      1 / (2 * (Parameters.modulus parameter : ℝ)) ≤
        TrimmedSlice.actualBasePrimary (Parameters.modulus parameter) (Parameters.safeMargin parameter)
          (boundary parameter) (Parameters.anchorWidth parameter) (Parameters.bodies parameter)
          (Parameters.legs parameter) (GaussianSource.v7Activation cutoffScale parameter)
          (bodyShifts parameter) (bodyLaw parameter).weight (starts parameter) (sources parameter)
          (sourceLaw parameter).weight color := by
  have hb := hmodel.mono fun _ h => h.1
  filter_upwards [hmodel, v7_primaryCalibrationLoss_eventually cutoffScale hscale boundary hb,
    v7_primaryCalibration_clearance_eventually cutoffScale hscale boundary hb,
    eventually_ge_atTop 2] with parameter hmodel hloss hclearance hlarge
  have hp : 1 ≤ parameter := by omega
  have hactivation : 0 < GaussianSource.v7Activation cutoffScale parameter :=
    GaussianSource.activation_positive _ _ _ _ (GaussianSource.legFeatureCount_positive cutoffScale parameter hscale hp)
  have hactivationUpper : GaussianSource.v7Activation cutoffScale parameter ≤ 1 :=
    GaussianSource.activation_le_one _ _ _ _
  have hq : (0 : ℤ) < Parameters.modulus parameter := by exact_mod_cast (Parameters.modulus_prime parameter).pos
  have hx : 0 < Parameters.security parameter := lt_of_lt_of_le (by decide : 0 < 2) (Parameters.security_ge_two parameter)
  have hlegs : 0 < (Parameters.legs parameter : ℝ) := by
    unfold Parameters.legs
    positivity
  have hwidth : Parameters.anchorWidth parameter ≠ 0 := by
    unfold Parameters.anchorWidth
    exact pow_ne_zero _ (ne_of_gt hx)
  have hpopulation : (Parameters.bodies parameter : ℝ) + 2 * Parameters.legs parameter =
      Parameters.dimension parameter := by exact_mod_cast Parameters.population_identity parameter
  intro color
  have hh := TrimmedSlice.actualBasePrimary_lower (Parameters.modulus parameter) (Parameters.safeMargin parameter)
    (boundary parameter) (3 * Parameters.anchorWidth parameter) (GaussianSource.legCutoff cutoffScale parameter)
    (Parameters.anchorWidth parameter) (Parameters.bodies parameter) (Parameters.legs parameter)
    (GaussianSource.v7Activation cutoffScale parameter) (bodyShifts parameter) (bodyLaw parameter).weight
    (starts parameter) (sources parameter) (sourceLaw parameter).weight
    hq hlegs (Nat.cast_nonneg _) hactivation hactivationUpper (by positivity) hmodel.1.1 (by positivity)
    (by positivity) hwidth hclearance.1 hclearance.2 (bodyLaw parameter).nonneg (bodyLaw parameter).sum_one
    (sourceLaw parameter).nonneg (sourceLaw parameter).sum_one hmodel.2.1 hmodel.2.2
    (by simpa only [Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, hpopulation] using hloss) color
  simpa only [Int.cast_natCast] using hh

end AFT
