import AFT.FinitePrimaryInverse
import AFT.Parameters
import AFT.ActivationParameters

/-!
# V7 parameter powers imply eventual primary-inverse smallness

The numerical inverse condition is discharged using the actual modulus and
anchor-width definitions. The remaining model inputs are the calibrated
sign-profile bounds and the weaker activation estimate `rho ≥ security⁻⁵`;
these are explicit probability estimates, not inverse-existence premises.
-/

namespace AFT

open Filter
open scoped Topology BigOperators

noncomputable def primaryRankEnvelope (signConstant l1Constant security : ℝ) : ℝ :=
  1 + Real.sqrt (4 * signConstant * l1Constant / security ^ 3) +
    4 * signConstant / security ^ 15

noncomputable def primaryTranslationEnvelope (shiftConstant lowerConstant security : ℝ) : ℝ :=
  Real.sqrt ((4 * shiftConstant / lowerConstant) / security ^ 22) +
    (4 / lowerConstant) / security ^ 7

section ScalarBounds

variable {ι : Type*} [Fintype ι]

theorem calibrated_sign_small_of_power_bounds (security activation l1Constant : ℝ)
    (signProfile : ι → ℝ) (hsecurity : 0 < security)
    (hactivation : 1 / security ^ 5 ≤ activation)
    (hl1 : (∑ color, |signProfile color|) ≤ l1Constant / security ^ 8)
    (hsmall : l1Constant / security ^ 3 ≤ 1 / 2) :
    (∑ color, |signProfile color|) ≤ activation / 2 := by
  have hscale : l1Constant / security ^ 8 =
      (l1Constant / security ^ 3) * (1 / security ^ 5) := by field_simp
  calc
    _ ≤ l1Constant / security ^ 8 := hl1
    _ = _ := hscale
    _ ≤ (1 / 2 : ℝ) * (1 / security ^ 5) :=
      mul_le_mul_of_nonneg_right hsmall (by positivity)
    _ ≤ _ := by linarith

theorem rankInverseActivity_le_envelope (security rate activation signConstant l1Constant : ℝ)
    (signProfile sign : ι → ℝ)
    (hsecurity : 0 < security) (hrate : 0 ≤ rate) (hrateBound : rate ≤ 2 / security ^ 15)
    (hactivation : 1 / security ^ 5 ≤ activation)
    (hsignConstant : 0 ≤ signConstant) (hl1Constant : 0 ≤ l1Constant)
    (hsign : ∀ color, |sign color| ≤ 1)
    (hl1 : (∑ color, |signProfile color|) ≤ l1Constant / security ^ 8)
    (hsmall : l1Constant / security ^ 3 ≤ 1 / 2) :
    rankInverseActivityConstant rate activation (signConstant * activation) signProfile sign ≤
      primaryRankEnvelope signConstant l1Constant security := by
  let mass := ∑ color, |signProfile color|
  let denominator := activation + signFunctional sign signProfile
  have hactivationPos : 0 < activation := lt_of_lt_of_le (by positivity) hactivation
  have hmass : 0 ≤ mass := Finset.sum_nonneg fun color _ => abs_nonneg _
  have hmassSmall : mass ≤ activation / 2 :=
    calibrated_sign_small_of_power_bounds security activation l1Constant signProfile
      hsecurity hactivation hl1 hsmall
  have hsignmass := signFunctional_abs_le_l1 sign signProfile hsign
  have hdenLower : activation / 2 ≤ denominator := by
    have h := (abs_le.mp hsignmass).1
    dsimp [denominator, mass] at *
    linarith
  have hdenPos : 0 < denominator := (half_pos hactivationPos).trans_le hdenLower
  have hratio : mass / activation ≤ l1Constant / security ^ 3 := by
    calc
      _ ≤ (l1Constant / security ^ 8) / activation :=
        div_le_div_of_nonneg_right hl1 (le_of_lt hactivationPos)
      _ ≤ (l1Constant / security ^ 8) / (1 / security ^ 5) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hactivation
      _ = _ := by field_simp
  have hsquare : signConstant * activation * mass / denominator ^ 2 ≤
      4 * signConstant * l1Constant / security ^ 3 := by
    calc
      _ ≤ signConstant * activation * mass / (activation / 2) ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos (half_pos hactivationPos))
          (by nlinarith)
      _ = (4 * signConstant) * (mass / activation) := by field_simp; ring
      _ ≤ (4 * signConstant) * (l1Constant / security ^ 3) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = _ := by ring
  have hrow : (signConstant * activation) / |denominator| ≤ 2 * signConstant := by
    rw [abs_of_pos hdenPos]
    apply (div_le_iff₀ hdenPos).mpr
    nlinarith [mul_le_mul_of_nonneg_left hdenLower hsignConstant]
  have hrowRate : rate * ((signConstant * activation) / |denominator|) ≤
      4 * signConstant / security ^ 15 := by
    calc
      _ ≤ rate * (2 * signConstant) := mul_le_mul_of_nonneg_left hrow hrate
      _ ≤ (2 / security ^ 15) * (2 * signConstant) :=
        mul_le_mul_of_nonneg_right hrateBound (by positivity)
      _ = _ := by ring
  have hsqrt := Real.sqrt_le_sqrt hsquare
  change 1 + Real.sqrt (signConstant * activation * mass / denominator ^ 2) +
      rate * (signConstant * activation / |denominator|) ≤ _
  unfold primaryRankEnvelope
  linarith

theorem intervalTranslationActivity_le_envelope (security modulus rate shiftConstant lowerConstant : ℝ)
    (width : ℕ) (hsecurity : 0 < security) (hmodulus : 0 < modulus)
    (hmodulusBound : modulus ≤ 2 * security ^ 40)
    (hwidth : (width : ℝ) = security ^ 32)
    (hrateBound : rate ≤ 2 / security ^ 15)
    (hshiftConstant : 0 ≤ shiftConstant) (hlowerConstant : 0 < lowerConstant) :
    intervalTranslationActivityConstant rate (shiftConstant * security ^ 2) width
      (lowerConstant / modulus) ≤ primaryTranslationEnvelope shiftConstant lowerConstant security := by
  have hsquare : 2 * (shiftConstant * security ^ 2) /
      ((width : ℝ) ^ 2 * (lowerConstant / modulus)) ≤
      (4 * shiftConstant / lowerConstant) / security ^ 22 := by
    calc
      _ = (2 * shiftConstant / lowerConstant) * modulus / security ^ 62 := by
        rw [hwidth]
        field_simp
      _ ≤ (2 * shiftConstant / lowerConstant) * (2 * security ^ 40) / security ^ 62 := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hmodulusBound (by positivity)) (by positivity)
      _ = _ := by field_simp; ring
  have hrow : rate * (1 / ((width : ℝ) * (lowerConstant / modulus))) ≤
      (4 / lowerConstant) / security ^ 7 := by
    calc
      _ = (rate * modulus) / (security ^ 32 * lowerConstant) := by
        rw [hwidth]
        field_simp
      _ ≤ ((2 / security ^ 15) * (2 * security ^ 40)) / (security ^ 32 * lowerConstant) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul hrateBound hmodulusBound (le_of_lt hmodulus) (by positivity)) (by positivity)
      _ = _ := by field_simp; ring
  have hsqrt := Real.sqrt_le_sqrt hsquare
  unfold intervalTranslationActivityConstant primaryTranslationEnvelope
  linarith

end ScalarBounds

/-- The actual `max 2 parameter` security value diverges. -/
theorem Parameters.security_tendsto : Tendsto Parameters.security atTop atTop :=
  tendsto_atTop_mono (fun parameter => le_max_right 2 parameter) tendsto_id

theorem primaryRankEnvelope_tendsto (signConstant l1Constant : ℝ) :
    Tendsto (fun parameter => primaryRankEnvelope signConstant l1Constant
      (Parameters.security parameter)) atTop (𝓝 1) := by
  have hfirst := ((tendsto_const_div_pow (4 * signConstant * l1Constant) 3 (by decide)).comp
    Parameters.security_tendsto).sqrt
  have hsecond := (tendsto_const_div_pow (4 * signConstant) 15 (by decide)).comp
    Parameters.security_tendsto
  simpa only [primaryRankEnvelope, Real.sqrt_zero, add_zero] using
    (tendsto_const_nhds.add hfirst).add hsecond

theorem primaryTranslationEnvelope_tendsto (shiftConstant lowerConstant : ℝ) :
    Tendsto (fun parameter => primaryTranslationEnvelope shiftConstant lowerConstant
      (Parameters.security parameter)) atTop (𝓝 0) := by
  have hfirst := ((tendsto_const_div_pow (4 * shiftConstant / lowerConstant) 22 (by decide)).comp
    Parameters.security_tendsto).sqrt
  have hsecond := (tendsto_const_div_pow (4 / lowerConstant) 7 (by decide)).comp
    Parameters.security_tendsto
  simpa only [primaryTranslationEnvelope, Real.sqrt_zero, add_zero] using hfirst.add hsecond

theorem v7_primary_envelopes_eventually_small (signConstant l1Constant shiftConstant lowerConstant : ℝ) :
    ∀ᶠ parameter in atTop,
      primaryRankEnvelope signConstant l1Constant (Parameters.security parameter) *
        primaryTranslationEnvelope shiftConstant lowerConstant (Parameters.security parameter) < 1 := by
  have ht := (primaryRankEnvelope_tendsto signConstant l1Constant).mul
    (primaryTranslationEnvelope_tendsto shiftConstant lowerConstant)
  exact ht.eventually (gt_mem_nhds (by norm_num : (1 : ℝ) * 0 < 1))

/-- The specified anchor width and Bertrand modulus give exactly the
`security⁻⁸` L1 scale used above. -/
theorem v7_anchor_ratio_bound (parameter : ℕ) :
    (Parameters.anchorWidth parameter : ℝ) / Parameters.modulus parameter ≤
      1 / (Parameters.security parameter : ℝ) ^ 8 := by
  have hsecurity : 0 < (Parameters.security parameter : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2) (Parameters.security_ge_two parameter)
  have hmodulus : (Parameters.security parameter : ℝ) ^ 40 ≤ Parameters.modulus parameter := by
    exact_mod_cast (Parameters.modulus_bounds parameter).1
  calc
    _ ≤ (Parameters.anchorWidth parameter : ℝ) / (Parameters.security parameter : ℝ) ^ 40 :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) hmodulus
    _ = _ := by
      simp only [Parameters.anchorWidth, Nat.cast_pow]
      field_simp

/-- Every retained primary pool containing at least half of the actual
`security^30` legs has the inverse square-root scale used in the activity. -/
theorem v7_primary_pool_rate_bound (parameter pool : ℕ)
    (hpool : Parameters.legs parameter ≤ 2 * pool) :
    0 < 1 / Real.sqrt (pool : ℝ) ∧
      1 / Real.sqrt (pool : ℝ) ≤ 2 / (Parameters.security parameter : ℝ) ^ 15 := by
  have hsecurity : 0 < (Parameters.security parameter : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2) (Parameters.security_ge_two parameter)
  have hpoolReal : (Parameters.security parameter : ℝ) ^ 30 ≤ 2 * (pool : ℝ) := by
    exact_mod_cast hpool
  have hpoolPos : 0 < (pool : ℝ) := by
    have hh : 0 < (Parameters.security parameter : ℝ) ^ 30 := by positivity
    linarith
  have hsqrt : 0 < Real.sqrt (pool : ℝ) := Real.sqrt_pos.mpr hpoolPos
  have hpower : ((Parameters.security parameter : ℝ) ^ 15) ^ 2 =
      (Parameters.security parameter : ℝ) ^ 30 := by ring
  have hcompare : (Parameters.security parameter : ℝ) ^ 15 ≤ 2 * Real.sqrt (pool : ℝ) := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [hpower, mul_pow, Real.sq_sqrt (le_of_lt hpoolPos)]
    nlinarith
  refine ⟨by positivity, ?_⟩
  exact (div_le_div_iff₀ hsqrt (by positivity)).mpr (by simpa using hcompare)

/-- The true width eventually covers the prescribed safe margin plus any
fixed multiple of the source displacement scale. -/
theorem v7_anchor_margin_eventually (shiftConstant : ℝ) :
    ∀ᶠ parameter in atTop,
      (Parameters.safeMargin parameter : ℝ) +
          shiftConstant * (Parameters.security parameter : ℝ) ^ 2 ≤
        Parameters.anchorWidth parameter := by
  have ht := (tendsto_const_div_pow (20 + shiftConstant) 30 (by decide)).comp
    Parameters.security_tendsto
  have hsmall : ∀ᶠ parameter in atTop,
      (20 + shiftConstant) / (Parameters.security parameter : ℝ) ^ 30 < 1 :=
    ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hsmall] with parameter hsmall
  have hsecurity : 0 < (Parameters.security parameter : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2) (Parameters.security_ge_two parameter)
  have hnum : 20 + shiftConstant ≤ (Parameters.security parameter : ℝ) ^ 30 :=
    ((div_lt_iff₀ (by positivity)).mp hsmall).le.trans_eq (one_mul _)
  have hh := mul_le_mul_of_nonneg_right hnum (sq_nonneg (Parameters.security parameter : ℝ))
  simp only [Parameters.safeMargin, Parameters.anchorWidth, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_pow]
  nlinarith [show (Parameters.security parameter : ℝ) ^ 30 *
      (Parameters.security parameter : ℝ) ^ 2 =
        (Parameters.security parameter : ℝ) ^ 32 by ring]

/-- After the actual V7 parameter substitution, both conditions needed by
`finiteIntervalPrimary_inverse_exists` hold eventually. The palette may
grow with the actual prime modulus. The premises are the local calibration
estimates; neither smallness of the inverse operator nor its existence is
assumed. -/
theorem v7_primary_inverse_conditions_eventually {palette : ℕ → Type*}
    [∀ parameter, Fintype (palette parameter)]
    (activation rate : ℕ → ℝ)
    (signProfile sign : (parameter : ℕ) → palette parameter → ℝ)
    (signConstant l1Constant shiftConstant lowerConstant : ℝ)
    (hsignConstant : 0 ≤ signConstant) (hl1Constant : 0 ≤ l1Constant)
    (hshiftConstant : 0 ≤ shiftConstant) (hlowerConstant : 0 < lowerConstant)
    (hcalibrated : ∀ᶠ parameter in atTop,
      1 / (Parameters.security parameter : ℝ) ^ 5 ≤ activation parameter ∧
      0 ≤ rate parameter ∧ rate parameter ≤ 2 / (Parameters.security parameter : ℝ) ^ 15 ∧
      (∀ color, |sign parameter color| ≤ 1) ∧
      (∑ color, |signProfile parameter color|) ≤
        l1Constant * ((Parameters.anchorWidth parameter : ℝ) / Parameters.modulus parameter)) :
    ∀ᶠ parameter in atTop,
      (∑ color, |signProfile parameter color|) < activation parameter ∧
      rankInverseActivityConstant (rate parameter) (activation parameter)
        (signConstant * activation parameter) (signProfile parameter) (sign parameter) *
      intervalTranslationActivityConstant (rate parameter)
        (shiftConstant * (Parameters.security parameter : ℝ) ^ 2)
        (Parameters.anchorWidth parameter) (lowerConstant / Parameters.modulus parameter) < 1 := by
  have htiny : ∀ᶠ parameter in atTop,
      l1Constant / (Parameters.security parameter : ℝ) ^ 3 < 1 / 2 := by
    have ht := (tendsto_const_div_pow l1Constant 3 (by decide)).comp Parameters.security_tendsto
    exact ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hcalibrated, htiny,
    v7_primary_envelopes_eventually_small signConstant l1Constant shiftConstant lowerConstant]
    with parameter hcal hsmall hproduct
  obtain ⟨hactivation, hrate, hrateBound, hsign, hl1⟩ := hcal
  have hsecurity : 0 < (Parameters.security parameter : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2) (Parameters.security_ge_two parameter)
  have hmodulus : 0 < (Parameters.modulus parameter : ℝ) := by
    exact_mod_cast (Parameters.modulus_prime parameter).pos
  have hmodulusBound : (Parameters.modulus parameter : ℝ) ≤
      2 * (Parameters.security parameter : ℝ) ^ 40 := by
    exact_mod_cast (Parameters.modulus_bounds parameter).2
  have hwidth : (Parameters.anchorWidth parameter : ℝ) =
      (Parameters.security parameter : ℝ) ^ 32 := by simp [Parameters.anchorWidth]
  have hl1Power : (∑ color, |signProfile parameter color|) ≤
      l1Constant / (Parameters.security parameter : ℝ) ^ 8 := by
    have hh := hl1.trans (mul_le_mul_of_nonneg_left (v7_anchor_ratio_bound parameter) hl1Constant)
    simpa only [mul_one_div] using hh
  have hactivationPos : 0 < activation parameter := lt_of_lt_of_le (by positivity) hactivation
  have hsignSmall := calibrated_sign_small_of_power_bounds (Parameters.security parameter)
    (activation parameter) l1Constant (signProfile parameter) hsecurity hactivation hl1Power hsmall.le
  constructor
  · exact hsignSmall.trans_lt (by linarith)
  · have hrank := rankInverseActivity_le_envelope (Parameters.security parameter)
      (rate parameter) (activation parameter) signConstant l1Constant (signProfile parameter)
      (sign parameter) hsecurity hrate hrateBound hactivation hsignConstant hl1Constant hsign
      hl1Power hsmall.le
    have herror := intervalTranslationActivity_le_envelope (Parameters.security parameter)
      (Parameters.modulus parameter) (rate parameter) shiftConstant lowerConstant
      (Parameters.anchorWidth parameter) hsecurity hmodulus hmodulusBound hwidth hrateBound
      hshiftConstant hlowerConstant
    have herrorNonneg : 0 ≤ intervalTranslationActivityConstant (rate parameter)
        (shiftConstant * (Parameters.security parameter : ℝ) ^ 2)
        (Parameters.anchorWidth parameter) (lowerConstant / Parameters.modulus parameter) := by
      unfold intervalTranslationActivityConstant
      positivity
    have hrankNonneg : 0 ≤ primaryRankEnvelope signConstant l1Constant (Parameters.security parameter) := by
      unfold primaryRankEnvelope
      positivity
    exact (mul_le_mul hrank herror herrorNonneg hrankNonneg).trans_lt hproduct

/-- The concrete clipped-Gaussian activation and every retained primary
pool discharge both analytic scalar assumptions in the inverse condition. -/
theorem v7_actual_primary_inverse_conditions_eventually {palette : ℕ → Type*}
    [∀ parameter, Fintype (palette parameter)]
    (cutoffScale : ℝ) (hcutoffScale : 1 ≤ cutoffScale) (pool : ℕ → ℕ)
    (signProfile sign : (parameter : ℕ) → palette parameter → ℝ)
    (signConstant l1Constant shiftConstant lowerConstant : ℝ)
    (hsignConstant : 0 ≤ signConstant) (hl1Constant : 0 ≤ l1Constant)
    (hshiftConstant : 0 ≤ shiftConstant) (hlowerConstant : 0 < lowerConstant)
    (hcalibrated : ∀ᶠ parameter in atTop,
      Parameters.legs parameter ≤ 2 * pool parameter ∧
      (∀ color, |sign parameter color| ≤ 1) ∧
      (∑ color, |signProfile parameter color|) ≤
        l1Constant * ((Parameters.anchorWidth parameter : ℝ) / Parameters.modulus parameter)) :
    ∀ᶠ parameter in atTop,
      (∑ color, |signProfile parameter color|) < GaussianSource.v7Activation cutoffScale parameter ∧
      rankInverseActivityConstant (1 / Real.sqrt (pool parameter : ℝ))
        (GaussianSource.v7Activation cutoffScale parameter)
        (signConstant * GaussianSource.v7Activation cutoffScale parameter)
        (signProfile parameter) (sign parameter) *
      intervalTranslationActivityConstant (1 / Real.sqrt (pool parameter : ℝ))
        (shiftConstant * (Parameters.security parameter : ℝ) ^ 2)
        (Parameters.anchorWidth parameter) (lowerConstant / Parameters.modulus parameter) < 1 := by
  apply v7_primary_inverse_conditions_eventually
    (GaussianSource.v7Activation cutoffScale) (fun parameter => 1 / Real.sqrt (pool parameter : ℝ))
    signProfile sign signConstant l1Constant shiftConstant lowerConstant
    hsignConstant hl1Constant hshiftConstant hlowerConstant
  filter_upwards [hcalibrated, GaussianSource.v7Activation_lower_eventually cutoffScale hcutoffScale,
    eventually_ge_atTop 2] with parameter hcal hactivation hlarge
  have hrate := v7_primary_pool_rate_bound parameter (pool parameter) hcal.1
  refine ⟨?_, hrate.1.le, hrate.2, hcal.2.1, hcal.2.2⟩
  simpa only [Parameters.security_eq parameter hlarge, one_div] using hactivation

end AFT
