import AFT.V7BetaRepairBound
import AFT.ActivationUpper

/-! # Actual body mean deficits and finite weighted profile estimates -/

namespace AFT

open scoped BigOperators Classical

section FiniteProfiles

variable {ι : Type*} [Fintype ι]

/-- The optimal uniform L1 bound determined by a probability profile's
pointwise upper bound. No support cardinality is assumed. -/
theorem probability_uniform_l1_le (profile : ι → ℝ) (upper : ℝ)
    (hpositive : 0 < (Fintype.card ι : ℝ))
    (hmass : ∑ color, profile color = 1)
    (hnonneg : ∀ color, 0 ≤ profile color)
    (hupper : ∀ color, profile color ≤ upper)
    (huniform : (Fintype.card ι : ℝ)⁻¹ ≤ upper) :
    (∑ color, |profile color - (Fintype.card ι : ℝ)⁻¹|) ≤
      2 * (1 - (Fintype.card ι : ℝ)⁻¹ / upper) := by
  have hu : 0 < upper := lt_of_lt_of_le (by positivity) huniform
  have hpoint (color : ι) : |profile color - (Fintype.card ι : ℝ)⁻¹| ≤
      profile color + (Fintype.card ι : ℝ)⁻¹ -
        2 * ((Fintype.card ι : ℝ)⁻¹ / upper) * profile color := by
    have hratio : (Fintype.card ι : ℝ)⁻¹ / upper ≤ 1 := (div_le_one hu).mpr huniform
    have hlow : 0 ≤ (Fintype.card ι : ℝ)⁻¹ / upper := by positivity
    apply abs_le.mpr
    constructor
    · nlinarith [mul_le_mul_of_nonneg_right hratio (hnonneg color)]
    · have hh := mul_le_mul_of_nonneg_left (hupper color) hlow
      have heq : ((Fintype.card ι : ℝ)⁻¹ / upper) * upper = (Fintype.card ι : ℝ)⁻¹ := by field_simp
      rw [heq] at hh
      nlinarith
  apply (Finset.sum_le_sum (fun color _ => hpoint color)).trans_eq
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum, hmass]
  field_simp
  ring

/-- The weighted squared profile norm follows from its actual L1 mass and
pointwise relative density; this retains the small fringe-mass gain. -/
theorem profileSquareNorm_le_relative_mul_l1 (primary profile : ι → ℝ) (relative : ℝ)
    (hp : ∀ color, 0 < primary color)
    (hrelative : ∀ color, |profile color| ≤ relative * primary color) :
    profileSquareNorm primary profile ≤ relative * ∑ color, |profile color| := by
  unfold profileSquareNorm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro color _
  apply (div_le_iff₀ (hp color)).mpr
  have hh := mul_le_mul_of_nonneg_left (hrelative color) (abs_nonneg (profile color))
  nlinarith [sq_abs (profile color)]

end FiniteProfiles

namespace TrimmedSlice

theorem actualBasePrimary_retained_lower {σ τ : Type*} [Fintype σ] [Fintype τ]
    (modulus margin boundary shiftBound cutoff : ℤ) (width : ℕ) (bodies legs activation : ℝ)
    (bodyShifts : σ → ℤ) (bodyWeights : σ → ℝ)
    (starts sources : τ → ℤ) (weights : τ → ℝ)
    (hq : 0 < modulus) (hlegs : 0 < legs) (hbodies : 0 ≤ bodies)
    (hactivation : 0 < activation) (hactivationUpper : activation ≤ 1)
    (hmargin : 0 ≤ margin) (hboundary : 0 ≤ boundary) (hshiftBound : 0 ≤ shiftBound)
    (hcutoff : 0 ≤ cutoff) (hwidth : width ≠ 0)
    (hmarginSmall : 4 * margin ≤ modulus) (hdeletedSmall : 2 * (shiftBound + 2 * boundary + cutoff) ≤ modulus)
    (hweights : ∀ index, 0 ≤ weights index) (hmass : ∑ index, weights index = 1)
    (hbound : ∀ index shift, shift ∈ anchorInterval (starts index) width → |shift| ≤ shiftBound)
    (hsources : ∀ index, |sources index| ≤ cutoff)
    (hloss : primaryCalibrationLoss modulus (bodies + 2 * legs) legs activation margin
      ((shiftBound : ℝ) + 2 * boundary) cutoff width ≤ 1 / 2) (color : ℤ) :
    (bodies + legs * activation) / (legs * activation) *
        (1 / ((modulus : ℝ) - 2 * margin) - blurredSafeLaw modulus margin bodyShifts bodyWeights color) +
      1 / (2 * (modulus : ℝ)) ≤ actualBasePrimary modulus margin boundary width bodies legs activation
      bodyShifts bodyWeights starts sources weights color := by
  have hqReal : 0 < (modulus : ℝ) := by exact_mod_cast hq
  have hmarginReal : 0 ≤ (margin : ℝ) := by exact_mod_cast hmargin
  have hboundaryReal : 0 ≤ (boundary : ℝ) := by exact_mod_cast hboundary
  have hshiftReal : 0 ≤ (shiftBound : ℝ) := by exact_mod_cast hshiftBound
  have hcutoffReal : 0 ≤ (cutoff : ℝ) := by exact_mod_cast hcutoff
  have hwidthReal : 0 < (width : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hwidth
  have hmarginSmallReal : 4 * (margin : ℝ) ≤ modulus := by exact_mod_cast hmarginSmall
  have hdeletedSmallReal : 2 * ((shiftBound : ℝ) + 2 * boundary + cutoff) ≤ modulus := by exact_mod_cast hdeletedSmall
  have hunshifted : mixedLaw modulus boundary starts (fun _ => 0) weights width color ≤
      1 / ((modulus : ℝ) - ((shiftBound : ℝ) + 2 * boundary)) := by
    convert mixedLaw_zero_le modulus boundary shiftBound starts weights width hwidth hweights hmass hbound (by omega) color using 1; ring
  have hvariation : |mixedLaw modulus boundary starts sources weights width color -
      mixedLaw modulus boundary starts (fun _ => 0) weights width color| ≤
      (cutoff : ℝ) / ((width : ℝ) * ((modulus : ℝ) - ((shiftBound : ℝ) + 2 * boundary) - cutoff)) := by
    convert mixedLaw_source_variation modulus boundary shiftBound cutoff starts sources weights width hwidth
      hweights hmass hbound hsources (by omega) color using 1; ring
  have hh := basePrimary_scalar_lower modulus bodies legs activation margin
    ((shiftBound : ℝ) + 2 * boundary) cutoff width
    (blurredSafeLaw modulus margin bodyShifts bodyWeights color)
    (mixedLaw modulus boundary starts sources weights width color)
    (mixedLaw modulus boundary starts (fun _ => 0) weights width color)
    hqReal hlegs hbodies hactivation hactivationUpper hmarginReal (by positivity) hcutoffReal hwidthReal
    hmarginSmallReal hdeletedSmallReal hunshifted hvariation
  have hremain : 1 / (2 * (modulus : ℝ)) ≤
      (1 - primaryCalibrationLoss modulus (bodies + 2 * legs) legs activation margin
        ((shiftBound : ℝ) + 2 * boundary) cutoff width) / modulus := by
    have hl : (1 / 2 : ℝ) ≤ 1 - primaryCalibrationLoss modulus (bodies + 2 * legs) legs activation margin
        ((shiftBound : ℝ) + 2 * boundary) cutoff width := by linarith
    convert div_le_div_of_nonneg_right hl hqReal.le using 1; ring
  apply (add_le_add le_rfl hremain).trans
  simpa only [actualBasePrimary, basePrimaryProfile, mul_one_div] using hh

/-- L1 deviation of the actual blurred safe-center law, uniformly in all
allowed shifts and in the source distribution. -/
theorem blurredSafeLaw_palette_l1_le {σ : Type*} [Fintype σ]
    (modulus : ℕ) (margin : ℤ) (shifts : σ → ℤ) (weights : σ → ℝ)
    (hmargin : 0 ≤ margin) (hmass : ∑ index, weights index = 1)
    (hnonneg : ∀ index, 0 ≤ weights index) (hwidth : 2 * margin < modulus)
    (hshift : ∀ index, |shifts index| ≤ margin) :
    (∑ color : Fin modulus, |blurredSafeLaw modulus margin shifts weights color.val -
      (modulus : ℝ)⁻¹|) ≤ 4 * margin / modulus := by
  have hq : 0 < (modulus : ℝ) := by exact_mod_cast (by omega : 0 < modulus)
  have hs : 0 < (modulus : ℝ) - 2 * margin := by exact_mod_cast (sub_pos.mpr hwidth)
  have hm : (0 : ℝ) ≤ margin := by exact_mod_cast hmargin
  have h := probability_uniform_l1_le (fun color : Fin modulus =>
      blurredSafeLaw modulus margin shifts weights color.val)
    (1 / ((modulus : ℝ) - 2 * margin)) (by simpa using hq)
    (blurredSafeLaw_palette_mass modulus margin shifts weights hmass hwidth hshift)
    (by intro color; unfold blurredSafeLaw; exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (hnonneg i) (intervalAnchorLaw_nonneg _ _ _))
    (fun color => by simpa only [Int.cast_natCast] using
      blurredSafeLaw_le modulus margin shifts weights hnonneg hmass hwidth color.val)
    (by simp only [Fintype.card_fin, one_div]; exact inv_anti₀ hs (by linarith))
  simp only [Fintype.card_fin] at h
  convert h using 1
  field_simp
  ring

/-- Averaging the two actual endpoint-sign calibrations retains their
common body deficit rather than discarding it. -/
theorem actualFairBasePrimary_retained_lower {σ τ : Type*} [Fintype σ] [Fintype τ]
    (modulus margin boundary shiftBound cutoff : ℤ) (width : ℕ) (bodies legs activation : ℝ)
    (bodyShifts : σ → ℤ) (bodyWeights : σ → ℝ)
    (startsPlus startsMinus sources : τ → ℤ) (weights : τ → ℝ)
    (hq : 0 < modulus) (hlegs : 0 < legs) (hbodies : 0 ≤ bodies)
    (hactivation : 0 < activation) (hactivationUpper : activation ≤ 1)
    (hmargin : 0 ≤ margin) (hboundary : 0 ≤ boundary) (hshiftBound : 0 ≤ shiftBound)
    (hcutoff : 0 ≤ cutoff) (hwidth : width ≠ 0)
    (hmarginSmall : 4 * margin ≤ modulus) (hdeletedSmall : 2 * (shiftBound + 2 * boundary + cutoff) ≤ modulus)
    (hweights : ∀ index, 0 ≤ weights index) (hmass : ∑ index, weights index = 1)
    (hplus : ∀ index shift, shift ∈ anchorInterval (startsPlus index) width → |shift| ≤ shiftBound)
    (hminus : ∀ index shift, shift ∈ anchorInterval (startsMinus index) width → |shift| ≤ shiftBound)
    (hsources : ∀ index, |sources index| ≤ cutoff)
    (hloss : primaryCalibrationLoss modulus (bodies + 2 * legs) legs activation margin
      ((shiftBound : ℝ) + 2 * boundary) cutoff width ≤ 1 / 2) (color : ℤ) :
    (bodies + legs * activation) / (legs * activation) *
        (1 / ((modulus : ℝ) - 2 * margin) - blurredSafeLaw modulus margin bodyShifts bodyWeights color) +
      1 / (2 * (modulus : ℝ)) ≤ actualFairBasePrimary modulus margin boundary width bodies legs activation
      bodyShifts bodyWeights startsPlus startsMinus sources weights color := by
  have hp := actualBasePrimary_retained_lower modulus margin boundary shiftBound cutoff width bodies legs activation
    bodyShifts bodyWeights startsPlus sources weights hq hlegs hbodies hactivation hactivationUpper
    hmargin hboundary hshiftBound hcutoff hwidth hmarginSmall hdeletedSmall hweights hmass hplus hsources hloss color
  have hm := actualBasePrimary_retained_lower modulus margin boundary shiftBound cutoff width bodies legs activation
    bodyShifts bodyWeights startsMinus sources weights hq hlegs hbodies hactivation hactivationUpper
    hmargin hboundary hshiftBound hcutoff hwidth hmarginSmall hdeletedSmall hweights hmass hminus hsources hloss color
  rw [actualFairBasePrimary_eq_average]
  linarith

end TrimmedSlice

section MeanNorms

variable {ι : Type*} [Fintype ι]

/-- The body/reference mean estimate before substituting parameter powers.
The L1 fringe mass is kept separate from the relative-density budget. -/
theorem body_reference_mean_bounds (body base primary reference : ι → ℝ)
    (uniform upper compensation scale fringe : ℝ)
    (hu : 0 < uniform) (hscale : 0 ≤ scale) (hscaleComp : scale ≤ compensation)
    (hp : ∀ color, 0 < primary color)
    (hlower : ∀ color, uniform / 4 ≤ primary color)
    (hbase : ∀ color, 0 ≤ base color ∧ base color ≤ 2 * primary color)
    (hbody : ∀ color, 0 ≤ body color ∧ body color ≤ upper)
    (hdeficit : ∀ color, upper - body color ≤ 2 * compensation * primary color)
    (hUu : uniform ≤ upper)
    (hmean : ∀ color, reference color = uniform + scale * (primary color - base color))
    (hfringe : (∑ color, |body color - reference color|) ≤ fringe) :
    (∀ color, |body color - reference color| ≤
      (5 * compensation + 4 * (upper - uniform) / uniform) * primary color) ∧
    profileSquareNorm primary (body - reference) ≤
      (5 * compensation + 4 * (upper - uniform) / uniform) * fringe := by
  have hc : 0 ≤ compensation := hscale.trans hscaleComp
  have hdiff0 : 0 ≤ upper - uniform := sub_nonneg.mpr hUu
  have hpoint (color : ι) : |body color - reference color| ≤
      (5 * compensation + 4 * (upper - uniform) / uniform) * primary color := by
    have href : |reference color - uniform| ≤ 3 * compensation * primary color := by
      rw [hmean, add_sub_cancel_left, abs_mul, abs_of_nonneg hscale]
      have hdiff : |primary color - base color| ≤ 3 * primary color := by
        apply abs_le.mpr
        constructor <;> linarith [(hbase color).1, (hbase color).2, hp color]
      have hh := mul_le_mul_of_nonneg_left hdiff hscale
      have ht := mul_le_mul_of_nonneg_right hscaleComp (hp color).le
      nlinarith
    have hconstant : upper - uniform ≤ 4 * (upper - uniform) / uniform * primary color := by
      have hh := mul_le_mul_of_nonneg_left (hlower color) (show 0 ≤ 4 * (upper - uniform) / uniform by positivity)
      have heq : 4 * (upper - uniform) / uniform * (uniform / 4) = upper - uniform := by field_simp
      rw [heq] at hh
      exact hh
    have hb : |body color - uniform| ≤ upper - body color + (upper - uniform) := by
      apply abs_le.mpr
      constructor <;> linarith [(hbody color).2]
    calc
      _ ≤ |body color - uniform| + |reference color - uniform| := by simpa only [abs_sub_comm uniform (reference color)] using abs_sub_le (body color) uniform (reference color)
      _ ≤ _ := by linarith [hdeficit color]
  refine ⟨hpoint, ?_⟩
  have hh := profileSquareNorm_le_relative_mul_l1 primary (body - reference)
    (5 * compensation + 4 * (upper - uniform) / uniform) hp (by simpa using hpoint)
  exact hh.trans (mul_le_mul_of_nonneg_left hfringe (by positivity))

end MeanNorms

namespace V7Calibration

open Filter
open scoped Topology

/-- The pointwise deficit estimate is proved from the actual calibration
numerator, actual shifted slices, and the V7 error estimates. -/
theorem base_retained_lower_eventually {σ τ : ℕ → Type*}
    [∀ parameter, Fintype (σ parameter)] [∀ parameter, Fintype (τ parameter)]
    (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (boundary : ℕ → ℤ)
    (bodyShifts : (parameter : ℕ) → σ parameter → ℤ)
    (bodyLaw : (parameter : ℕ) → FiniteDist (σ parameter))
    (startsPlus startsMinus sources : (parameter : ℕ) → τ parameter → ℤ)
    (sourceLaw : (parameter : ℕ) → FiniteDist (τ parameter))
    (hsupport : ∀ᶠ parameter in atTop,
      PhysicalSupports parameter cutoffScale (boundary parameter)
        (startsPlus parameter) (startsMinus parameter) (sources parameter)) :
    ∀ᶠ parameter in atTop, ∀ color : Fin (Parameters.modulus parameter),
      ((Parameters.bodies parameter : ℝ) + Parameters.legs parameter * GaussianSource.v7Activation cutoffScale parameter) /
          (Parameters.legs parameter * GaussianSource.v7Activation cutoffScale parameter) *
        (1 / ((Parameters.modulus parameter : ℝ) - 2 * Parameters.safeMargin parameter) -
          TrimmedSlice.blurredSafeLaw (Parameters.modulus parameter) (Parameters.safeMargin parameter)
            (bodyShifts parameter) (bodyLaw parameter).weight color.val) +
        1 / (2 * (Parameters.modulus parameter : ℝ)) ≤
      basePrimary parameter cutoffScale (boundary parameter) (bodyShifts parameter) (bodyLaw parameter)
        (startsPlus parameter) (startsMinus parameter) (sources parameter) (sourceLaw parameter) color := by
  have hb := hsupport.mono fun _ h => h.1
  filter_upwards [hsupport, v7_primaryCalibrationLoss_eventually cutoffScale hscale boundary hb,
    v7_primaryCalibration_clearance_eventually cutoffScale hscale boundary hb,
    eventually_ge_atTop 2] with parameter hs hloss hclear hlarge
  have hx : 0 < Parameters.security parameter := lt_of_lt_of_le (by decide : 0 < 2) (Parameters.security_ge_two parameter)
  have hwidth : Parameters.anchorWidth parameter ≠ 0 := pow_ne_zero _ (ne_of_gt hx)
  have hq : (0 : ℤ) < Parameters.modulus parameter := by exact_mod_cast (Parameters.modulus_prime parameter).pos
  have hlegs : 0 < (Parameters.legs parameter : ℝ) := by unfold Parameters.legs; positivity
  have ha : 0 < GaussianSource.v7Activation cutoffScale parameter :=
    GaussianSource.activation_positive _ _ _ _ (GaussianSource.legFeatureCount_positive cutoffScale parameter hscale (by omega))
  have hpopulation : (Parameters.bodies parameter : ℝ) + 2 * Parameters.legs parameter = Parameters.dimension parameter := by
    exact_mod_cast Parameters.population_identity parameter
  intro color
  have hh := TrimmedSlice.actualFairBasePrimary_retained_lower (Parameters.modulus parameter)
    (Parameters.safeMargin parameter) (boundary parameter) (3 * Parameters.anchorWidth parameter)
    (GaussianSource.legCutoff cutoffScale parameter) (Parameters.anchorWidth parameter)
    (Parameters.bodies parameter) (Parameters.legs parameter) (GaussianSource.v7Activation cutoffScale parameter)
    (bodyShifts parameter) (bodyLaw parameter).weight (startsPlus parameter) (startsMinus parameter)
    (sources parameter) (sourceLaw parameter).weight hq hlegs (Nat.cast_nonneg _) ha
    (GaussianSource.activation_le_one _ _ _ _) (by positivity) hs.1.1 (by positivity) (by positivity)
    hwidth hclear.1 hclear.2 (sourceLaw parameter).nonneg (sourceLaw parameter).sum_one
    hs.2.1 hs.2.2.1 hs.2.2.2
    (by simpa only [Int.cast_natCast, Int.cast_mul, Int.cast_ofNat, hpopulation] using hloss) color.val
  simpa only [basePrimary, Int.cast_natCast] using hh

/-- The actual body-to-primary relative deficit, including the beta repair. -/
theorem body_deficit_eventually {σ τ : ℕ → Type*}
    [∀ parameter, Fintype (σ parameter)] [∀ parameter, Fintype (τ parameter)]
    (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ) (boundary : ℕ → ℤ)
    (bodyShifts : (parameter : ℕ) → σ parameter → ℤ)
    (bodyLaw : (parameter : ℕ) → FiniteDist (σ parameter))
    (startsPlus startsMinus sources : (parameter : ℕ) → τ parameter → ℤ)
    (sourceLaw : (parameter : ℕ) → FiniteDist (τ parameter))
    (hmodel : ∀ᶠ parameter in atTop,
      PhysicalSupports parameter cutoffScale (boundary parameter)
        (startsPlus parameter) (startsMinus parameter) (sources parameter) ∧
      (∀ index, |bodyShifts parameter index| ≤ (Parameters.safeMargin parameter : ℤ) - boundary parameter) ∧
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ color : Fin (Parameters.modulus parameter),
      1 / ((Parameters.modulus parameter : ℝ) - 2 * Parameters.safeMargin parameter) -
        TrimmedSlice.blurredSafeLaw (Parameters.modulus parameter) (Parameters.safeMargin parameter)
          (bodyShifts parameter) (bodyLaw parameter).weight color.val ≤
      2 * ((Parameters.legs parameter : ℝ) * GaussianSource.v7Activation cutoffScale parameter /
        Parameters.bodies parameter) *
      primary parameter cutoffScale (beta parameter) (boundary parameter) (bodyShifts parameter) (bodyLaw parameter)
        (startsPlus parameter) (startsMinus parameter) (sources parameter) (sourceLaw parameter) color := by
  filter_upwards [base_retained_lower_eventually cutoffScale hscale boundary bodyShifts bodyLaw
    startsPlus startsMinus sources sourceLaw (hmodel.mono fun _ h => h.1),
    primary_ge_half_base_eventually cutoffScale hscale beta boundary bodyShifts bodyLaw
      startsPlus startsMinus sources sourceLaw hmodel,
    primary_estimates_eventually cutoffScale hscale beta boundary bodyShifts bodyLaw
      startsPlus startsMinus sources sourceLaw hmodel, eventually_ge_atTop 1]
    with parameter hret hhalf hest hp
  intro color
  have hN : (0 : ℝ) < Parameters.bodies parameter := by exact_mod_cast Parameters.bodies_positive parameter
  have hm : (0 : ℝ) < Parameters.legs parameter := by
    unfold Parameters.legs
    have hh := Parameters.security_ge_two parameter
    positivity
  have ha : 0 < GaussianSource.v7Activation cutoffScale parameter :=
    GaussianSource.activation_positive _ _ _ _ (GaussianSource.legFeatureCount_positive cutoffScale parameter hscale hp)
  have hq : (0 : ℝ) < Parameters.modulus parameter := by exact_mod_cast (Parameters.modulus_prime parameter).pos
  have hprimary : 0 < primary parameter cutoffScale (beta parameter) (boundary parameter)
      (bodyShifts parameter) (bodyLaw parameter) (startsPlus parameter) (startsMinus parameter)
      (sources parameter) (sourceLaw parameter) color := lt_of_lt_of_le (by positivity) (hest.1 color)
  have hbase := hret color
  have hbase' := hhalf color
  let deficit := 1 / ((Parameters.modulus parameter : ℝ) - 2 * Parameters.safeMargin parameter) -
        TrimmedSlice.blurredSafeLaw (Parameters.modulus parameter) (Parameters.safeMargin parameter)
          (bodyShifts parameter) (bodyLaw parameter).weight color.val
  let pr := primary parameter cutoffScale (beta parameter) (boundary parameter)
      (bodyShifts parameter) (bodyLaw parameter) (startsPlus parameter) (startsMinus parameter)
      (sources parameter) (sourceLaw parameter) color
  have hmain : (((Parameters.bodies parameter : ℝ) + Parameters.legs parameter * GaussianSource.v7Activation cutoffScale parameter) /
      (Parameters.legs parameter * GaussianSource.v7Activation cutoffScale parameter)) * deficit ≤ 2 * pr := by
    dsimp only [deficit, pr]
    linarith [show 0 < 1 / (2 * (Parameters.modulus parameter : ℝ)) by positivity]
  have hmul := (div_le_iff₀ (mul_pos hm ha)).mp (show
      (((Parameters.bodies parameter : ℝ) + Parameters.legs parameter * GaussianSource.v7Activation cutoffScale parameter) * deficit) /
        (Parameters.legs parameter * GaussianSource.v7Activation cutoffScale parameter) ≤ 2 * pr by
      convert hmain using 1; ring)
  change deficit ≤ 2 * ((Parameters.legs parameter : ℝ) * GaussianSource.v7Activation cutoffScale parameter /
    Parameters.bodies parameter) * pr
  by_cases hd : 0 ≤ deficit
  · have hh : deficit * Parameters.bodies parameter ≤ 2 * pr *
        (Parameters.legs parameter * GaussianSource.v7Activation cutoffScale parameter) := by
      nlinarith [mul_nonneg hd (mul_pos hm ha).le]
    have hdiv := (le_div_iff₀ hN).mpr hh
    convert hdiv using 1; ring
  · have hpr : 0 ≤ pr := hprimary.le
    exact (le_of_not_ge hd).trans (by positivity)

end V7Calibration

end AFT
