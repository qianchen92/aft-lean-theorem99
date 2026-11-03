import AFT.TrimmedSlice
import AFT.Parameters

/-!
# Pointwise positivity of the mean-calibrated primary law

The estimates retain the actual mean-calibration formula. The first result
isolates its deterministic arithmetic, including the nonnegative body
mean deficit; concrete averaged trimmed slices supply its hypotheses.
-/

namespace AFT

open scoped BigOperators

/-- The three explicit losses in V7's primary positivity calculation. -/
noncomputable def primaryCalibrationLoss
    (modulus dimension legs activation margin deleted cutoff width : ℝ) : ℝ :=
  4 * dimension * margin / (legs * activation * modulus) +
    4 * deleted / (activation * modulus) + 4 * cutoff / (activation * width)

/-- Exact deterministic positivity calculation, with the body deficit
retained. `deleted` is the baseline slice shift bound plus both margins. -/
theorem basePrimary_scalar_lower (modulus bodies legs activation margin deleted cutoff width
    body shifted unshifted : ℝ)
    (hq : 0 < modulus) (hlegs : 0 < legs) (hbodies : 0 ≤ bodies)
    (hactivation : 0 < activation) (hactivationUpper : activation ≤ 1)
    (hmargin : 0 ≤ margin) (hdeleted : 0 ≤ deleted) (hcutoff : 0 ≤ cutoff) (hwidth : 0 < width)
    (hmarginSmall : 4 * margin ≤ modulus) (hdeletedSmall : 2 * (deleted + cutoff) ≤ modulus)
    (hunshifted : unshifted ≤ 1 / (modulus - deleted))
    (hvariation : |shifted - unshifted| ≤ cutoff / (width * (modulus - deleted - cutoff))) :
    (bodies + legs * activation) / (legs * activation) *
        (1 / (modulus - 2 * margin) - body) +
      (1 - primaryCalibrationLoss modulus (bodies + 2 * legs) legs activation margin deleted cutoff width) /
        modulus ≤
    ((bodies + 2 * legs) / modulus - (bodies + legs * activation) * body -
      2 * legs * shifted + 2 * legs * activation * unshifted) / (legs * activation) := by
  have hsafe : 0 < modulus - 2 * margin := by linarith
  have hslice : 0 < modulus - deleted := by linarith
  have hsliceSource : 0 < modulus - deleted - cutoff := by linarith
  have hbodyDiff : 0 ≤ 1 / (modulus - 2 * margin) - 1 / modulus := by
    exact sub_nonneg.mpr (one_div_le_one_div_of_le hsafe (by linarith))
  have hbodyBound : 1 / (modulus - 2 * margin) - 1 / modulus ≤ 4 * margin / modulus ^ 2 := by
    calc
      _ = 2 * margin / (modulus * (modulus - 2 * margin)) := by field_simp; ring
      _ ≤ 2 * margin / (modulus ^ 2 / 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (by nlinarith [mul_nonneg (le_of_lt hq) (sub_nonneg.mpr hmarginSmall)])
      _ = _ := by ring
  have hsliceBound : unshifted - 1 / modulus ≤ 2 * deleted / modulus ^ 2 := by
    calc
      _ ≤ 1 / (modulus - deleted) - 1 / modulus := sub_le_sub_right hunshifted _
      _ = deleted / (modulus * (modulus - deleted)) := by field_simp; ring
      _ ≤ deleted / (modulus ^ 2 / 2) :=
        div_le_div_of_nonneg_left hdeleted (by positivity)
          (by nlinarith [mul_nonneg (le_of_lt hq) (show 0 ≤ modulus - 2 * deleted by linarith)])
      _ = _ := by ring
  have hchangeBound : shifted - unshifted ≤ 2 * cutoff / (width * modulus) := by
    calc
      _ ≤ |shifted - unshifted| := le_abs_self _
      _ ≤ cutoff / (width * (modulus - deleted - cutoff)) := hvariation
      _ ≤ cutoff / (width * modulus / 2) :=
        div_le_div_of_nonneg_left hcutoff (by positivity)
          (by nlinarith [mul_nonneg (le_of_lt hwidth) (sub_nonneg.mpr hdeletedSmall)])
      _ = _ := by ring
  let coefficient := (bodies + legs * activation) / (legs * activation)
  have hcoefficient : 0 ≤ coefficient := by dsimp [coefficient]; positivity
  have hcoefficientUpper : coefficient ≤ (bodies + 2 * legs) / (legs * activation) := by
    dsimp [coefficient]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  have hbodyTerm := mul_le_mul hcoefficientUpper hbodyBound hbodyDiff
    (by positivity : 0 ≤ (bodies + 2 * legs) / (legs * activation))
  have hfactor : 0 ≤ 2 * (1 - activation) / activation :=
    div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hactivationUpper)) hactivation.le
  have hfactorUpper : 2 * (1 - activation) / activation ≤ 2 / activation := by
    apply div_le_div_of_nonneg_right _ hactivation.le
    linarith
  have hsliceTerm := (mul_le_mul_of_nonneg_left hsliceBound hfactor).trans
    (mul_le_mul_of_nonneg_right hfactorUpper (by positivity : 0 ≤ 2 * deleted / modulus ^ 2))
  have hchangeTerm := mul_le_mul_of_nonneg_left hchangeBound (by positivity : 0 ≤ 2 / activation)
  have heq :
      ((bodies + 2 * legs) / modulus - (bodies + legs * activation) * body -
        2 * legs * shifted + 2 * legs * activation * unshifted) / (legs * activation) =
      coefficient * (1 / (modulus - 2 * margin) - body) + 1 / modulus -
        coefficient * (1 / (modulus - 2 * margin) - 1 / modulus) -
        (2 * (1 - activation) / activation) * (unshifted - 1 / modulus) -
        (2 / activation) * (shifted - unshifted) := by
    dsimp [coefficient]
    field_simp
    ring
  rw [heq]
  have hloss : primaryCalibrationLoss modulus (bodies + 2 * legs) legs activation margin deleted cutoff width /
      modulus = ((bodies + 2 * legs) / (legs * activation)) * (4 * margin / modulus ^ 2) +
      (2 / activation) * (2 * deleted / modulus ^ 2) + (2 / activation) * (2 * cutoff / (width * modulus)) := by
    unfold primaryCalibrationLoss
    field_simp
    ring
  change coefficient * _ + _ ≤ _
  rw [sub_div, hloss]
  nlinarith only [hbodyTerm, hsliceTerm, hchangeTerm]

/-- Once the three computed losses sum to at most one half, the actual
calibration numerator is bounded below by `1/(2q)`, with no positivity
assumption on that numerator. -/
theorem basePrimary_scalar_positive (modulus bodies legs activation margin deleted cutoff width
    body shifted unshifted : ℝ)
    (hq : 0 < modulus) (hlegs : 0 < legs) (hbodies : 0 ≤ bodies)
    (hactivation : 0 < activation) (hactivationUpper : activation ≤ 1)
    (hmargin : 0 ≤ margin) (hdeleted : 0 ≤ deleted) (hcutoff : 0 ≤ cutoff) (hwidth : 0 < width)
    (hmarginSmall : 4 * margin ≤ modulus) (hdeletedSmall : 2 * (deleted + cutoff) ≤ modulus)
    (hbody : body ≤ 1 / (modulus - 2 * margin))
    (hunshifted : unshifted ≤ 1 / (modulus - deleted))
    (hvariation : |shifted - unshifted| ≤ cutoff / (width * (modulus - deleted - cutoff)))
    (hloss : primaryCalibrationLoss modulus (bodies + 2 * legs) legs activation margin deleted cutoff width ≤ 1 / 2) :
    1 / (2 * modulus) ≤
      ((bodies + 2 * legs) / modulus - (bodies + legs * activation) * body -
        2 * legs * shifted + 2 * legs * activation * unshifted) / (legs * activation) := by
  have hh := basePrimary_scalar_lower modulus bodies legs activation margin deleted cutoff width body shifted unshifted
    hq hlegs hbodies hactivation hactivationUpper hmargin hdeleted hcutoff hwidth hmarginSmall hdeletedSmall
    hunshifted hvariation
  have hnonneg : 0 ≤ (bodies + legs * activation) / (legs * activation) *
      (1 / (modulus - 2 * margin) - body) := mul_nonneg (by positivity) (sub_nonneg.mpr hbody)
  have hremain := div_le_div_of_nonneg_right (show (1 / 2 : ℝ) ≤ 1 -
      primaryCalibrationLoss modulus (bodies + 2 * legs) legs activation margin deleted cutoff width by linarith) hq.le
  have hhalf : (1 / 2 : ℝ) / modulus = 1 / (2 * modulus) := by ring
  rw [hhalf] at hremain
  linarith

namespace TrimmedSlice

/-- The actual mean of a safe uniform center after a finite public body blur. -/
noncomputable def blurredSafeLaw {σ : Type*} [Fintype σ]
    (modulus margin : ℤ) (shifts : σ → ℤ) (weights : σ → ℝ) (color : ℤ) : ℝ :=
  ∑ index, weights index * intervalAnchorLaw margin (modulus - 2 * margin).toNat (color - shifts index)

theorem blurredSafeLaw_le {σ : Type*} [Fintype σ]
    (modulus margin : ℤ) (shifts : σ → ℤ) (weights : σ → ℝ)
    (hweights : ∀ index, 0 ≤ weights index) (hmass : ∑ index, weights index = 1)
    (hwidth : 2 * margin < modulus) (color : ℤ) :
    blurredSafeLaw modulus margin shifts weights color ≤ 1 / ((modulus : ℝ) - 2 * margin) := by
  have hwidthCast : ((modulus - 2 * margin).toNat : ℝ) = (modulus : ℝ) - 2 * margin := by
    have hh : ((modulus - 2 * margin).toNat : ℤ) = modulus - 2 * margin := Int.toNat_of_nonneg (by omega)
    exact_mod_cast hh
  calc
    _ ≤ ∑ index, weights index * (((modulus - 2 * margin).toNat : ℝ)⁻¹) :=
      Finset.sum_le_sum fun index _ => mul_le_mul_of_nonneg_left
        (intervalAnchorLaw_bound _ _ _) (hweights index)
    _ = _ := by rw [← Finset.sum_mul, hmass, one_mul, hwidthCast, one_div]

/-- The original mean calibration, now with actual finite blurred safe and
trimmed slice laws. On the finite output palette this is V7's base primary law. -/
noncomputable def actualBasePrimary {σ τ : Type*} [Fintype σ] [Fintype τ]
    (modulus margin boundary : ℤ) (width : ℕ) (bodies legs activation : ℝ)
    (bodyShifts : σ → ℤ) (bodyWeights : σ → ℝ)
    (starts sources : τ → ℤ) (weights : τ → ℝ) : ℤ → ℝ :=
  basePrimaryProfile (bodies + 2 * legs) bodies legs activation
    (fun _ => 1 / (modulus : ℝ)) (blurredSafeLaw modulus margin bodyShifts bodyWeights)
    (mixedLaw modulus boundary starts sources weights width)
    (mixedLaw modulus boundary starts (fun _ => 0) weights width)

/-- Pointwise positivity follows for the actual finite calibration, not
for profiles supplied with positivity as an input hypothesis. -/
theorem actualBasePrimary_lower {σ τ : Type*} [Fintype σ] [Fintype τ]
    (modulus margin boundary shiftBound cutoff : ℤ) (width : ℕ) (bodies legs activation : ℝ)
    (bodyShifts : σ → ℤ) (bodyWeights : σ → ℝ)
    (starts sources : τ → ℤ) (weights : τ → ℝ)
    (hq : 0 < modulus) (hlegs : 0 < legs) (hbodies : 0 ≤ bodies)
    (hactivation : 0 < activation) (hactivationUpper : activation ≤ 1)
    (hmargin : 0 ≤ margin) (hboundary : 0 ≤ boundary) (hshiftBound : 0 ≤ shiftBound)
    (hcutoff : 0 ≤ cutoff) (hwidth : width ≠ 0)
    (hmarginSmall : 4 * margin ≤ modulus) (hdeletedSmall : 2 * (shiftBound + 2 * boundary + cutoff) ≤ modulus)
    (hbodyWeights : ∀ index, 0 ≤ bodyWeights index) (hbodyMass : ∑ index, bodyWeights index = 1)
    (hweights : ∀ index, 0 ≤ weights index) (hmass : ∑ index, weights index = 1)
    (hbound : ∀ index shift, shift ∈ anchorInterval (starts index) width → |shift| ≤ shiftBound)
    (hsources : ∀ index, |sources index| ≤ cutoff)
    (hloss : primaryCalibrationLoss modulus (bodies + 2 * legs) legs activation margin
      ((shiftBound : ℝ) + 2 * boundary) cutoff width ≤ 1 / 2) (color : ℤ) :
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
  have hbody := blurredSafeLaw_le modulus margin bodyShifts bodyWeights hbodyWeights hbodyMass (by omega) color
  have hunshifted : mixedLaw modulus boundary starts (fun _ => 0) weights width color ≤
      1 / ((modulus : ℝ) - ((shiftBound : ℝ) + 2 * boundary)) := by
    convert mixedLaw_zero_le modulus boundary shiftBound starts weights width hwidth hweights hmass hbound (by omega) color using 1; ring
  have hvariation : |mixedLaw modulus boundary starts sources weights width color -
      mixedLaw modulus boundary starts (fun _ => 0) weights width color| ≤
      (cutoff : ℝ) / ((width : ℝ) * ((modulus : ℝ) - ((shiftBound : ℝ) + 2 * boundary) - cutoff)) := by
    convert mixedLaw_source_variation modulus boundary shiftBound cutoff starts sources weights width hwidth
      hweights hmass hbound hsources (by omega) color using 1; ring
  have hh := basePrimary_scalar_positive modulus bodies legs activation margin
    ((shiftBound : ℝ) + 2 * boundary) cutoff width
    (blurredSafeLaw modulus margin bodyShifts bodyWeights color)
    (mixedLaw modulus boundary starts sources weights width color)
    (mixedLaw modulus boundary starts (fun _ => 0) weights width color)
    hqReal hlegs hbodies hactivation hactivationUpper hmarginReal (by positivity) hcutoffReal hwidthReal
    hmarginSmallReal hdeletedSmallReal hbody hunshifted hvariation hloss
  simpa only [actualBasePrimary, basePrimaryProfile, mul_one_div] using hh

end TrimmedSlice

end AFT
