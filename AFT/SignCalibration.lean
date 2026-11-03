import AFT.PrimaryCalibration
import AFT.TrimmedPalette

/-!
# The signed diffuse response is controlled by the actual calibration
-/

namespace AFT

open scoped BigOperators

/-- The exact signed endpoint mean from the two actual shift-sign branches. -/
def calibratedSignResponse (activation : ℝ) (shiftedPlus shiftedMinus unshiftedPlus unshiftedMinus : ℝ) : ℝ :=
  shiftedPlus - shiftedMinus - activation * (unshiftedPlus - unshiftedMinus)

theorem reciprocal_trimmed_excess (modulus deleted : ℝ)
    (hq : 0 < modulus) (hd : 0 ≤ deleted) (hsmall : 2 * deleted ≤ modulus) :
    1 / (modulus - deleted) - 1 / modulus ≤ 2 * deleted / modulus ^ 2 := by
  have hden : 0 < modulus - deleted := by linarith
  calc
    _ = deleted / (modulus * (modulus - deleted)) := by field_simp; ring
    _ ≤ deleted / (modulus ^ 2 / 2) :=
      div_le_div_of_nonneg_left hd (by positivity)
        (by nlinarith [mul_nonneg hq.le (sub_nonneg.mpr hsmall)])
    _ = _ := by ring

set_option maxHeartbeats 800000 in
/-- Pointwise sign domination follows from the actual mean-calibration
identity and the explicit trimmed-slice estimates. Its positive primary
profile is the computed numerator, not a premise. -/
theorem calibratedSignResponse_scalar_bound
    (modulus bodies legs activation margin deleted cutoff width
      body shiftedPlus shiftedMinus unshiftedPlus unshiftedMinus : ℝ)
    (hq : 0 < modulus) (hlegs : 0 < legs) (hbodies : 0 ≤ bodies)
    (ha : 0 < activation) (haUpper : activation ≤ 1 / 2)
    (hm : 0 ≤ margin) (hd : 0 ≤ deleted) (hc : 0 ≤ cutoff) (hw : 0 < width) (hwq : width ≤ modulus)
    (hmargin : 4 * margin ≤ modulus) (hdeleted : 2 * (deleted + cutoff) ≤ modulus)
    (hbody : body ≤ 1 / (modulus - 2 * margin))
    (hplus : shiftedPlus ≤ 1 / (modulus - deleted - cutoff))
    (hminus : shiftedMinus ≤ 1 / (modulus - deleted - cutoff))
    (hvariationPlus : |shiftedPlus - unshiftedPlus| ≤ cutoff / (width * (modulus - deleted - cutoff)))
    (hvariationMinus : |shiftedMinus - unshiftedMinus| ≤ cutoff / (width * (modulus - deleted - cutoff)))
    (hloss : primaryCalibrationLoss modulus (bodies + 2 * legs) legs activation margin deleted cutoff width ≤ 1 / 2) :
    |calibratedSignResponse activation shiftedPlus shiftedMinus unshiftedPlus unshiftedMinus| ≤
      activation * (((bodies + 2 * legs) / modulus - (bodies + legs * activation) * body -
        2 * legs * ((shiftedPlus + shiftedMinus) / 2) +
        2 * legs * activation * ((unshiftedPlus + unshiftedMinus) / 2)) / (legs * activation)) := by
  let variation := cutoff / (width * (modulus - deleted - cutoff))
  let ceiling := 1 / (modulus - deleted - cutoff)
  have hslice : 0 < modulus - deleted - cutoff := by linarith
  have hsafe : 0 < modulus - 2 * margin := by linarith
  have hfactor : 0 ≤ 1 - activation := by linarith
  have hdiff : |shiftedPlus - shiftedMinus| ≤ 2 * ceiling - shiftedPlus - shiftedMinus := by
    exact abs_le.mpr (by dsimp [ceiling]; constructor <;> linarith)
  have hnoise : |(shiftedPlus - unshiftedPlus) - (shiftedMinus - unshiftedMinus)| ≤ 2 * variation :=
    (abs_sub _ _).trans (by dsimp [variation]; linarith)
  have hsplit : calibratedSignResponse activation shiftedPlus shiftedMinus unshiftedPlus unshiftedMinus =
      (1 - activation) * (shiftedPlus - shiftedMinus) +
        activation * ((shiftedPlus - unshiftedPlus) - (shiftedMinus - unshiftedMinus)) := by
    unfold calibratedSignResponse
    ring
  have habs : |calibratedSignResponse activation shiftedPlus shiftedMinus unshiftedPlus unshiftedMinus| ≤
      (1 - activation) * (2 * ceiling - shiftedPlus - shiftedMinus) + 2 * activation * variation := by
    rw [hsplit]
    have hh := abs_add_le ((1 - activation) * (shiftedPlus - shiftedMinus))
      (activation * ((shiftedPlus - unshiftedPlus) - (shiftedMinus - unshiftedMinus)))
    rw [abs_mul, abs_mul, abs_of_nonneg hfactor, abs_of_pos ha] at hh
    have h1 := mul_le_mul_of_nonneg_left hdiff hfactor
    have h2 := mul_le_mul_of_nonneg_left hnoise ha.le
    nlinarith only [hh, h1, h2]
  have hvp := (abs_le.mp hvariationPlus).2
  have hvm := (abs_le.mp hvariationMinus).2
  have hceiling : ceiling - 1 / modulus ≤ 2 * (deleted + cutoff) / modulus ^ 2 := by
    simpa only [ceiling, sub_add_eq_sub_sub] using reciprocal_trimmed_excess modulus (deleted + cutoff) hq (by positivity) hdeleted
  have hbodyBound : body - 1 / modulus ≤ 4 * margin / modulus ^ 2 := by
    have hh := reciprocal_trimmed_excess modulus (2 * margin) hq (by positivity) (by linarith)
    exact (sub_le_sub_right hbody _).trans (hh.trans_eq (by ring))
  have hceilingTerm : 2 * (1 - activation) * (ceiling - 1 / modulus) ≤
      4 * (deleted + cutoff) / modulus ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hceiling (by positivity : 0 ≤ 2 * (1 - activation))
    have h2 := mul_le_mul_of_nonneg_right (show 2 * (1 - activation) ≤ 2 by linarith)
      (by positivity : 0 ≤ 2 * (deleted + cutoff) / modulus ^ 2)
    exact (h1.trans h2).trans_eq (by ring)
  have hbodyCoefficient : 0 ≤ (bodies + legs * activation) / legs := by positivity
  have hbodyCoefficientUpper : (bodies + legs * activation) / legs ≤ (bodies + 2 * legs) / legs := by
    apply div_le_div_of_nonneg_right _ hlegs.le
    nlinarith
  have hbodyTerm : (bodies + legs * activation) / legs * (body - 1 / modulus) ≤
      4 * (bodies + 2 * legs) * margin / (legs * modulus ^ 2) := by
    have hh := (mul_le_mul_of_nonneg_left hbodyBound hbodyCoefficient).trans
      (mul_le_mul_of_nonneg_right hbodyCoefficientUpper (by positivity))
    exact hh.trans_eq (by ring)
  have hvariation : variation ≤ 2 * cutoff / (width * modulus) := by
    dsimp [variation]
    calc
      _ ≤ cutoff / (width * modulus / 2) := div_le_div_of_nonneg_left hc (by positivity)
        (by nlinarith [mul_nonneg hw.le (sub_nonneg.mpr hdeleted)])
      _ = _ := by ring
  have hcutoffShift : 4 * cutoff / modulus ^ 2 ≤ 4 * cutoff / (width * modulus) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
  have hsourceTerm : 4 * activation * variation ≤ 4 * cutoff / (width * modulus) := by
    have hh := mul_le_mul_of_nonneg_left hvariation (by positivity : 0 ≤ 4 * activation)
    have hh2 := mul_le_mul_of_nonneg_right (show 8 * activation ≤ 4 by linarith)
      (by positivity : 0 ≤ cutoff / (width * modulus))
    have heq : 4 * activation * (2 * cutoff / (width * modulus)) =
        8 * activation * (cutoff / (width * modulus)) := by ring
    rw [heq] at hh
    exact (hh.trans hh2).trans_eq (by ring)
  have hfirstNonneg : 0 ≤ 4 * (bodies + 2 * legs) * margin / (legs * modulus ^ 2) := by positivity
  have hsecondNonneg : 0 ≤ 4 * deleted / modulus ^ 2 := by positivity
  have hscaledLoss : 2 * activation / modulus *
      primaryCalibrationLoss modulus (bodies + 2 * legs) legs activation margin deleted cutoff width =
      2 * (4 * (bodies + 2 * legs) * margin / (legs * modulus ^ 2)) +
        2 * (4 * deleted / modulus ^ 2) + 8 * cutoff / (width * modulus) := by
    unfold primaryCalibrationLoss
    field_simp
    ring
  have hlossScaled := mul_le_mul_of_nonneg_left hloss (by positivity : 0 ≤ 2 * activation / modulus)
  rw [hscaledLoss] at hlossScaled
  have herror : 2 * (1 - activation) * (ceiling - 1 / modulus) +
      (bodies + legs * activation) / legs * (body - 1 / modulus) + 4 * activation * variation ≤ activation / modulus := by
    have hsplitD : 4 * (deleted + cutoff) / modulus ^ 2 = 4 * deleted / modulus ^ 2 + 4 * cutoff / modulus ^ 2 := by ring
    rw [hsplitD] at hceilingTerm
    calc
      _ ≤ (4 * deleted / modulus ^ 2 + 4 * cutoff / modulus ^ 2) +
          4 * (bodies + 2 * legs) * margin / (legs * modulus ^ 2) + 4 * cutoff / (width * modulus) :=
        add_le_add (add_le_add hceilingTerm hbodyTerm) hsourceTerm
      _ ≤ (4 * deleted / modulus ^ 2 + 4 * cutoff / (width * modulus)) +
          4 * (bodies + 2 * legs) * margin / (legs * modulus ^ 2) + 4 * cutoff / (width * modulus) := by
        linarith only [hcutoffShift]
      _ ≤ 2 * (4 * (bodies + 2 * legs) * margin / (legs * modulus ^ 2)) +
          2 * (4 * deleted / modulus ^ 2) + 8 * cutoff / (width * modulus) := by
        ring_nf at hfirstNonneg hsecondNonneg ⊢
        linarith only [hfirstNonneg, hsecondNonneg]
      _ ≤ 2 * activation / modulus * (1 / 2) := hlossScaled
      _ = _ := by ring
  have hidentity (ceiling variation : ℝ) : activation * (((bodies + 2 * legs) / modulus - (bodies + legs * activation) * body -
        2 * legs * ((shiftedPlus + shiftedMinus) / 2) +
        2 * legs * activation * ((unshiftedPlus + unshiftedMinus) / 2)) / (legs * activation)) =
      (1 - activation) * (2 * ceiling - shiftedPlus - shiftedMinus) + 2 * activation * variation +
        activation / modulus - (2 * (1 - activation) * (ceiling - 1 / modulus) +
        (bodies + legs * activation) / legs * (body - 1 / modulus) + 4 * activation * variation) +
        activation * (unshiftedPlus + unshiftedMinus - shiftedPlus - shiftedMinus + 2 * variation) := by
    field_simp
    ring
  rw [hidentity ceiling variation]
  have hlast : 0 ≤ activation * (unshiftedPlus + unshiftedMinus - shiftedPlus - shiftedMinus + 2 * variation) := by
    apply mul_nonneg ha.le
    dsimp [variation]
    linarith
  linarith

/-- The four actual probability laws give the L1 sign-response estimate
by comparison with the same uniform law. -/
theorem calibratedSignResponse_l1_bound {ι : Type*} [Fintype ι]
    (activation bound : ℝ) (reference shiftedPlus shiftedMinus unshiftedPlus unshiftedMinus : ι → ℝ)
    (ha : 0 ≤ activation) (haUpper : activation ≤ 1) (hbound : 0 ≤ bound)
    (hsp : (∑ color, |shiftedPlus color - reference color|) ≤ bound)
    (hsm : (∑ color, |shiftedMinus color - reference color|) ≤ bound)
    (hup : (∑ color, |unshiftedPlus color - reference color|) ≤ bound)
    (hum : (∑ color, |unshiftedMinus color - reference color|) ≤ bound) :
    (∑ color, |calibratedSignResponse activation (shiftedPlus color) (shiftedMinus color)
      (unshiftedPlus color) (unshiftedMinus color)|) ≤ 4 * bound := by
  have hpoint (color : ι) : |calibratedSignResponse activation (shiftedPlus color) (shiftedMinus color)
      (unshiftedPlus color) (unshiftedMinus color)| ≤
      |shiftedPlus color - reference color| + |shiftedMinus color - reference color| +
        activation * (|unshiftedPlus color - reference color| + |unshiftedMinus color - reference color|) := by
    have hs : shiftedPlus color - shiftedMinus color =
        (shiftedPlus color - reference color) - (shiftedMinus color - reference color) := by ring
    have hu : unshiftedPlus color - unshiftedMinus color =
        (unshiftedPlus color - reference color) - (unshiftedMinus color - reference color) := by ring
    unfold calibratedSignResponse
    rw [hs, hu]
    have h1 := abs_sub (shiftedPlus color - reference color) (shiftedMinus color - reference color)
    have h2 := abs_sub (unshiftedPlus color - reference color) (unshiftedMinus color - reference color)
    have h3 := abs_sub ((shiftedPlus color - reference color) - (shiftedMinus color - reference color))
      (activation * ((unshiftedPlus color - reference color) - (unshiftedMinus color - reference color)))
    rw [abs_mul, abs_of_nonneg ha] at h3
    have h4 := mul_le_mul_of_nonneg_left h2 ha
    linarith only [h1, h3, h4]
  have hs := Finset.sum_le_sum (fun color (_ : color ∈ Finset.univ) => hpoint color)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  have hu := mul_le_mul_of_nonneg_left (add_le_add hup hum) ha
  have hc := mul_le_mul_of_nonneg_right haUpper (show 0 ≤ bound + bound by positivity)
  linarith

namespace TrimmedSlice

/-- Equal mixture of the two public shift-sign branches. -/
noncomputable def fairMixedLaw {τ : Type*} [Fintype τ] (modulus boundary : ℤ)
    (startsPlus startsMinus sources : τ → ℤ) (weights : τ → ℝ) (width : ℕ) (color : ℤ) : ℝ :=
  (mixedLaw modulus boundary startsPlus sources weights width color +
    mixedLaw modulus boundary startsMinus sources weights width color) / 2

noncomputable def actualSignResponse {τ : Type*} [Fintype τ] (modulus boundary : ℤ)
    (startsPlus startsMinus sources : τ → ℤ) (weights : τ → ℝ) (width : ℕ) (activation : ℝ) (color : ℤ) : ℝ :=
  calibratedSignResponse activation
    (mixedLaw modulus boundary startsPlus sources weights width color)
    (mixedLaw modulus boundary startsMinus sources weights width color)
    (mixedLaw modulus boundary startsPlus (fun _ => 0) weights width color)
    (mixedLaw modulus boundary startsMinus (fun _ => 0) weights width color)

noncomputable def actualFairBasePrimary {σ τ : Type*} [Fintype σ] [Fintype τ]
    (modulus margin boundary : ℤ) (width : ℕ) (bodies legs activation : ℝ)
    (bodyShifts : σ → ℤ) (bodyWeights : σ → ℝ)
    (startsPlus startsMinus sources : τ → ℤ) (weights : τ → ℝ) : ℤ → ℝ :=
  basePrimaryProfile (bodies + 2 * legs) bodies legs activation
    (fun _ => 1 / (modulus : ℝ)) (blurredSafeLaw modulus margin bodyShifts bodyWeights)
    (fairMixedLaw modulus boundary startsPlus startsMinus sources weights width)
    (fairMixedLaw modulus boundary startsPlus startsMinus (fun _ => 0) weights width)

theorem actualSignResponse_zero_boundary {τ : Type*} [Fintype τ] (modulus boundary : ℤ)
    (startsPlus startsMinus sources : τ → ℤ) (weights : τ → ℝ) (width : ℕ) (activation : ℝ)
    (color : ℤ) (hout : color < boundary ∨ modulus - 1 - boundary < color) :
    actualSignResponse modulus boundary startsPlus startsMinus sources weights width activation color = 0 := by
  simp [actualSignResponse, calibratedSignResponse, mixedLaw_zero_boundary _ _ _ _ _ _ _ hout]

theorem actualSignResponse_palette_mass {τ : Type*} [Fintype τ]
    (modulus : ℕ) (boundary shiftBound cutoff : ℤ) (width : ℕ) (hwidth : width ≠ 0)
    (startsPlus startsMinus sources : τ → ℤ) (weights : τ → ℝ) (activation : ℝ)
    (hmass : ∑ index, weights index = 1) (hboundary : 0 ≤ boundary) (hcutoff : 0 ≤ cutoff)
    (hplus : ∀ index shift, shift ∈ anchorInterval (startsPlus index) width → |shift| ≤ shiftBound)
    (hminus : ∀ index shift, shift ∈ anchorInterval (startsMinus index) width → |shift| ≤ shiftBound)
    (hsources : ∀ index, |sources index| ≤ cutoff)
    (hclearance : 2 * boundary + shiftBound + cutoff < modulus) :
    ∑ color : Fin modulus, actualSignResponse modulus boundary startsPlus startsMinus sources weights width activation color.val = 0 := by
  have hsp := mixedLaw_palette_mass modulus boundary shiftBound cutoff width hwidth startsPlus sources weights hmass hboundary hplus hsources hclearance
  have hsm := mixedLaw_palette_mass modulus boundary shiftBound cutoff width hwidth startsMinus sources weights hmass hboundary hminus hsources hclearance
  have hup := mixedLaw_palette_mass modulus boundary shiftBound cutoff width hwidth startsPlus (fun _ => 0) weights hmass hboundary hplus (by simpa using fun _ : τ => hcutoff) hclearance
  have hum := mixedLaw_palette_mass modulus boundary shiftBound cutoff width hwidth startsMinus (fun _ => 0) weights hmass hboundary hminus (by simpa using fun _ : τ => hcutoff) hclearance
  simp only [actualSignResponse, calibratedSignResponse, Finset.sum_sub_distrib, ← Finset.mul_sum,
    hsp, hsm, hup, hum, sub_self, mul_zero]

theorem actualSignResponse_palette_l1_le {τ : Type*} [Fintype τ]
    (modulus : ℕ) (boundary shiftBound cutoff : ℤ) (width : ℕ) (hwidth : width ≠ 0)
    (startsPlus startsMinus sources : τ → ℤ) (weights : τ → ℝ) (activation : ℝ)
    (hweights : ∀ index, 0 ≤ weights index) (hmass : ∑ index, weights index = 1)
    (hboundary : 0 ≤ boundary) (hshiftBound : 0 ≤ shiftBound) (hcutoff : 0 ≤ cutoff)
    (ha : 0 ≤ activation) (haUpper : activation ≤ 1)
    (hplus : ∀ index shift, shift ∈ anchorInterval (startsPlus index) width → |shift| ≤ shiftBound)
    (hminus : ∀ index shift, shift ∈ anchorInterval (startsMinus index) width → |shift| ≤ shiftBound)
    (hsources : ∀ index, |sources index| ≤ cutoff)
    (hclearance : 2 * boundary + shiftBound + cutoff < modulus) :
    (∑ color : Fin modulus, |actualSignResponse modulus boundary startsPlus startsMinus sources weights width activation color.val|) ≤
      8 * ((shiftBound : ℝ) + cutoff + 2 * boundary) / modulus := by
  have hsp := mixedLaw_palette_l1_le modulus boundary shiftBound cutoff width hwidth startsPlus sources weights hweights hmass hboundary hplus hsources hclearance
  have hsm := mixedLaw_palette_l1_le modulus boundary shiftBound cutoff width hwidth startsMinus sources weights hweights hmass hboundary hminus hsources hclearance
  have hup := mixedLaw_palette_l1_le modulus boundary shiftBound cutoff width hwidth startsPlus (fun _ => 0) weights hweights hmass hboundary hplus (by simpa using fun _ : τ => hcutoff) hclearance
  have hum := mixedLaw_palette_l1_le modulus boundary shiftBound cutoff width hwidth startsMinus (fun _ => 0) weights hweights hmass hboundary hminus (by simpa using fun _ : τ => hcutoff) hclearance
  have hb : 0 ≤ 2 * ((shiftBound : ℝ) + cutoff + 2 * boundary) / modulus := by
    have : (0 : ℝ) ≤ shiftBound := by exact_mod_cast hshiftBound
    have : (0 : ℝ) ≤ cutoff := by exact_mod_cast hcutoff
    have : (0 : ℝ) ≤ boundary := by exact_mod_cast hboundary
    positivity
  have hh := calibratedSignResponse_l1_bound activation
    (2 * ((shiftBound : ℝ) + cutoff + 2 * boundary) / modulus)
    (fun _ : Fin modulus => (modulus : ℝ)⁻¹)
    (fun color : Fin modulus => mixedLaw modulus boundary startsPlus sources weights width color.val)
    (fun color : Fin modulus => mixedLaw modulus boundary startsMinus sources weights width color.val)
    (fun color : Fin modulus => mixedLaw modulus boundary startsPlus (fun _ => 0) weights width color.val)
    (fun color : Fin modulus => mixedLaw modulus boundary startsMinus (fun _ => 0) weights width color.val)
    ha haUpper hb hsp hsm hup hum
  exact hh.trans_eq (by ring)

/-- The fair-sign calibration is exactly the average of the two concrete
sign-conditioned calibration numerators. -/
theorem actualFairBasePrimary_eq_average {σ τ : Type*} [Fintype σ] [Fintype τ]
    (modulus margin boundary : ℤ) (width : ℕ) (bodies legs activation : ℝ)
    (bodyShifts : σ → ℤ) (bodyWeights : σ → ℝ)
    (startsPlus startsMinus sources : τ → ℤ) (weights : τ → ℝ) (color : ℤ) :
    actualFairBasePrimary modulus margin boundary width bodies legs activation bodyShifts bodyWeights
      startsPlus startsMinus sources weights color =
      (actualBasePrimary modulus margin boundary width bodies legs activation bodyShifts bodyWeights startsPlus sources weights color +
        actualBasePrimary modulus margin boundary width bodies legs activation bodyShifts bodyWeights startsMinus sources weights color) / 2 := by
  unfold actualFairBasePrimary actualBasePrimary basePrimaryProfile fairMixedLaw
  ring

/-- The true signed diffuse mean is pointwise dominated by the activation
times the computed fair-sign base primary law. -/
theorem actualSignResponse_domination {σ τ : Type*} [Fintype σ] [Fintype τ]
    (modulus margin boundary shiftBound cutoff : ℤ) (width : ℕ) (bodies legs activation : ℝ)
    (bodyShifts : σ → ℤ) (bodyWeights : σ → ℝ)
    (startsPlus startsMinus sources : τ → ℤ) (weights : τ → ℝ)
    (hq : 0 < modulus) (hlegs : 0 < legs) (hbodies : 0 ≤ bodies)
    (hactivation : 0 < activation) (hactivationUpper : activation ≤ 1 / 2)
    (hmargin : 0 ≤ margin) (hboundary : 0 ≤ boundary) (hshiftBound : 0 ≤ shiftBound)
    (hcutoff : 0 ≤ cutoff) (hwidth : width ≠ 0) (hwidthUpper : (width : ℤ) ≤ modulus)
    (hmarginSmall : 4 * margin ≤ modulus) (hdeletedSmall : 2 * (shiftBound + 2 * boundary + cutoff) ≤ modulus)
    (hbodyWeights : ∀ index, 0 ≤ bodyWeights index) (hbodyMass : ∑ index, bodyWeights index = 1)
    (hweights : ∀ index, 0 ≤ weights index) (hmass : ∑ index, weights index = 1)
    (hplus : ∀ index shift, shift ∈ anchorInterval (startsPlus index) width → |shift| ≤ shiftBound)
    (hminus : ∀ index shift, shift ∈ anchorInterval (startsMinus index) width → |shift| ≤ shiftBound)
    (hsources : ∀ index, |sources index| ≤ cutoff)
    (hloss : primaryCalibrationLoss modulus (bodies + 2 * legs) legs activation margin
      ((shiftBound : ℝ) + 2 * boundary) cutoff width ≤ 1 / 2) (color : ℤ) :
    |actualSignResponse modulus boundary startsPlus startsMinus sources weights width activation color| ≤
      activation * actualFairBasePrimary modulus margin boundary width bodies legs activation bodyShifts bodyWeights
        startsPlus startsMinus sources weights color := by
  have hqReal : 0 < (modulus : ℝ) := by exact_mod_cast hq
  have hmReal : 0 ≤ (margin : ℝ) := by exact_mod_cast hmargin
  have hbReal : 0 ≤ (boundary : ℝ) := by exact_mod_cast hboundary
  have hsReal : 0 ≤ (shiftBound : ℝ) := by exact_mod_cast hshiftBound
  have hcReal : 0 ≤ (cutoff : ℝ) := by exact_mod_cast hcutoff
  have hwReal : 0 < (width : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hwidth
  have hwUpper : (width : ℝ) ≤ modulus := by exact_mod_cast hwidthUpper
  have hmSmall : 4 * (margin : ℝ) ≤ modulus := by exact_mod_cast hmarginSmall
  have hdSmall : 2 * ((shiftBound : ℝ) + 2 * boundary + cutoff) ≤ modulus := by exact_mod_cast hdeletedSmall
  have hclearance : 2 * boundary + shiftBound + cutoff < modulus := by omega
  have hbody := blurredSafeLaw_le modulus margin bodyShifts bodyWeights hbodyWeights hbodyMass (by omega) color
  have hsp : mixedLaw modulus boundary startsPlus sources weights width color ≤
      1 / ((modulus : ℝ) - ((shiftBound : ℝ) + 2 * boundary) - cutoff) := by
    convert mixedLaw_le modulus boundary shiftBound cutoff startsPlus sources weights width hwidth
      hweights hmass hplus hsources hclearance color using 1; ring
  have hsm : mixedLaw modulus boundary startsMinus sources weights width color ≤
      1 / ((modulus : ℝ) - ((shiftBound : ℝ) + 2 * boundary) - cutoff) := by
    convert mixedLaw_le modulus boundary shiftBound cutoff startsMinus sources weights width hwidth
      hweights hmass hminus hsources hclearance color using 1; ring
  have hvp : |mixedLaw modulus boundary startsPlus sources weights width color -
      mixedLaw modulus boundary startsPlus (fun _ => 0) weights width color| ≤
      (cutoff : ℝ) / ((width : ℝ) * ((modulus : ℝ) - ((shiftBound : ℝ) + 2 * boundary) - cutoff)) := by
    convert mixedLaw_source_variation modulus boundary shiftBound cutoff startsPlus sources weights width hwidth
      hweights hmass hplus hsources hclearance color using 1; ring
  have hvm : |mixedLaw modulus boundary startsMinus sources weights width color -
      mixedLaw modulus boundary startsMinus (fun _ => 0) weights width color| ≤
      (cutoff : ℝ) / ((width : ℝ) * ((modulus : ℝ) - ((shiftBound : ℝ) + 2 * boundary) - cutoff)) := by
    convert mixedLaw_source_variation modulus boundary shiftBound cutoff startsMinus sources weights width hwidth
      hweights hmass hminus hsources hclearance color using 1; ring
  have hh := calibratedSignResponse_scalar_bound modulus bodies legs activation margin
    ((shiftBound : ℝ) + 2 * boundary) cutoff width (blurredSafeLaw modulus margin bodyShifts bodyWeights color)
    (mixedLaw modulus boundary startsPlus sources weights width color)
    (mixedLaw modulus boundary startsMinus sources weights width color)
    (mixedLaw modulus boundary startsPlus (fun _ => 0) weights width color)
    (mixedLaw modulus boundary startsMinus (fun _ => 0) weights width color)
    hqReal hlegs hbodies hactivation hactivationUpper hmReal (by positivity) hcReal hwReal hwUpper
    hmSmall hdSmall hbody hsp hsm hvp hvm hloss
  simpa only [actualSignResponse, actualFairBasePrimary, basePrimaryProfile, fairMixedLaw, mul_one_div] using hh

end TrimmedSlice

end AFT
