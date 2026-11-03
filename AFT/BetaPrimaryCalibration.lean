import AFT.PrimaryCalibrationParameters
import AFT.TrimmedPalette
import AFT.SignCalibrationParameters

/-!
# The beta boundary-mass repair preserves the actual primary lower bound
-/

namespace AFT

open Filter
open scoped BigOperators Topology

noncomputable def uniformFiniteProfile {ι : Type*} [DecidableEq ι] (support : Finset ι) (color : ι) : ℝ :=
  if color ∈ support then (support.card : ℝ)⁻¹ else 0

/-- The exact beta repair halves the base law at worst when its boundary
mass is within the typical factor-two range and the interior debit is small. -/
theorem betaPrimaryRepair_ge_half {ι : Type*} [Fintype ι] [DecidableEq ι]
    (boundary : Finset ι) (base : ι → ℝ) (baseMass repairedMass : ℝ)
    (hmassLower : baseMass / 2 ≤ repairedMass) (hmassUpper : repairedMass ≤ 2 * baseMass)
    (hboundary : ∀ color ∈ boundary, base color = baseMass / boundary.card)
    (hinterior : ∀ color ∉ boundary, 2 * baseMass / (boundaryᶜ.card : ℝ) ≤ base color) :
    ∀ color, base color / 2 ≤ calibratedPrimaryProfile base
      (uniformFiniteProfile boundary) (uniformFiniteProfile boundaryᶜ) (repairedMass - baseMass) color := by
  intro color
  by_cases hc : color ∈ boundary
  · simp only [calibratedPrimaryProfile, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
      smul_eq_mul, uniformFiniteProfile, Finset.mem_compl]
    simp only [hc, not_true_eq_false, if_true, if_false, sub_zero]
    rw [hboundary color hc]
    have hh := div_le_div_of_nonneg_right hmassLower (Nat.cast_nonneg boundary.card)
    simp only [div_eq_mul_inv] at hh ⊢
    nlinarith only [hh]
  · simp only [calibratedPrimaryProfile, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
      smul_eq_mul, uniformFiniteProfile, Finset.mem_compl]
    simp only [hc, not_false_eq_true, if_false, if_true, zero_sub]
    have hh := mul_le_mul_of_nonneg_right hmassUpper (inv_nonneg.mpr (Nat.cast_nonneg boundaryᶜ.card))
    have hi := hinterior color hc
    simp only [div_eq_mul_inv] at hi
    nlinarith only [hh, hi]

/-- The factor-two typical beta interval gives exactly the factor-two
boundary-mass interval, including its actual reciprocal-beta formula. -/
theorem beta_boundary_mass_bounds (dimension legs activation boundaryFraction beta : ℝ)
    (hdimension : 0 < dimension) (hlegs : 0 < legs) (hactivation : 0 < activation)
    (hboundary : 0 ≤ boundaryFraction)
    (hbetaLower : legs / (2 * dimension) ≤ beta) (hbetaUpper : beta ≤ 2 * legs / dimension) :
    (dimension * boundaryFraction / (legs * activation)) / 2 ≤ boundaryFraction / (activation * beta) ∧
      boundaryFraction / (activation * beta) ≤ 2 * (dimension * boundaryFraction / (legs * activation)) := by
  have hbeta : 0 < beta := lt_of_lt_of_le (by positivity) hbetaLower
  constructor
  · calc
      _ = boundaryFraction / (activation * (2 * legs / dimension)) := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_left hboundary (by positivity)
        (mul_le_mul_of_nonneg_left hbetaUpper hactivation.le)
  · calc
      _ ≤ boundaryFraction / (activation * (legs / (2 * dimension))) :=
        div_le_div_of_nonneg_left hboundary (by positivity)
          (mul_le_mul_of_nonneg_left hbetaLower hactivation.le)
      _ = _ := by field_simp

/-- The real V7 boundary palette is the complement of the zero-shift trimmed interval. -/
def boundaryPalette (modulus : ℕ) (halfWidth : ℤ) : Finset (Fin modulus) :=
  (TrimmedSlice.paletteSlice modulus halfWidth 0)ᶜ

theorem mem_boundaryPalette (modulus : ℕ) (halfWidth : ℤ) (color : Fin modulus) :
    color ∈ boundaryPalette modulus halfWidth ↔
      (color.val : ℤ) < halfWidth ∨ (modulus : ℤ) - 1 - halfWidth < color.val := by
  simp only [boundaryPalette, Finset.mem_compl, TrimmedSlice.paletteSlice, Finset.mem_filter,
    Finset.mem_univ, true_and, TrimmedSlice.mem_slice]
  omega

theorem boundaryPalette_card (modulus : ℕ) (halfWidth : ℤ)
    (hh : 0 ≤ halfWidth) (hsmall : 2 * halfWidth ≤ modulus) :
    ((boundaryPalette modulus halfWidth).card : ℤ) = 2 * halfWidth := by
  rw [boundaryPalette, Finset.card_compl, Fintype.card_fin,
    TrimmedSlice.paletteSlice_card modulus halfWidth 0 hh]
  simp only [abs_zero, Int.sub_zero]
  omega

theorem boundaryPalette_compl_card (modulus : ℕ) (halfWidth : ℤ)
    (hh : 0 ≤ halfWidth) (hsmall : 2 * halfWidth ≤ modulus) :
    ((boundaryPalette modulus halfWidth)ᶜ.card : ℤ) = (modulus : ℤ) - 2 * halfWidth := by
  simp only [boundaryPalette, compl_compl]
  rw [TrimmedSlice.paletteSlice_card modulus halfWidth 0 hh]
  simp only [abs_zero, Int.sub_zero]
  omega

noncomputable def v7BaseBoundaryMass (cutoffScale : ℝ) (parameter : ℕ) (boundaryHalfWidth : ℤ) : ℝ :=
  (Parameters.dimension parameter : ℝ) * (boundaryPalette (Parameters.modulus parameter) boundaryHalfWidth).card /
    ((Parameters.modulus parameter : ℝ) * Parameters.legs parameter * GaussianSource.v7Activation cutoffScale parameter)

theorem boundaryMass_power_bound (security modulus activation boundarySize : ℝ)
    (hx : 0 < security) (hq : 0 < modulus) (ha : 1 / security ^ 5 ≤ activation)
    (hb : boundarySize ≤ 40 * security ^ 2) :
    (modulus * security ^ 20) * boundarySize / (modulus * security ^ 30 * activation) ≤
      40 / security ^ 3 := by
  have hap : 0 < activation := lt_of_lt_of_le (by positivity) ha
  have hinv : 1 / activation ≤ security ^ 5 := by
    simpa only [one_div_one_div] using one_div_le_one_div_of_le (by positivity : 0 < 1 / security ^ 5) ha
  calc
    _ ≤ (modulus * security ^ 20) * (40 * security ^ 2) / (modulus * security ^ 30 * activation) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by positivity)) (by positivity)
    _ = (40 / security ^ 8) * (1 / activation) := by field_simp
    _ ≤ (40 / security ^ 8) * security ^ 5 := mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = _ := by field_simp

/-- The actual boundary debit is eventually below half the proven base
primary lower bound, uniformly over all permitted boundary half-widths. -/
theorem v7_boundary_debit_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (boundary : ℕ → ℤ)
    (hboundary : ∀ᶠ parameter in atTop,
      0 ≤ boundary parameter ∧ boundary parameter ≤ Parameters.safeMargin parameter) :
    ∀ᶠ parameter in atTop,
      2 * v7BaseBoundaryMass cutoffScale parameter (boundary parameter) /
        ((boundaryPalette (Parameters.modulus parameter) (boundary parameter))ᶜ.card : ℝ) ≤
      1 / (2 * (Parameters.modulus parameter : ℝ)) := by
  have hsmall := ((tendsto_const_div_pow (40 : ℝ) 3 (by decide)).comp Parameters.security_tendsto).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))
  filter_upwards [hboundary, hsmall,
    GaussianSource.v7Activation_lower_eventually cutoffScale hscale,
    v7_primaryCalibration_clearance_eventually cutoffScale hscale boundary hboundary,
    eventually_ge_atTop 2] with parameter hb hsmall ha hclear hlarge
  have hx : 0 < (Parameters.security parameter : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2) (Parameters.security_ge_two parameter)
  have hq : 0 < (Parameters.modulus parameter : ℝ) := by exact_mod_cast (Parameters.modulus_prime parameter).pos
  have hhalf : 2 * boundary parameter ≤ Parameters.modulus parameter := by omega
  have hcard := boundaryPalette_card (Parameters.modulus parameter) (boundary parameter) hb.1 hhalf
  have hcompl := boundaryPalette_compl_card (Parameters.modulus parameter) (boundary parameter) hb.1 hhalf
  have hcardReal : ((boundaryPalette (Parameters.modulus parameter) (boundary parameter)).card : ℝ) ≤
      40 * (Parameters.security parameter : ℝ) ^ 2 := by
    have hh : ((boundaryPalette (Parameters.modulus parameter) (boundary parameter)).card : ℤ) ≤
        2 * Parameters.safeMargin parameter := by omega
    have hhReal : ((boundaryPalette (Parameters.modulus parameter) (boundary parameter)).card : ℝ) ≤
        2 * (Parameters.safeMargin parameter : ℝ) := by exact_mod_cast hh
    simp only [Parameters.safeMargin, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] at hhReal
    nlinarith only [hhReal]
  have ha' : 1 / (Parameters.security parameter : ℝ) ^ 5 ≤ GaussianSource.v7Activation cutoffScale parameter := by
    simpa only [Parameters.security_eq parameter hlarge, one_div] using ha
  have hmass : v7BaseBoundaryMass cutoffScale parameter (boundary parameter) ≤ 40 / (Parameters.security parameter : ℝ) ^ 3 := by
    have hh := boundaryMass_power_bound (Parameters.security parameter) (Parameters.modulus parameter)
      (GaussianSource.v7Activation cutoffScale parameter)
      (boundaryPalette (Parameters.modulus parameter) (boundary parameter)).card hx hq ha' hcardReal
    simpa only [v7BaseBoundaryMass, Parameters.dimension, Parameters.meanDensity, Parameters.legs,
      Nat.cast_mul, Nat.cast_pow] using hh
  have hcomplReal : (Parameters.modulus parameter : ℝ) / 2 ≤
      ((boundaryPalette (Parameters.modulus parameter) (boundary parameter))ᶜ.card : ℝ) := by
    have hh : (Parameters.modulus parameter : ℤ) ≤
        2 * ((boundaryPalette (Parameters.modulus parameter) (boundary parameter))ᶜ.card : ℤ) := by omega
    have hh' : (Parameters.modulus parameter : ℝ) ≤
        2 * ((boundaryPalette (Parameters.modulus parameter) (boundary parameter))ᶜ.card : ℝ) := by exact_mod_cast hh
    linarith
  have hcomplPos : 0 < ((boundaryPalette (Parameters.modulus parameter) (boundary parameter))ᶜ.card : ℝ) :=
    (half_pos hq).trans_le hcomplReal
  apply (div_le_iff₀ hcomplPos).mpr
  have hmassSmall := hmass.trans hsmall.le
  have hscaled := mul_le_mul_of_nonneg_left hcomplReal (by positivity : 0 ≤ 1 / (2 * (Parameters.modulus parameter : ℝ)))
  have hquarter : 1 / (2 * (Parameters.modulus parameter : ℝ)) * ((Parameters.modulus parameter : ℝ) / 2) = 1 / 4 := by field_simp; norm_num
  rw [hquarter] at hscaled
  linarith

namespace TrimmedSlice

/-- Physical body blur support keeps the entire boundary strip empty. -/
theorem blurredSafeLaw_zero_boundary {σ : Type*} [Fintype σ]
    (modulus margin boundary : ℤ) (shifts : σ → ℤ) (weights : σ → ℝ)
    (hwidth : 2 * margin ≤ modulus) (hshift : ∀ index, |shifts index| ≤ margin - boundary)
    (color : ℤ) (hout : color < boundary ∨ modulus - 1 - boundary < color) :
    blurredSafeLaw modulus margin shifts weights color = 0 := by
  have hcast : ((modulus - 2 * margin).toNat : ℤ) = modulus - 2 * margin := Int.toNat_of_nonneg (by omega)
  unfold blurredSafeLaw
  apply Finset.sum_eq_zero
  intro index _
  have hh := abs_le.mp (hshift index)
  have hnot : color - shifts index ∉ anchorInterval margin (modulus - 2 * margin).toNat := by
    simp only [anchorInterval, Finset.mem_Ico, hcast]
    omega
  simp [intervalAnchorLaw, hnot]

/-- On the boundary the actual calibrated numerator has exactly its
constant `dimension/(q * legs * activation)` value. -/
theorem actualBasePrimary_boundary {σ τ : Type*} [Fintype σ] [Fintype τ]
    (modulus margin boundary : ℤ) (width : ℕ) (bodies legs activation : ℝ)
    (bodyShifts : σ → ℤ) (bodyWeights : σ → ℝ)
    (starts sources : τ → ℤ) (weights : τ → ℝ)
    (hwidth : 2 * margin ≤ modulus) (hshift : ∀ index, |bodyShifts index| ≤ margin - boundary)
    (color : ℤ) (hout : color < boundary ∨ modulus - 1 - boundary < color) :
    actualBasePrimary modulus margin boundary width bodies legs activation bodyShifts bodyWeights starts sources weights color =
      (bodies + 2 * legs) / ((modulus : ℝ) * legs * activation) := by
  simp only [actualBasePrimary, basePrimaryProfile,
    blurredSafeLaw_zero_boundary modulus margin boundary bodyShifts bodyWeights hwidth hshift color hout,
    mixedLaw_zero_boundary _ _ _ _ _ _ _ hout, mul_zero, sub_zero, add_zero]
  ring

/-- A safe center after a supported physical blur is still a normalized
law on the finite output palette. -/
theorem blurredSafeLaw_palette_mass {σ : Type*} [Fintype σ]
    (modulus : ℕ) (margin : ℤ) (shifts : σ → ℤ) (weights : σ → ℝ)
    (hmass : ∑ index, weights index = 1) (hwidth : 2 * margin < modulus)
    (hshift : ∀ index, |shifts index| ≤ margin) :
    ∑ color : Fin modulus, blurredSafeLaw modulus margin shifts weights color.val = 1 := by
  have hcast : (((modulus : ℤ) - 2 * margin).toNat : ℤ) = (modulus : ℤ) - 2 * margin :=
    Int.toNat_of_nonneg (by omega)
  have hwidthNat : ((modulus : ℤ) - 2 * margin).toNat ≠ 0 := by omega
  have hrow (index : σ) :
      ∑ color : Fin modulus, intervalAnchorLaw margin ((modulus : ℤ) - 2 * margin).toNat
        ((color.val : ℤ) - shifts index) = 1 := by
    have heq (color : ℤ) : intervalAnchorLaw margin ((modulus : ℤ) - 2 * margin).toNat
        (color - shifts index) = intervalAnchorLaw (margin + shifts index)
          ((modulus : ℤ) - 2 * margin).toNat color := by
      have hm : color - shifts index ∈ anchorInterval margin ((modulus : ℤ) - 2 * margin).toNat ↔
          color ∈ anchorInterval (margin + shifts index) ((modulus : ℤ) - 2 * margin).toNat := by
        simp only [anchorInterval, Finset.mem_Ico]
        omega
      simp only [intervalAnchorLaw, hm]
    simp_rw [heq]
    rw [finitePalette_sum_eq_support (fun color : Fin modulus => (color.val : ℤ))
      (by intro a b heq; dsimp only at heq; apply Fin.ext; exact_mod_cast heq)
      (anchorInterval (margin + shifts index) ((modulus : ℤ) - 2 * margin).toNat)]
    · exact intervalAnchorLaw_mass _ _ hwidthNat
    · intro color hc
      have hs := abs_le.mp (hshift index)
      simp only [anchorInterval, Finset.mem_Ico, hcast] at hc
      have hcolor : 0 ≤ color ∧ color < modulus := by omega
      refine Finset.mem_image.mpr ⟨⟨color.toNat, by omega⟩, Finset.mem_univ _, ?_⟩
      dsimp only
      omega
    · intro color hc
      simp [intervalAnchorLaw, hc]
  unfold blurredSafeLaw
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hrow, mul_one]
  exact hmass

theorem actualFairBasePrimary_palette_mass {σ τ : Type*} [Fintype σ] [Fintype τ]
    (modulus : ℕ) (margin boundary shiftBound cutoff : ℤ) (width : ℕ)
    (bodies legs activation : ℝ) (bodyShifts : σ → ℤ) (bodyWeights : σ → ℝ)
    (startsPlus startsMinus sources : τ → ℤ) (weights : τ → ℝ)
    (hq : modulus ≠ 0) (hmark : legs * activation ≠ 0) (hwidth : width ≠ 0)
    (hbodyMass : ∑ index, bodyWeights index = 1) (hbodyWidth : 2 * margin < modulus)
    (hbodyShifts : ∀ index, |bodyShifts index| ≤ margin)
    (hmass : ∑ index, weights index = 1) (hboundary : 0 ≤ boundary) (hcutoff : 0 ≤ cutoff)
    (hplus : ∀ index shift, shift ∈ anchorInterval (startsPlus index) width → |shift| ≤ shiftBound)
    (hminus : ∀ index shift, shift ∈ anchorInterval (startsMinus index) width → |shift| ≤ shiftBound)
    (hsources : ∀ index, |sources index| ≤ cutoff)
    (hclearance : 2 * boundary + shiftBound + cutoff < modulus) :
    ∑ color : Fin modulus, actualFairBasePrimary modulus margin boundary width bodies legs activation
      bodyShifts bodyWeights startsPlus startsMinus sources weights color.val = 1 := by
  have hb := blurredSafeLaw_palette_mass modulus margin bodyShifts bodyWeights hbodyMass hbodyWidth hbodyShifts
  have hsp := mixedLaw_palette_mass modulus boundary shiftBound cutoff width hwidth startsPlus sources weights hmass hboundary hplus hsources hclearance
  have hsm := mixedLaw_palette_mass modulus boundary shiftBound cutoff width hwidth startsMinus sources weights hmass hboundary hminus hsources hclearance
  have hup := mixedLaw_palette_mass modulus boundary shiftBound cutoff width hwidth startsPlus (fun _ => 0) weights hmass hboundary hplus (by simpa using fun _ : τ => hcutoff) hclearance
  have hum := mixedLaw_palette_mass modulus boundary shiftBound cutoff width hwidth startsMinus (fun _ => 0) weights hmass hboundary hminus (by simpa using fun _ : τ => hcutoff) hclearance
  have hu : (∑ _color : Fin modulus, 1 / (modulus : ℝ)) = 1 := by simp [hq]
  change signedProfileMass (basePrimaryProfile (bodies + 2 * legs) bodies legs activation
    (fun _ : Fin modulus => 1 / (modulus : ℝ))
    (fun color : Fin modulus => blurredSafeLaw modulus margin bodyShifts bodyWeights color.val)
    (fun color : Fin modulus => fairMixedLaw modulus boundary startsPlus startsMinus sources weights width color.val)
    (fun color : Fin modulus => fairMixedLaw modulus boundary startsPlus startsMinus (fun _ => 0) weights width color.val)) = 1
  apply basePrimaryProfile_mass _ _ _ _ _ _ _ _ hmark rfl hu hb
  · simp only [signedProfileMass_apply, fairMixedLaw, ← Finset.sum_div,
      Finset.sum_add_distrib, hsp, hsm]
    norm_num
  · simp only [signedProfileMass_apply, fairMixedLaw, ← Finset.sum_div,
      Finset.sum_add_distrib, hup, hum]
    norm_num

end TrimmedSlice

end AFT
