import CurrentAFT.RationalBackgroundProfiles
import CurrentAFT.RationalMassLiftProgram
import CurrentAFT.CalibrationCoordinateError

/-! # Numerical densities of the original mixed background certificates -/
namespace CurrentAFT.RationalBackgroundDensities
open AFT RationalNumerics DiffuseProfiles ProposalPrimary ActualControls BackgroundCertificates BackgroundTranslations
open scoped BigOperators
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base PublicParameterProgram.modulus primaryLaw centerLaw

def primary (security bits output : ℕ) : ℚ :=
  RationalMassLiftProgram.current security bits (RationalBackgroundProfiles.bodyDeviation security bits) output

def residual (security bits : ℕ) (shift : ℤ) (output : ℕ) : ℚ :=
  RationalMassLiftProgram.current security bits (RationalBackgroundProfiles.residual security bits shift) output

def body (security bits output : ℕ) : ℚ :=
  1-RationalBackgroundProfiles.safe security output/RationalProposalProgram.center security bits output

def seed (security bits : ℕ) (shift : ℤ) (output : ℕ) : ℚ :=
  RationalBackgroundProfiles.seedProfile security shift output/RationalProposalProgram.center security bits output

noncomputable section
open scoped Classical

def centerErrorConstant (security : ℕ) : ℝ :=
  64*(Parameters.base security:ℝ)*Parameters.dimension security*Parameters.modulus security+2

def primaryErrorConstant (security : ℕ) : ℝ :=
  2*RationalMassLiftProgram.errorConstant security+3*RationalTensorInverseProgram.actualBound security

def residualErrorConstant (security : ℕ) : ℝ :=
  2*RationalMassLiftProgram.errorConstant security+6*RationalTensorInverseProgram.actualBound security

def bodyErrorConstant (security : ℕ) : ℝ := (2*(Parameters.modulus security:ℝ))^2*centerErrorConstant security

theorem primary_actual (security : ℕ) (output : FirstHistogram.Palette security) :
    RationalMassLiftProgram.actual security (FringeCertificate.bodyDeviation security) output =
      FringeCertificate.primaryCertificateDensity security output := by
  rw [RationalMassLiftProgram.actual_formula]
  unfold FringeCertificate.primaryCertificateDensity FringeCertificate.primaryCertificateProfile
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem residual_actual (security : ℕ) (shift : ℤ) (output : FirstHistogram.Palette security) :
    RationalMassLiftProgram.actual security (BackgroundTranslations.translationResidual security shift) output =
      BackgroundTranslations.residualCertificateDensity security shift output := by
  rw [RationalMassLiftProgram.actual_formula]
  unfold BackgroundTranslations.residualCertificateDensity BackgroundTranslations.residualCertificateProfile
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem bodyDeviation_bound (security bits : ℕ) (output : FirstHistogram.Palette security) :
    |(RationalBackgroundProfiles.bodyDeviation security bits output.val:ℝ)| ≤ 2 := by
  have hn := (RationalProposalProgram.approximateBodyLaw security bits false).nonneg output
  have hu := (RationalProposalProgram.approximateBodyLaw security bits false).atom_le_one output
  have hq : (1:ℝ) ≤ Parameters.modulus security := by exact_mod_cast (Parameters.modulus_spec security).2.pos
  have hi : 0 ≤ (Parameters.modulus security:ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
  have hi' : (Parameters.modulus security:ℝ)⁻¹ ≤ 1 := by
    simpa only [one_div, inv_one] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hq
  simp only [RationalBackgroundProfiles.bodyDeviation, RationalBackgroundProfiles.colors, Rat.cast_sub, one_div,
    Rat.cast_inv, Rat.cast_natCast, PublicParameterProgram.modulus_value, RationalProposalProgram.body_cast]
  rw [abs_le]
  constructor <;> linarith

theorem residual_bound (security bits : ℕ) (shift : ℤ) (output : FirstHistogram.Palette security) :
    |(RationalBackgroundProfiles.residual security bits shift output.val:ℝ)| ≤ 2 := by
  have hu (color : FirstHistogram.Palette security) : |BackgroundTranslations.unsafePart security shift color| ≤ 1 := by
    rw [abs_of_nonneg (BackgroundTranslations.unsafePart_nonneg security shift color)]
    exact (BackgroundTranslations.unsafePart_le_shifted security shift color).trans ((shiftedSafeLaw security shift).atom_le_one color)
  have hc : |(RationalBackgroundProfiles.convolution security bits (RationalBackgroundProfiles.unsafeProfile security shift) output.val:ℝ)| ≤ 1 := by
    rw [RationalBackgroundProfiles.convolution_cast]
    simp_rw [RationalBackgroundProfiles.unsafe_cast]
    exact CalibrationCoordinateError.expectation_abs_bound _ _ 1 (fun seed => hu _)
  have hm := BackgroundTranslations.unsafeMass_le_one security shift
  have hn := BackgroundTranslations.unsafeMass_nonneg security shift
  have hb := (RationalProposalProgram.approximateBodyLaw security bits false).atom_le_one output
  have hbn := (RationalProposalProgram.approximateBodyLaw security bits false).nonneg output
  simp only [RationalBackgroundProfiles.residual, Rat.cast_sub, Rat.cast_mul, RationalBackgroundProfiles.unsafeTotal_cast,
    RationalProposalProgram.body_cast]
  apply (abs_sub _ _).trans
  rw [abs_mul, abs_of_nonneg hn, abs_of_nonneg hbn]
  exact (add_le_add hc (mul_le_mul hm hb hbn (by norm_num))).trans_eq (by norm_num)

theorem primary_error (security bits : ℕ) (output : FirstHistogram.Palette security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ))) :
    |(primary security bits output.val:ℝ)-FringeCertificate.primaryCertificateDensity security output| ≤
      primaryErrorConstant security*(1/(2:ℝ)^bits) := by
  rw [primary, ← primary_actual]
  exact (RationalMassLiftProgram.current_profile_error security bits (RationalBackgroundProfiles.bodyDeviation security bits)
    (FringeCertificate.bodyDeviation security) 2 (3/(2:ℝ)^bits) (by norm_num) (by positivity)
    (bodyDeviation_bound security bits) (RationalBackgroundProfiles.bodyDeviation_error security bits)
    hfirst hprecision hbudget output).trans_eq (by unfold primaryErrorConstant; ring)

theorem residual_error (security bits : ℕ) (shift : ℤ) (output : FirstHistogram.Palette security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ))) :
    |(residual security bits shift output.val:ℝ)-BackgroundTranslations.residualCertificateDensity security shift output| ≤
      residualErrorConstant security*(1/(2:ℝ)^bits) := by
  rw [residual, ← residual_actual]
  exact (RationalMassLiftProgram.current_profile_error security bits (RationalBackgroundProfiles.residual security bits shift)
    (BackgroundTranslations.translationResidual security shift) 2 (6/(2:ℝ)^bits) (by norm_num) (by positivity)
    (residual_bound security bits shift) (RationalBackgroundProfiles.residual_error security bits shift)
    hfirst hprecision hbudget output).trans_eq (by unfold residualErrorConstant; ring)

theorem safe_quotient_error (security bits : ℕ) (numerator : ℕ → ℚ) (profile : FirstHistogram.Palette security → ℝ)
    (bound : ℝ) (hb : 0 ≤ bound) (hnum : ∀ color, (numerator color.val:ℝ) = profile color)
    (hbound : ∀ color, |profile color| ≤ bound) (output : SafePalette security)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ))) :
    |(numerator output.val.val/RationalProposalProgram.center security bits output.val.val:ℚ)-
      profile output.val/(centerLaw security).weight output.val| ≤
      bound*bodyErrorConstant security*(1/(2:ℝ)^bits) := by
  let q : ℝ := Parameters.modulus security
  have hq : 0 < q := FirstResponse.modulus_pos security
  have ha := RationalProposalProgram.center_lower_safe security bits output
  have hb' : 1/(2*q) ≤ (centerLaw security).weight output.val := ActualControls.bodyReference_lower security output
  have hd : |(RationalProposalProgram.center security bits output.val.val:ℝ)-(centerLaw security).weight output.val| ≤
      centerErrorConstant security*(1/(2:ℝ)^bits) := by
    simpa only [centerLaw, centerErrorConstant] using RationalProposalProgram.center_error security bits output.val hprecision hbudget
  have hx := RationalDensityInverseProgram.quotient_error (profile output.val) (profile output.val)
    (RationalProposalProgram.center security bits output.val.val:ℝ) ((centerLaw security).weight output.val)
    (1/(2*q)) 0 (centerErrorConstant security*(1/(2:ℝ)^bits)) bound (by positivity) ha hb'
    (by norm_num) (by unfold centerErrorConstant; positivity) hb (by simp) hd (hbound output.val)
  rw [Rat.cast_div, hnum]
  apply hx.trans_eq
  unfold bodyErrorConstant
  dsimp only [q]
  ring_nf
  simp only [inv_inv]

theorem body_formula (security : ℕ) (output : SafePalette security) :
    BackgroundCertificates.bodyCertificateDensity security output.val =
      1-(safeLaw security).weight output.val/(centerLaw security).weight output.val := by
  have hb : (centerLaw security).weight output.val ≠ 0 := ne_of_gt (bodyReference_positive security output)
  unfold BackgroundCertificates.bodyCertificateDensity BackgroundCertificates.bodyCertificateProfile
  field_simp [hb]

theorem body_error (security bits : ℕ) (output : SafePalette security)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ))) :
    |(body security bits output.val.val:ℝ)-BackgroundCertificates.bodyCertificateDensity security output.val| ≤
      bodyErrorConstant security*(1/(2:ℝ)^bits) := by
  have hs (color : FirstHistogram.Palette security) : |(safeLaw security).weight color| ≤ 1 := by
    rw [abs_of_nonneg ((safeLaw security).nonneg color)]
    exact (safeLaw security).atom_le_one color
  have hx := safe_quotient_error security bits (RationalBackgroundProfiles.safe security) (safeLaw security).weight 1
    (by norm_num) (RationalBackgroundProfiles.safe_cast security) hs output hprecision hbudget
  have he : (body security bits output.val.val:ℝ)-BackgroundCertificates.bodyCertificateDensity security output.val =
      -((RationalBackgroundProfiles.safe security output.val.val/RationalProposalProgram.center security bits output.val.val:ℚ)-
        (safeLaw security).weight output.val/(centerLaw security).weight output.val) := by
    rw [body, Rat.cast_sub, Rat.cast_one, body_formula]
    ring
  rw [he, abs_neg]
  simpa only [one_mul] using hx

theorem seedProfile_bound (security : ℕ) (shift : ℤ) (output : FirstHistogram.Palette security) :
    |BackgroundTranslations.safeSeedProfile security shift output| ≤ 2 := by
  let projectedLaw : FiniteDist (FirstHistogram.Palette security) :=
    { weight := BackgroundTranslations.projectedShiftProfile security shift
      nonneg := BackgroundTranslations.projectedShiftProfile_nonneg security shift
      sum_one := BackgroundTranslations.projectedShiftProfile_mass security shift }
  have hp0 := projectedLaw.nonneg output
  have hp1 := projectedLaw.atom_le_one output
  have hs0 := (safeLaw security).nonneg output
  have hs1 := (safeLaw security).atom_le_one output
  unfold BackgroundTranslations.safeSeedProfile
  apply (abs_sub _ _).trans
  rw [abs_of_nonneg hp0, abs_of_nonneg hs0]
  exact (add_le_add hp1 hs1).trans_eq (by norm_num)

theorem seed_error (security bits : ℕ) (shift : ℤ) (output : SafePalette security)
    (hprecision : 1/(2:ℝ)^bits ≤ 1/(4*(Parameters.base security:ℝ)))
    (hbudget : 64*(Parameters.base security:ℝ)*Parameters.dimension security*(1/(2:ℝ)^bits) ≤ 1/(4*(Parameters.modulus security:ℝ))) :
    |(seed security bits shift output.val.val:ℝ)-BackgroundTranslations.safeSeedDensity security shift output.val| ≤
      2*bodyErrorConstant security*(1/(2:ℝ)^bits) := by
  exact safe_quotient_error security bits (RationalBackgroundProfiles.seedProfile security shift)
    (BackgroundTranslations.safeSeedProfile security shift) 2 (by norm_num)
    (RationalBackgroundProfiles.seedProfile_cast security shift) (seedProfile_bound security shift) output hprecision hbudget

end
end CurrentAFT.RationalBackgroundDensities
