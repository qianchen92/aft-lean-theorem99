import CurrentAFT.RationalProposalProgram
import CurrentAFT.BackgroundTranslations
import CurrentAFT.ProposalSymmetry
import CurrentAFT.CalibrationCoordinateError

/-! # Literal rational profiles for the current mixed background data

Safe projections are exact rational finite sums.  Root convolutions keep
both Gaussian edges and use the same local seed law as the actual model.
-/
namespace CurrentAFT.RationalBackgroundProfiles
open AFT GaussianSource RationalNumerics DiffuseProfiles ProposalPrimary BackgroundCertificates BackgroundTranslations
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus Parameters.base Parameters.safeMargin

abbrev colors (security : ℕ) := (PublicParameterProgram.modulus security).count

def margin (security : ℕ) : ℕ := 3*(security+2)^2

def safe (security output : ℕ) : ℚ := RationalProposalProgram.safeEntry (colors security) (margin security) output

def shifted (security : ℕ) (shift : ℤ) (output : ℕ) : ℚ :=
  RationalProposalProgram.bodyKernel (colors security) (margin security) shift output

def Safe (security output : ℕ) : Prop :=
  (margin security:ℤ) ≤ output ∧ (output:ℤ) < (colors security:ℤ)-margin security

instance safeDecidable (security output : ℕ) : Decidable (Safe security output) := by unfold Safe; infer_instance

def unsafeProfile (security : ℕ) (shift : ℤ) (output : ℕ) : ℚ :=
  if Safe security output then 0 else shifted security shift output

def unsafeTotal (security : ℕ) (shift : ℤ) : ℚ :=
  ∑ output : Fin (colors security), unsafeProfile security shift output.val

def projected (security : ℕ) (shift : ℤ) (output : ℕ) : ℚ :=
  shifted security shift output-unsafeProfile security shift output+unsafeTotal security shift*safe security output

def seedProfile (security : ℕ) (shift : ℤ) (output : ℕ) : ℚ := projected security shift output-safe security output

def inverseShift (security : ℕ) (shift : ℤ) (output : ℕ) : ℕ :=
  (((output:ℤ)-shift) % (colors security:ℤ)).toNat

def convolution (security bits : ℕ) (profile : ℕ → ℚ) (output : ℕ) : ℚ :=
  RationalProposalProgram.seedEvaluate security bits (fun seed =>
    profile (inverseShift security (seed.1.1.val-seed.1.2.val) output))

def bodyDeviation (security bits output : ℕ) : ℚ :=
  RationalProposalProgram.body security bits false output-1/(colors security:ℚ)

def residual (security bits : ℕ) (shift : ℤ) (output : ℕ) : ℚ :=
  convolution security bits (unsafeProfile security shift) output-
    unsafeTotal security shift*RationalProposalProgram.body security bits false output

noncomputable section
open scoped Classical

theorem margin_value (security : ℕ) : margin security = Parameters.safeMargin security := by
  simp only [margin, Parameters.safeMargin, Parameters.sourceCutoff, Parameters.base]

theorem safe_cast (security : ℕ) (output : FirstHistogram.Palette security) :
    (safe security output.val:ℝ) = (safeLaw security).weight output := by
  unfold safe RationalProposalProgram.safeEntry
  rw [colors, PublicParameterProgram.modulus_value, margin_value, AFT.V7Calibration.sliceProbabilityProgram_cast]
  rw [safeLaw, TrimmedSlice.finiteLaw_weight]

theorem shifted_cast (security : ℕ) (shift : ℤ) (output : FirstHistogram.Palette security) :
    (shifted security shift output.val:ℝ) = (shiftedSafeLaw security shift).weight output := by
  unfold shifted
  rw [colors, PublicParameterProgram.modulus_value, margin_value]
  exact RationalProposalProgram.bodyKernel_cast security shift output

theorem safe_iff (security : ℕ) (output : FirstHistogram.Palette security) :
    Safe security output.val ↔ InwardAnchor.SafeColor security output := by
  unfold Safe InwardAnchor.SafeColor
  rw [colors, PublicParameterProgram.modulus_value, margin_value]

theorem unsafe_cast (security : ℕ) (shift : ℤ) (output : FirstHistogram.Palette security) :
    (unsafeProfile security shift output.val:ℝ) = BackgroundTranslations.unsafePart security shift output := by
  unfold unsafeProfile BackgroundTranslations.unsafePart
  by_cases h : InwardAnchor.SafeColor security output
  · rw [if_pos ((safe_iff security output).mpr h), if_pos h]
    exact Rat.cast_zero
  · rw [if_neg (fun hs => h ((safe_iff security output).mp hs)), if_neg h]
    exact shifted_cast security shift output

theorem unsafeTotal_cast (security : ℕ) (shift : ℤ) :
    (unsafeTotal security shift:ℝ) = BackgroundTranslations.unsafeMass security shift := by
  unfold unsafeTotal BackgroundTranslations.unsafeMass
  rw [Rat.cast_sum]
  have he : colors security = Parameters.modulus security := PublicParameterProgram.modulus_value security
  rw [he]
  apply Finset.sum_congr (by ext; simp)
  intro output _
  exact unsafe_cast security shift output

theorem projected_cast (security : ℕ) (shift : ℤ) (output : FirstHistogram.Palette security) :
    (projected security shift output.val:ℝ) = BackgroundTranslations.projectedShiftProfile security shift output := by
  simp only [projected, Rat.cast_add, Rat.cast_sub, Rat.cast_mul, shifted_cast, unsafe_cast,
    unsafeTotal_cast, safe_cast, BackgroundTranslations.projectedShiftProfile]

theorem seedProfile_cast (security : ℕ) (shift : ℤ) (output : FirstHistogram.Palette security) :
    (seedProfile security shift output.val:ℝ) = BackgroundTranslations.safeSeedProfile security shift output := by
  simp only [seedProfile, Rat.cast_sub, projected_cast, safe_cast, BackgroundTranslations.safeSeedProfile]

theorem inverseShift_value (security : ℕ) (shift : ℤ) (output : FirstHistogram.Palette security) :
    inverseShift security shift output.val = ((shiftEquiv security shift).symm output).val := by
  rw [ProposalSymmetry.shiftEquiv_symm_apply]
  have h := (RationalProposalProgram.shift_condition security (-shift) output (shiftEquiv security (-shift) output)).mp rfl
  have hh := congrArg Int.toNat h
  simpa only [inverseShift, colors, PublicParameterProgram.modulus_value, sub_eq_add_neg, Int.toNat_natCast] using hh

theorem convolution_cast (security bits : ℕ) (profile : ℕ → ℚ) (output : FirstHistogram.Palette security) :
    (convolution security bits profile output.val:ℝ) =
      (RationalProposalProgram.approximateSeedLaw security bits).expectation (fun seed =>
        (profile ((shiftEquiv security (actualBlur security seed)).symm output).val:ℝ)) := by
  rw [convolution, RationalProposalProgram.seedEvaluate_cast]
  apply congrArg (FiniteDist.expectation (RationalProposalProgram.approximateSeedLaw security bits))
  funext seed
  rw [inverseShift_value]
  rfl

theorem convolution_error (security bits : ℕ) (profile : ℕ → ℚ) (ideal : FirstHistogram.Palette security → ℝ)
    (hprofile : ∀ output, (profile output.val:ℝ) = ideal output) (bound : ℝ)
    (hbound : ∀ output, |ideal output| ≤ bound) (output : FirstHistogram.Palette security) :
    |(convolution security bits profile output.val:ℝ)-rootConvolutionProfile security ideal output| ≤
      bound*(3/(2:ℝ)^bits) := by
  rw [convolution_cast]
  simp_rw [hprofile]
  exact (CyclePatternProgram.expectation_difference_le_l1 (RationalProposalProgram.approximateSeedLaw security bits)
    (actualSeedLaw security) (fun seed => ideal ((shiftEquiv security (actualBlur security seed)).symm output)) bound
    (fun seed => hbound _)).trans
    (mul_le_mul_of_nonneg_left (RationalProposalProgram.seed_l1 security bits)
      ((abs_nonneg (ideal output)).trans (hbound output)))

theorem convolution_profile_error (security bits : ℕ) (profile : ℕ → ℚ) (ideal : FirstHistogram.Palette security → ℝ)
    (bound profileError : ℝ) (hbound : ∀ output : FirstHistogram.Palette security, |(profile output.val:ℝ)| ≤ bound)
    (hdiff : ∀ output : FirstHistogram.Palette security, |(profile output.val:ℝ)-ideal output| ≤ profileError)
    (output : FirstHistogram.Palette security) :
    |(convolution security bits profile output.val:ℝ)-rootConvolutionProfile security ideal output| ≤
      bound*(3/(2:ℝ)^bits)+profileError := by
  have hfirst := convolution_error security bits profile (fun color => (profile color.val:ℝ))
    (fun _ => rfl) bound hbound output
  have hsecond := CalibrationCoordinateError.expectation_abs_bound (actualSeedLaw security)
    (fun seed => (profile ((shiftEquiv security (actualBlur security seed)).symm output).val:ℝ)-
      ideal ((shiftEquiv security (actualBlur security seed)).symm output)) profileError (fun seed => hdiff _)
  have hs : |rootConvolutionProfile security (fun color => (profile color.val:ℝ)) output-
      rootConvolutionProfile security ideal output| ≤ profileError := by
    simpa only [rootConvolutionProfile, FiniteDist.expectation, mul_sub, Finset.sum_sub_distrib] using hsecond
  exact (abs_sub_le _ (rootConvolutionProfile security (fun color => (profile color.val:ℝ)) output) _).trans
    (add_le_add hfirst hs)

theorem bodyDeviation_error (security bits : ℕ) (output : FirstHistogram.Palette security) :
    |(bodyDeviation security bits output.val:ℝ)-FringeCertificate.bodyDeviation security output| ≤ 3/(2:ℝ)^bits := by
  simp only [bodyDeviation, colors, Rat.cast_sub, one_div, Rat.cast_inv, Rat.cast_natCast,
    PublicParameterProgram.modulus_value, FringeCertificate.bodyDeviation, FringeCertificate.uniformProfile]
  convert RationalProposalProgram.body_error security bits false output using 1
  congr 1
  ring

theorem residual_error (security bits : ℕ) (shift : ℤ) (output : FirstHistogram.Palette security) :
    |(residual security bits shift output.val:ℝ)-BackgroundTranslations.translationResidual security shift output| ≤ 6/(2:ℝ)^bits := by
  have hu (color : FirstHistogram.Palette security) : |BackgroundTranslations.unsafePart security shift color| ≤ 1 := by
    rw [abs_of_nonneg (BackgroundTranslations.unsafePart_nonneg security shift color)]
    exact (BackgroundTranslations.unsafePart_le_shifted security shift color).trans ((shiftedSafeLaw security shift).atom_le_one color)
  have hc := convolution_error security bits (unsafeProfile security shift) (BackgroundTranslations.unsafePart security shift)
    (unsafe_cast security shift) 1 hu output
  have hm := BackgroundTranslations.unsafeMass_le_one security shift
  have hn := BackgroundTranslations.unsafeMass_nonneg security shift
  have hb := RationalProposalProgram.body_error security bits false output
  simp only [residual, Rat.cast_sub, Rat.cast_mul, unsafeTotal_cast, BackgroundTranslations.translationResidual]
  have hsplit : (convolution security bits (unsafeProfile security shift) output.val:ℝ)-
      BackgroundTranslations.unsafeMass security shift*(RationalProposalProgram.body security bits false output.val:ℝ)-
      (rootConvolutionProfile security (BackgroundTranslations.unsafePart security shift) output-
        BackgroundTranslations.unsafeMass security shift*(bodyLaw security false).weight output) =
    ((convolution security bits (unsafeProfile security shift) output.val:ℝ)-rootConvolutionProfile security (BackgroundTranslations.unsafePart security shift) output)-
      BackgroundTranslations.unsafeMass security shift*((RationalProposalProgram.body security bits false output.val:ℝ)-(bodyLaw security false).weight output) := by ring
  rw [hsplit]
  apply (abs_sub _ _).trans
  rw [abs_mul, abs_of_nonneg hn]
  exact (add_le_add hc (mul_le_mul hm hb (abs_nonneg _) (by norm_num))).trans_eq (by ring)

end
end CurrentAFT.RationalBackgroundProfiles
