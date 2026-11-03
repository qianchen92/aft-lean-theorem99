import CurrentAFT.PairQuadraticEvaluation
import CurrentAFT.HistogramMean

/-! Literal independent-root, same-scalar leg background generating polynomial. -/

namespace CurrentAFT.LegPolynomialEvaluation

open AFT AFT.RepresentedPolynomial ControlCoordinates GradedControlAlgebra LeadingEvaluation
  DiffuseProfiles ProposalPrimary ActualControls PrimaryMassFamilies BackgroundFamilies
  BackgroundEvaluation BackgroundFirstEvaluation BackgroundAtomEvaluation PairQuadraticEvaluation
  BackgroundCertificates BackgroundTranslations BackgroundLinear LocalCoefficientFamily
  LocalReferenceEnergy FirstHistogram FringeCertificate BodyRootAverages
  ConditionalPairMean LegBackgroundFamilies HistogramMean
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount ProposalPrimary.primaryLaw ActualControls.bodyReference

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

abbrev Scalar (security : ℕ) := LocalReferenceEnergy.Scalar security

def profileEvaluation (security order : ℕ) :=
  (TruncatedOutput.quotientMap (Variable := ActualControls.Palette security) order).toLinearMap.comp
    (profileForm (Color := ActualControls.Palette security))

def attachmentLaw (security : ℕ) (scalar : Scalar security) : FiniteDist (ActualControls.Palette security) :=
  rootAverage security (shiftedSafeLaw security scalar.val)

theorem attachmentLaw_weight (security : ℕ) (scalar : Scalar security) (output : ActualControls.Palette security) :
    (attachmentLaw security scalar).weight output =
      rootConvolutionProfile security (shiftedSafeLaw security scalar.val).weight output := by
  rw [attachmentLaw, rootAverage_seed]
  simp only [FiniteDist.mix_weight, FiniteDist.map_equiv_weight, rootConvolutionProfile]

theorem attachmentLaw_average (security : ℕ) :
    (scalarLaw security).mix (attachmentLaw security) = bodyLaw security true := by
  unfold attachmentLaw
  rw [← rootAverage_mix]
  exact rootAverage_attachment security

def attachmentDeviation (security : ℕ) (scalar : Scalar security) : ActualControls.Palette security → ℝ :=
  (attachmentLaw security scalar).weight - uniformProfile security

theorem attachmentDeviation_average (security : ℕ) :
    (∑ scalar, (scalarLaw security).weight scalar • attachmentDeviation security scalar) =
      (bodyLaw security true).weight - uniformProfile security := by
  funext output
  have h := congrArg (fun law : FiniteDist (ActualControls.Palette security) => law.weight output)
    (attachmentLaw_average security)
  simp only [FiniteDist.mix_weight] at h
  simp only [attachmentDeviation, Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, FiniteDist.sum_one, one_mul]
  rw [h]

theorem meanTranslation_image (security order : ℕ) (horder : 1 ≤ order) :
    evaluation security order (meanTranslation security order horder) =
      TruncatedOutput.quotientMap order (profileForm ((bodyLaw security true).weight - uniformProfile security)) := by
  have hprofile (scalar : Scalar security) :
      rootConvolutionProfile security (shiftedSafeLaw security scalar.val).weight - uniformProfile security =
        attachmentDeviation security scalar := by
    funext output
    simp only [attachmentDeviation, Pi.sub_apply, attachmentLaw_weight]
  unfold meanTranslation
  simp only [map_sum, map_smul, translationCertificate_image]
  change (∑ scalar : Scalar security, (scalarLaw security).weight scalar •
    profileEvaluation security order
      (rootConvolutionProfile security (shiftedSafeLaw security scalar.val).weight - uniformProfile security)) =
    profileEvaluation security order _
  simp_rw [← map_smul]
  rw [← map_sum]
  simp_rw [hprofile]
  rw [attachmentDeviation_average]

theorem legLinearCertificate_image (security order : ℕ) (horder : 1 ≤ order) :
    evaluation security order (legLinearCertificate security order horder) =
      TruncatedOutput.quotientMap order (profileForm
        (fun output => legFirstMean security output - 3 * uniformProfile security output)) := by
  unfold legLinearCertificate
  rw [map_smul, map_add, map_smul, map_smul, freeCertificate_image, meanTranslation_image]
  change -(Parameters.legCount security : ℝ)⁻¹ •
      (freeMass security • profileEvaluation security order _ +
        (Parameters.modulus security : ℝ) • profileEvaluation security order _) =
    profileEvaluation security order _
  rw [← map_smul, ← map_smul, ← map_add, ← map_smul]
  congr 1
  funext output
  have hbaseline := baseline_first_histogram security output
  have hlegs := (BackgroundLinear.legCount_pos security).ne'
  simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
  field_simp [hlegs]
  nlinarith [hbaseline]

theorem conditionalPairLaw_histogram (security : ℕ) (scalar : Scalar security) (output : ActualControls.Palette security) :
    (∑ second, (conditionalPairLaw security scalar).weight (output, second)) +
        (∑ first, (conditionalPairLaw security scalar).weight (first, output)) = pairMean security scalar output := by
  rw [pairMean_actual]
  simp only [conditionalPairLaw, FiniteDist.mix_weight, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> rw [Finset.sum_comm]

theorem conditionalPairLaw_mass (security : ℕ) (scalar : Scalar security) :
    (∑ first, ∑ second, (conditionalPairLaw security scalar).weight (first, second)) = 1 := by
  simpa only [Fintype.sum_prod_type] using (conditionalPairLaw security scalar).sum_one

theorem conditionalPairLinear_profile_image (security order : ℕ) (horder : 1 ≤ order) (scalar : Scalar security) :
    evaluation security order (ConditionalPairLinear.certificate security order horder scalar) =
      TruncatedOutput.quotientMap order (profileForm (centeredMean security scalar)) := by
  rw [conditionalPairLinear_image]
  change TruncatedOutput.quotientMap order (massPolynomial security 1 (oneWordProfile (centeredMean security scalar))) = _
  rw [massPolynomial_one]

theorem conditionalPairGenerating (security order : ℕ) (horder : 2 ≤ order) (scalar : Scalar security) :
    TruncatedOutput.quotientMap order (pairGenerating (uniformProfile security)
      (fun first second => (conditionalPairLaw security scalar).weight (first, second))) =
      1 + evaluation security order (ConditionalPairLinear.certificate security order (by omega) scalar) +
        evaluation security order (PairQuadraticFamilies.pairQuadraticCertificate security order horder scalar) := by
  rw [pairGenerating_canonical, conditionalPairLaw_mass, map_one]
  have hprofile : (fun output =>
      (∑ second, (conditionalPairLaw security scalar).weight (output, second)) +
      (∑ first, (conditionalPairLaw security scalar).weight (first, output)) -
      2 * 1 * uniformProfile security output) = centeredMean security scalar := by
    funext output
    rw [conditionalPairLaw_histogram]
    simp only [centeredMean, mul_one]
  rw [hprofile, map_add, map_add, map_one, conditionalPairLinear_profile_image, pairQuadraticCertificate_image]
  ring

def conditionalLegGenerating (security : ℕ) (scalar : Scalar security) : MvPolynomial (ActualControls.Palette security) ℝ :=
  tripleGenerating (uniformProfile security) (fun first second attached =>
    (conditionalPairLaw security scalar).weight (first, second) * (attachmentLaw security scalar).weight attached)

def legGenerating (security : ℕ) : MvPolynomial (ActualControls.Palette security) ℝ :=
  ∑ scalar, (scalarLaw security).weight scalar • conditionalLegGenerating security scalar

theorem conditionalLegGenerating_factorization (security : ℕ) (scalar : Scalar security) :
    conditionalLegGenerating security scalar =
      pairGenerating (uniformProfile security) (fun first second => (conditionalPairLaw security scalar).weight (first, second)) *
        (1 + profileForm (attachmentDeviation security scalar)) := by
  rw [conditionalLegGenerating, tripleGenerating_tensor,
    singleGenerating_mass_one _ _ (attachmentLaw security scalar).sum_one]
  rfl

theorem translationCertificate_attachment_image (security order : ℕ) (horder : 1 ≤ order) (scalar : Scalar security) :
    evaluation security order (translationCertificate security order horder scalar.val) =
      TruncatedOutput.quotientMap order (profileForm (attachmentDeviation security scalar)) := by
  rw [translationCertificate_image]
  congr 2
  funext output
  simp only [attachmentDeviation, Pi.sub_apply, attachmentLaw_weight]

theorem conditionalLegGenerating_image (security order : ℕ) (horder : 2 ≤ order) (scalar : Scalar security) :
    TruncatedOutput.quotientMap order (conditionalLegGenerating security scalar) =
      1 + evaluation security order
        (ConditionalPairLinear.certificate security order (by omega) scalar +
          translationCertificate security order (by omega) scalar.val) +
        evaluation security order (conditionalQuadratic security order horder scalar) +
        evaluation security order (conditionalCubic security order horder scalar) := by
  rw [conditionalLegGenerating_factorization, map_mul, map_add, map_one,
    conditionalPairGenerating security order horder scalar,
    ← translationCertificate_attachment_image security order (by omega) scalar]
  unfold conditionalQuadratic conditionalCubic
  simp only [map_add, map_mul]
  ring

theorem legLinearProfile_average (security : ℕ) :
    (∑ scalar, (scalarLaw security).weight scalar •
      (centeredMean security scalar + attachmentDeviation security scalar)) =
      fun output => legFirstMean security output - 3 * uniformProfile security output := by
  funext output
  have hatt := congrFun (attachmentDeviation_average security) output
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at hatt
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, mul_add,
    Finset.sum_add_distrib]
  rw [hatt]
  simp only [centeredMean, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    FiniteDist.sum_one, one_mul]
  have hleg := offBodyMean_leg security output
  unfold offBodyMean FiniteDist.expectation at hleg
  nlinarith [hleg]

theorem legLinear_image_average (security order : ℕ) (horder : 1 ≤ order) :
    (∑ scalar, (scalarLaw security).weight scalar • evaluation security order
      (ConditionalPairLinear.certificate security order horder scalar +
        translationCertificate security order horder scalar.val)) =
      evaluation security order (legLinearCertificate security order horder) := by
  simp only [map_add, conditionalPairLinear_profile_image, translationCertificate_attachment_image]
  rw [legLinearCertificate_image]
  change (∑ scalar : Scalar security, (scalarLaw security).weight scalar •
    (profileEvaluation security order (centeredMean security scalar) +
      profileEvaluation security order (attachmentDeviation security scalar))) = profileEvaluation security order _
  simp_rw [← map_add]
  simp_rw [← map_smul]
  rw [← map_sum, legLinearProfile_average]

theorem completeLegAtom_image (security order : ℕ) (horder : 2 ≤ order) :
    evaluation security order (1 + completeLegAtom security order horder) =
      TruncatedOutput.quotientMap order (legGenerating security) := by
  unfold legGenerating
  simp only [map_sum, map_smul, conditionalLegGenerating_image security order horder, smul_add,
    Finset.sum_add_distrib]
  rw [← Finset.sum_smul, FiniteDist.sum_one, one_smul, legLinear_image_average]
  unfold completeLegAtom legQuadratic legCubic
  simp only [map_add, map_one, map_sum, map_smul]
  ring

end

end CurrentAFT.LegPolynomialEvaluation
