import CurrentAFT.ActualBackgroundInverse
import CurrentAFT.LocalCoefficientEvaluation

/-!
# The actual primary and safe-body endpoint forms for background families

Primary forms use the genuine calibrated first response. Body forms use
the actual protected cyclic root convolution of a safe-center Dirac mass.
-/

namespace CurrentAFT.BackgroundEvaluation

open AFT ControlCoordinates LeadingEvaluation DiffuseProfiles ProposalPrimary ActualControls
  PrimaryTensorInverse PrimaryMassFamilies MarkedPairLeading LocalCoefficientFamily LocalCoefficientEvaluation
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw ActualControls.bodyReference

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

def bodyForm (security : ℕ) (center : SafePalette security) : MvPolynomial (ActualControls.Palette security) ℝ :=
  RepresentedPolynomial.profileForm (bodyConvolution security (Pi.single center.val 1))

theorem bodyForm_homogeneous (security : ℕ) (center : SafePalette security) : (bodyForm security center).IsHomogeneous 1 := by
  rw [bodyForm, RepresentedPolynomial.profileForm_apply]
  apply MvPolynomial.IsHomogeneous.sum
  intro output _
  exact (MvPolynomial.isHomogeneous_C _ _).mul (MvPolynomial.isHomogeneous_X ℝ output)

def evaluation (security order : ℕ) :=
  LocalCoefficientEvaluation.evaluation security order (bodyForm security) (bodyForm_homogeneous security)

theorem massCertificateFamily_image (security order degree : ℕ) (hdegree : degree ≤ order)
    (profile : (Fin degree → ActualControls.Palette security) → ℝ)
    (hcentered : MassCentered degree profile)
    (hsymmetric : ∀ (permutation : Equiv.Perm (Fin degree)) word, profile (word ∘ permutation) = profile word) :
    evaluation security order (massCertificateFamily security order degree hdegree profile hcentered hsymmetric) =
      TruncatedOutput.quotientMap order (massPolynomial security degree profile) := by
  unfold massCertificateFamily
  change familyLinear (primaryLaw security) (bodyReference security) (primaryForm security) (bodyForm security) order (Pi.single _ _) = _
  rw [familyLinear_single]
  change TruncatedOutput.quotientMap order (kernelPolynomial (primaryLaw security) (bodyReference security)
    (primaryForm security) (bodyForm security) (fun colors (_ : Fin 0 → SafePalette security) => massLift security degree profile colors)) = _
  rw [primary_kernelPolynomial]
  unfold primaryLeadingPolynomial
  rw [massLift_leading]

theorem primaryDeviation_image (security order : ℕ) (horder : 1 ≤ order) :
    evaluation security order (PrimaryDeviationCertificate.certificate security order horder) =
      TruncatedOutput.quotientMap order (massPolynomial security 1 (oneWordProfile (PrimaryDeviationCertificate.deviation security))) :=
  massCertificateFamily_image security order 1 horder _ _ _

theorem conditionalPairLinear_image (security order : ℕ) (horder : 1 ≤ order) (scalar : ConditionalPairMean.Scalar security) :
    evaluation security order (ConditionalPairLinear.certificate security order horder scalar) =
      TruncatedOutput.quotientMap order (massPolynomial security 1 (ConditionalPairLinear.wordMean security scalar)) :=
  massCertificateFamily_image security order 1 horder _ _ _

theorem diffusePrimary_image (security order : ℕ) (horder : 2 ≤ order) (scalar : ℤ) :
    evaluation security order (DiffusePairCertificates.diffusePrimaryCertificate security order horder scalar) =
      TruncatedOutput.quotientMap order (massPolynomial security 2 (DiffusePairCertificates.residualMass security scalar)) :=
  massCertificateFamily_image security order 2 horder _ _ _

end

end CurrentAFT.BackgroundEvaluation
