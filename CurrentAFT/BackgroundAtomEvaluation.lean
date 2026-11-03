import CurrentAFT.BodyChannelEvaluation

/-! Exact evaluation of the actual free and translated background atoms. -/

namespace CurrentAFT.BackgroundAtomEvaluation

open AFT ControlCoordinates DiffuseProfiles ProposalPrimary ActualControls
  BackgroundFamilies BackgroundEvaluation BackgroundFirstEvaluation BodyChannelEvaluation
  BackgroundCertificates BackgroundTranslations FringeCertificate
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw ActualControls.bodyReference

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

theorem freeCertificate_image (security order : ℕ) (horder : 1 ≤ order) :
    evaluation security order (freeCertificate security order horder) =
      TruncatedOutput.quotientMap order (RepresentedPolynomial.profileForm
        ((convolvedCenterLaw security).weight - uniformProfile security)) := by
  unfold freeCertificate
  rw [map_add, primaryFamily_image, bodyFamily_image, safeMass_full, bodyConvolution_density]
  rw [← map_add, ← map_add, free_background_certificate_leading]

theorem translationCertificate_image (security order : ℕ) (horder : 1 ≤ order) (shift : ℤ) :
    evaluation security order (translationCertificate security order horder shift) =
      TruncatedOutput.quotientMap order (RepresentedPolynomial.profileForm
        (rootConvolutionProfile security (shiftedSafeLaw security shift).weight - uniformProfile security)) := by
  unfold translationCertificate
  rw [map_add, map_add, primaryFamily_image, primaryFamily_image, bodyFamily_image,
    safeMass_full, bodyConvolution_density]
  rw [← map_add, ← map_add, ← map_add, ← map_add]
  congr 2
  rw [add_right_comm, translation_certificate_leading]

end

end CurrentAFT.BackgroundAtomEvaluation
