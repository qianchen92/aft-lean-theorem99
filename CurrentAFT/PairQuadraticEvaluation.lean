import CurrentAFT.DiffusePairEvaluation
import CurrentAFT.MixedPairEvaluation
import CurrentAFT.ActualPairBridge

/-! Exact physical evaluation of both actual branches of the conditional pair. -/

namespace CurrentAFT.PairQuadraticEvaluation

open AFT AFT.SafePair AFT.RepresentedPolynomial ControlCoordinates LeadingEvaluation
  DiffuseProfiles ProposalPrimary ActualControls PrimaryMassFamilies BackgroundFamilies
  BackgroundEvaluation BackgroundFirstEvaluation BackgroundAtomEvaluation MixedPairEvaluation
  DiffusePairEvaluation PairQuadraticFamilies LocalCoefficientFamily MarkedPairLeading
  LocalReferenceEnergy ActualPairBridge FringeCertificate
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw ActualControls.bodyReference
  MarkedPairLeading.bodyConvolution

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

theorem massPolynomial_pairForm (security : ℕ)
    (profile : ActualControls.Palette security → ActualControls.Palette security → ℝ) :
    massPolynomial security 2 (pairWordProfile profile) = pairForm profile := massPolynomial_pair security profile

theorem markedPairCertificate_image (security order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security) :
    evaluation security order (markedPairCertificate security order horder scalar) =
      TruncatedOutput.quotientMap order (pairForm (canonicalPair (uniformProfile security)
        (fun primary output => (primaryLaw security).weight primary * (markedCompanionAt security primary scalar).weight output))) := by
  unfold markedPairCertificate
  change evaluation security order (MarkedPairCertificates.markedMixedCertificate security order horder scalar +
    PrimaryDeviationCertificate.certificate security order (by omega) * freeCertificate security order (by omega)) = _
  rw [map_add, map_mul, markedMixedCertificate_image, primaryDeviation_image, freeCertificate_image,
    massPolynomial_pairForm, massPolynomial_one, ← map_mul, ← map_add]
  rw [← pairForm_tensor, ← pairForm_add]
  congr 2
  exact (marked_pair_canonical_decomposition security scalar).symm

theorem canonicalPair_linear_combination {Color : Type*} [Fintype Color] (reference : Color → ℝ)
    (first second : Color → Color → ℝ) (left right : ℝ) :
    canonicalPair reference (left • first + right • second) =
      left • canonicalPair reference first + right • canonicalPair reference second := by
  funext a b
  simp only [canonicalPair, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  ring

def conditionalPairLaw (security : ℕ) (scalar : Scalar security) : FiniteDist (Pair security) :=
  (primaryLaw security).mix (fun primary => pairAt security primary scalar)

theorem conditionalPairLaw_weight (security : ℕ) (scalar : Scalar security)
    (first second : ActualControls.Palette security) :
    (conditionalPairLaw security scalar).weight (first, second) =
      signedPairAt security scalar (fun _ => 1) first second := by
  simp only [conditionalPairLaw, FiniteDist.mix_weight, signedPairAt, mul_one]

theorem pairQuadraticCertificate_image (security order : ℕ) (horder : 2 ≤ order) (scalar : Scalar security) :
    evaluation security order (pairQuadraticCertificate security order horder scalar) =
      TruncatedOutput.quotientMap order (pairForm (canonicalPair (uniformProfile security)
        (fun first second => (conditionalPairLaw security scalar).weight (first, second)))) := by
  unfold pairQuadraticCertificate
  rw [map_add, map_smul, map_smul, diffuseCertificate_image, markedPairCertificate_image,
    massPolynomial_pairForm, ← map_smul, ← map_smul, ← map_add]
  simp_rw [MvPolynomial.smul_eq_C_mul]
  rw [← pairForm_smul, ← pairForm_smul, ← pairForm_add, ← canonicalPair_linear_combination]
  congr 3
  funext first second
  simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_assoc] using
    ((conditionalPairLaw_weight security scalar first second).trans
      (signedPairAt_actual_decomposition security scalar first second)).symm

end

end CurrentAFT.PairQuadraticEvaluation
