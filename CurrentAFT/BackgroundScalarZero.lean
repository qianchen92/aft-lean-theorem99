import CurrentAFT.LegBackgroundFamilies
import CurrentAFT.GradedInverse

/-! The complete concrete background atoms have exactly zero scalar coefficient. -/

namespace CurrentAFT.BackgroundScalarZero

open AFT ControlCoordinates GradedControlAlgebra GradedInverse DiffuseProfiles ProposalPrimary ActualControls
  BackgroundFamilies BackgroundLinear PairCertificateFamilies PrimaryMassFamilies
  DiffusePairCertificates MarkedPairCertificates PairQuadraticFamilies LegBackgroundFamilies
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw ActualControls.bodyReference

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]

theorem positive_single_zero (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (arity : TruncatedArity order) (hpositive : 0 < arity.val.1.val + arity.val.2.val)
    (kernel : canonicalKernels primary body arity.val.1.val arity.val.2.val) :
    (Pi.single arity kernel : KernelFamily primary body order) (zeroArity order) = 0 := by
  apply Pi.single_eq_of_ne
  intro hequal
  have hdegree := congrArg (fun arity : TruncatedArity order => arity.val.1.val + arity.val.2.val) hequal
  have hzero : (zeroArity order).val.1.val + (zeroArity order).val.2.val = 0 := by simp [zeroArity]
  dsimp only at hdegree
  omega

theorem product_zero (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (first second : KernelFamily primary body order) (hfirst : first (zeroArity order) = 0) :
    (first * second) (zeroArity order) = 0 := by
  have h := vanishesBelow_mul primary body order 1 0 first second
    (vanishesBelow_one_of_zero primary body order first hfirst) (vanishesBelow_zero primary body order second)
  exact h (zeroArity order) (by simp [zeroArity])

theorem primaryFamily_zero (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ) (horder : 1 ≤ order)
    (density : Primary → ℝ) (hcenter : ∑ color, primary.weight color * density color = 0) :
    primaryFamily primary body order horder density hcenter (zeroArity order) = 0 := by
  unfold primaryFamily
  apply positive_single_zero
  simp [BackgroundFamilies.primaryArity]

theorem bodyFamily_zero (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ) (horder : 1 ≤ order)
    (density : Body → ℝ) (hcenter : ∑ color, body.weight color * density color = 0) :
    bodyFamily primary body order horder density hcenter (zeroArity order) = 0 := by
  unfold bodyFamily
  apply positive_single_zero
  simp [bodyArity]

theorem freeCertificate_zero (security order : ℕ) (horder : 1 ≤ order) :
    freeCertificate security order horder (zeroArity order) = 0 := by
  simp only [freeCertificate, Pi.add_apply, primaryFamily_zero, bodyFamily_zero, add_zero]

theorem translationCertificate_zero (security order : ℕ) (horder : 1 ≤ order) (shift : ℤ) :
    translationCertificate security order horder shift (zeroArity order) = 0 := by
  simp only [translationCertificate, Pi.add_apply, primaryFamily_zero, bodyFamily_zero, add_zero]

theorem meanTranslation_zero (security order : ℕ) (horder : 1 ≤ order) :
    meanTranslation security order horder (zeroArity order) = 0 := by
  simp only [meanTranslation, Finset.sum_apply, Pi.smul_apply, translationCertificate_zero, smul_zero, Finset.sum_const_zero]

theorem legLinearCertificate_zero (security order : ℕ) (horder : 1 ≤ order) :
    legLinearCertificate security order horder (zeroArity order) = 0 := by
  simp only [legLinearCertificate, Pi.smul_apply, Pi.add_apply, freeCertificate_zero, meanTranslation_zero, smul_zero, add_zero]

theorem massCertificateFamily_zero (security order degree : ℕ) (hdegree : degree ≤ order) (hpositive : 0 < degree)
    (profile : (Fin degree → ActualControls.Palette security) → ℝ)
    (hcentered : PrimaryTensorInverse.MassCentered degree profile)
    (hsymmetric : ∀ (permutation : Equiv.Perm (Fin degree)) word, profile (word ∘ permutation) = profile word) :
    massCertificateFamily security order degree hdegree profile hcentered hsymmetric (zeroArity order) = 0 := by
  unfold massCertificateFamily
  apply positive_single_zero
  simpa [PrimaryMassFamilies.primaryArity] using hpositive

theorem diffuseBodyCertificate_zero (security order : ℕ) (horder : 2 ≤ order) (scalar : ℤ) :
    diffuseBodyCertificate security order horder scalar (zeroArity order) = 0 := by
  unfold diffuseBodyCertificate
  apply positive_single_zero
  simp [bodyPairArity]

theorem diffusePrimaryCertificate_zero (security order : ℕ) (horder : 2 ≤ order) (scalar : ℤ) :
    diffusePrimaryCertificate security order horder scalar (zeroArity order) = 0 := by
  unfold diffusePrimaryCertificate
  exact massCertificateFamily_zero _ _ _ _ (by omega) _ _ _

theorem diffuseCertificate_zero (security order : ℕ) (horder : 2 ≤ order) (scalar : ℤ) :
    diffuseCertificate security order horder scalar (zeroArity order) = 0 := by
  simp only [diffuseCertificate, Pi.add_apply, diffuseBodyCertificate_zero, diffusePrimaryCertificate_zero, add_zero]

theorem markedMixedCertificate_zero (security order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security) :
    markedMixedCertificate security order horder scalar (zeroArity order) = 0 := by
  unfold markedMixedCertificate
  apply positive_single_zero
  simp [mixedArity]

theorem primaryDeviationCertificate_zero (security order : ℕ) (horder : 1 ≤ order) :
    PrimaryDeviationCertificate.certificate security order horder (zeroArity order) = 0 := by
  unfold PrimaryDeviationCertificate.certificate
  exact massCertificateFamily_zero _ _ _ _ (by omega) _ _ _

theorem markedPairCertificate_zero (security order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security) :
    markedPairCertificate security order horder scalar (zeroArity order) = 0 := by
  change markedMixedCertificate security order horder scalar (zeroArity order) +
    (PrimaryDeviationCertificate.certificate security order (by omega) * freeCertificate security order (by omega)) (zeroArity order) = 0
  rw [markedMixedCertificate_zero, product_zero _ _ _ _ _ (primaryDeviationCertificate_zero security order (by omega)), add_zero]

theorem pairQuadraticCertificate_zero (security order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security) :
    pairQuadraticCertificate security order horder scalar (zeroArity order) = 0 := by
  simp only [pairQuadraticCertificate, Pi.add_apply, Pi.smul_apply, diffuseCertificate_zero,
    markedPairCertificate_zero, smul_zero, add_zero]

theorem conditionalPairLinear_zero (security order : ℕ) (horder : 1 ≤ order) (scalar : MarkedPairSeed.Scalar security) :
    ConditionalPairLinear.certificate security order horder scalar (zeroArity order) = 0 := by
  unfold ConditionalPairLinear.certificate
  exact massCertificateFamily_zero _ _ _ _ (by omega) _ _ _

theorem conditionalQuadratic_zero (security order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security) :
    conditionalQuadratic security order horder scalar (zeroArity order) = 0 := by
  change pairQuadraticCertificate security order horder scalar (zeroArity order) +
    (ConditionalPairLinear.certificate security order (by omega) scalar *
      translationCertificate security order (by omega) scalar.val) (zeroArity order) = 0
  rw [pairQuadraticCertificate_zero, product_zero _ _ _ _ _ (conditionalPairLinear_zero security order (by omega) scalar), add_zero]

theorem conditionalCubic_zero (security order : ℕ) (horder : 2 ≤ order) (scalar : MarkedPairSeed.Scalar security) :
    conditionalCubic security order horder scalar (zeroArity order) = 0 := by
  exact product_zero _ _ _ _ _ (pairQuadraticCertificate_zero security order horder scalar)

theorem legQuadratic_zero (security order : ℕ) (horder : 2 ≤ order) :
    legQuadratic security order horder (zeroArity order) = 0 := by
  simp only [legQuadratic, Finset.sum_apply, Pi.smul_apply, conditionalQuadratic_zero, smul_zero, Finset.sum_const_zero]

theorem legCubic_zero (security order : ℕ) (horder : 2 ≤ order) :
    legCubic security order horder (zeroArity order) = 0 := by
  simp only [legCubic, Finset.sum_apply, Pi.smul_apply, conditionalCubic_zero, smul_zero, Finset.sum_const_zero]

theorem completeLegAtom_zero (security order : ℕ) (horder : 2 ≤ order) :
    completeLegAtom security order horder (zeroArity order) = 0 := by
  simp only [completeLegAtom, Pi.add_apply, legLinearCertificate_zero, legQuadratic_zero, legCubic_zero, add_zero]

end

end CurrentAFT.BackgroundScalarZero
