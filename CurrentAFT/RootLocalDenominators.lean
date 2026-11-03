import CurrentAFT.RootSelectedZeroTag
import CurrentAFT.RootOrdinaryGroupedChannel
import CurrentAFT.RootUnselectedBlockChannel

/-! # Literal physical denominators of the selected local channels

The primary factor contains an independent compensator and the complete
same-scalar leg. The ordinary factor is the actual root-averaged center
singleton. These equalities identify the physical factors canceled by
the finite reciprocals; no polynomial image is assumed injective.
-/
namespace CurrentAFT.RootLocalDenominators
open AFT AFT.RepresentedPolynomial DiffuseProfiles ProposalPrimary ActualControls FirstHistogram
  LocalReferenceEnergy PairedReferenceEnergy FixedPairedFirst IndependentPairedReference
  PositiveFirstCoefficient ActualBlockFock RootTaggedSelected RootReferenceExpectation
  RootBackgroundPolynomial RootIndependentBackground BodyRootAverages BackgroundPolynomialEvaluation
  BackgroundEndpointLaw CycleRootExpansion ControlCoordinates GradedControlAlgebra GradedControlNorm
  LocalCoefficientFamily LocalRaisingBounds NormalizedLocalPolynomial
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw rootReference
abbrev Palette (security : ℕ) := ActualControls.Palette security

theorem uniformReference_eq (security : ℕ) :
    (uniformReference security).weight = FringeCertificate.uniformProfile security := by
  funext color
  rw [uniformReference_weight]
  simp only [FringeCertificate.uniformProfile, one_div]

theorem generating_eq_block {Slot : Type*} [Fintype Slot] (security : ℕ)
    (law : FiniteDist (Slot → Palette security)) :
    centeredGeneratingLinear (uniformReference security).weight law.weight = blockGenerating security law := by
  simp only [centeredGeneratingLinear, blockGenerating, finiteGenerating, LinearMap.coe_mk, AddHom.coe_mk,
    MvPolynomial.smul_eq_C_mul, uniformReference_eq]

theorem positiveFour_periodic (security : ℕ) (firstComp secondComp firstAttach secondAttach : ℤ)
    (hcomp : (firstComp : Root security) = (secondComp : Root security))
    (hattach : (firstAttach : Root security) = (secondAttach : Root security))
    (scalar : FirstHistogram.Scalar security) :
    positiveFourLaw security firstComp firstAttach scalar = positiveFourLaw security secondComp secondAttach scalar := by
  have hc : compensatorAt security firstComp = compensatorAt security secondComp := by
    unfold compensatorAt
    rw [shiftEquiv_eq_of_cast security firstComp secondComp hcomp]
  have ha : attachmentAt security firstAttach scalar = attachmentAt security secondAttach scalar := by
    unfold attachmentAt
    rw [shiftEquiv_eq_of_cast security (firstAttach + scalar.val) (secondAttach + scalar.val)
      (by simp only [Int.cast_add, hattach])]
  simp only [positiveFourLaw, hc, positiveTripleLaw, ha]

theorem independentPositive_root_mixture (security : ℕ) (word : Fin 4 → Palette security) :
    (sourceLaw security).expectation (fun sample =>
      (positiveFourLaw security (sample.1.1.val : ℤ) (sample.1.2.val : ℤ) sample.2).weight word) =
      (independentPositiveLaw security).weight word := by
  rw [IndependentReferenceEnergy.independentPositive_mixture]
  unfold sourceLaw rootsLaw IndependentReferenceEnergy.rootLaw
  rw [FiniteDist.expectation_prod, FiniteDist.expectation_comm, FiniteDist.expectation_prod]
  apply congrArg (scalarLaw security).expectation
  funext scalar
  rw [FiniteDist.expectation_prod]
  calc
    _ = (actualSeedLaw security).expectation (fun comp =>
        (rootReference security).expectation (fun attach =>
          (positiveFourLaw security (actualBlur security comp) (attach.val : ℤ) scalar).weight word)) := by
      apply rootReference_seed_expectation security (fun comp : ℤ =>
        (rootReference security).expectation (fun attach =>
          (positiveFourLaw security comp (attach.val : ℤ) scalar).weight word))
      intro first second hequal
      apply congrArg (rootReference security).expectation
      funext attach
      rw [positiveFour_periodic security first second (attach.val : ℤ) (attach.val : ℤ) hequal rfl scalar]
    _ = _ := by
      rw [FiniteDist.expectation_prod]
      apply congrArg (actualSeedLaw security).expectation
      funext comp
      apply rootReference_seed_expectation security (fun attach : ℤ =>
        (positiveFourLaw security (actualBlur security comp) attach scalar).weight word)
      intro first second hequal
      rw [positiveFour_periodic security (actualBlur security comp) (actualBlur security comp)
        first second rfl hequal scalar]

theorem finiteGenerating_cons {Color : Type*} [Fintype Color] (reference : Color → ℝ)
    (first : FiniteDist Color) (tail : FiniteDist (Fin 3 → Color)) :
    finiteGenerating ((first.prod tail).map (fun draw => Fin.cons draw.1 draw.2))
      (fun word : Fin 4 → Color => ∏ index, centeredFactor reference (word index)) =
      singleGenerating reference first.weight * finiteGenerating tail (fun word => ∏ index, centeredFactor reference (word index)) := by
  rw [finiteGenerating_map]
  simp only [Function.comp_def, Fin.prod_univ_succ]
  exact finiteGenerating_prod first tail (centeredFactor reference)
    (fun word => ∏ index : Fin 3, centeredFactor reference (word index))

theorem positiveFour_generating (security : ℕ) (comp attach : ℤ) (scalar : FirstHistogram.Scalar security) :
    blockGenerating security (positiveFourLaw security comp attach scalar) =
      singleGenerating (FringeCertificate.uniformProfile security) (compensatorAt security comp).weight *
        blockGenerating security (positiveTripleLaw security attach scalar) :=
  finiteGenerating_cons (FringeCertificate.uniformProfile security) (compensatorAt security comp)
    (positiveTripleLaw security attach scalar)

theorem compensator_root_mix (security : ℕ) :
    (rootReference security).mix (fun root => compensatorAt security (root.val : ℤ)) =
      BackgroundCertificates.convolvedCenterLaw security := by
  unfold compensatorAt
  rw [rootReference_shift_mix, rootAverage_free]

def ordinaryPolynomial (security : ℕ) : MvPolynomial (Palette security) ℝ :=
  singleGenerating (FringeCertificate.uniformProfile security) (BackgroundCertificates.convolvedCenterLaw security).weight

def primaryPolynomial (security : ℕ) : MvPolynomial (Palette security) ℝ :=
  ordinaryPolynomial security * LegPolynomialEvaluation.legGenerating security

theorem independentPositive_generating (security : ℕ) :
    centeredGeneratingLinear (uniformReference security).weight (independentPositiveLaw security).weight =
      primaryPolynomial security := by
  have hmass : (independentPositiveLaw security).weight =
      ∑ sample : RootTaggedSelected.Sample security, (sourceLaw security).weight sample •
        (positiveFourLaw security (sample.1.1.val : ℤ) (sample.1.2.val : ℤ) sample.2).weight := by
    funext word
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using (independentPositive_root_mixture security word).symm
  rw [hmass, map_sum]
  simp only [map_smul, generating_eq_block, positiveFour_generating]
  have hleg := primary_root_average security
  simp only [primaryLawAt, blockGenerating_mix] at hleg
  rw [show primaryPolynomial security =
    (∑ comp : Root security, (rootReference security).weight comp •
      singleGenerating (FringeCertificate.uniformProfile security) (compensatorAt security (comp.val : ℤ)).weight) *
    (∑ attach : Root security, (rootReference security).weight attach •
      ∑ scalar, (scalarLaw security).weight scalar • blockGenerating security (positiveTripleLaw security (attach.val : ℤ) scalar)) from by
    rw [hleg, ← singleGenerating_mix, compensator_root_mix]
    rfl]
  simp only [sourceLaw, rootsLaw, Fintype.sum_prod_type, FiniteDist.prod_weight]
  symm
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro comp _
  apply Finset.sum_congr rfl
  intro attach _
  apply Finset.sum_congr rfl
  intro scalar _
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1
  ring

theorem primary_positive_image (security order : ℕ) :
    BackgroundEvaluation.evaluation security order
      (NormalizedLocalPolynomial.positiveFamily security order (independentPositiveLaw security)) =
      TruncatedOutput.quotientMap order (primaryPolynomial security) := by
  rw [NormalizedLocalPolynomial.positiveFamily]
  change LocalCoefficientEvaluation.evaluation security order (BackgroundEvaluation.bodyForm security)
    (BackgroundEvaluation.bodyForm_homogeneous security) (completeFamily security order (independentPositiveLaw security).weight) = _
  rw [NormalizedLocalPolynomial.completeFamily_image, independentPositive_generating]

theorem primary_reciprocal_physical (security order : ℕ) :
    BackgroundEvaluation.evaluation security order (LocalRaisingBounds.positiveInverse security order) *
      TruncatedOutput.quotientMap order (primaryPolynomial security) = 1 := by
  rw [← primary_positive_image, ← map_mul]
  rw [LocalRaisingBounds.positiveInverse, GradedInverse.backgroundInverse_mul _ _ order _
    (positiveFamily_zeroArity security order (independentPositiveLaw security)), map_one]

theorem ordinaryPolynomial_eq (security : ℕ) : ordinaryPolynomial security =
    1 + profileForm (OrdinaryRaising.deviation security) := by
  rw [ordinaryPolynomial, singleGenerating_mass_one _ _ (BackgroundCertificates.convolvedCenterLaw security).sum_one]
  rfl

theorem ordinary_positive_image (security order : ℕ) (horder : 1 ≤ order) :
    BackgroundEvaluation.evaluation security order (OrdinaryRaising.positiveFamily security order horder) =
      TruncatedOutput.quotientMap order (ordinaryPolynomial security) := by
  rw [ordinaryPolynomial_eq, map_add, map_one]
  exact OrdinaryRaising.positiveFamily_image security order horder

theorem meanLaw_free (security : ℕ) (queue : ℤ) :
    RootTaggedLocal.meanLaw security .free queue = BackgroundCertificates.convolvedCenterLaw security := by
  unfold RootTaggedLocal.meanLaw RootTaggedLocal.shiftedLaw UniformBodyProfiles.preRootLaw
  rw [rootReference_shift_mix, rootAverage_free]

theorem ordinary_eq_unselected_center (security : ℕ) (queue : ℤ) (index : Fin (centerCount security)) :
    ordinaryPolynomial security = RootUnselectedBlockChannel.positivePolynomial security queue (.inr (.inl index)) := by
  rw [RootUnselectedBlockChannel.positivePolynomial, meanLaw_free, uniformReference_eq]
  rfl

end
end CurrentAFT.RootLocalDenominators
