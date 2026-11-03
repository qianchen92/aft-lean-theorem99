import CurrentAFT.RationalRootProfileProgram
import CurrentAFT.DiffusePairEvaluation
import AFT.PairCoreProgram
import AFT.RationalCanonicalPairProgram

/-! # Computed diffuse-pair safe seed and its actual quadratic residual -/
namespace CurrentAFT.RationalDiffuseResidualProgram
open AFT GaussianSource RationalNumerics DiffuseProfiles ProposalPrimary ActualControls
  DiffusePair DiffusePairBounds DiffusePairResidual DiffusePairResidualRates
open scoped BigOperators
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def evaluate (security colors width cutoff bits : ℕ) (scalar : ℤ) (first second : ℕ) : ℚ :=
  ∑ sign : Bool, ∑ left : Window cutoff, ∑ right : Window cutoff,
    (1 / 2 : ℚ) * RationalProposalProgram.gaussianWeight security cutoff bits left *
      RationalProposalProgram.gaussianWeight security cutoff bits right *
      AFT.V7Calibration.averagedPairProgram colors 1
        ((if sign then (width : ℤ) else -2 * (width : ℤ) + 1) + (left.val - right.val)) scalar width first second

def pair (security bits : ℕ) (scalar : ℤ) (first second : ℕ) : ℚ :=
  evaluate security (PublicParameterProgram.modulus security).count ((security + 2)^48)
    (((security + 2)^2 - 1) / 2) bits scalar first second

def core (security : ℕ) : Finset (Fin (PublicParameterProgram.modulus security).count) :=
  Finset.univ.filter (fun color => RationalBackgroundProfiles.Safe security color.val)

def seed (security bits : ℕ) (scalar : ℤ) (first second : ℕ) : ℚ :=
  rationalCanonicalPairProgram (PublicParameterProgram.modulus security).count
    (RationalBackgroundProfiles.safe security)
    (fun first second => if RationalBackgroundProfiles.Safe security first ∧ RationalBackgroundProfiles.Safe security second then
      pair security bits scalar first second else 0) first second

def uniformCanonical (security bits : ℕ) (scalar : ℤ) (first second : ℕ) : ℚ :=
  rationalCanonicalPairProgram (PublicParameterProgram.modulus security).count
    (fun _ => 1 / (PublicParameterProgram.modulus security).count) (pair security bits scalar) first second

def smoothedSeed (security bits : ℕ) (scalar : ℤ) (first second : ℕ) : ℚ :=
  RationalBackgroundProfiles.convolution security bits
    (fun left => RationalBackgroundProfiles.convolution security bits (seed security bits scalar left) second) first

def residual (security bits : ℕ) (scalar : ℤ) (first second : ℕ) : ℚ :=
  uniformCanonical security bits scalar first second - smoothedSeed security bits scalar first second

def bodyDensity (security bits : ℕ) (scalar : ℤ) (first second : ℕ) : ℚ :=
  seed security bits scalar first second /
    (RationalProposalProgram.center security bits first * RationalProposalProgram.center security bits second)

noncomputable section
open scoped Classical
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff Parameters.safeMargin
  PublicParameterProgram.modulus primaryLaw centerLaw
attribute [local irreducible] pair seed smoothedSeed

def approximatePairSeed (security bits : ℕ) : FiniteDist (PairSeed security) :=
  (FiniteDist.uniform Bool).prod
    ((windowApproxLaw (WindowGaussianSampler.squaredWidth security) (edgeCutoff security) bits).prod
      (windowApproxLaw (WindowGaussianSampler.squaredWidth security) (edgeCutoff security) bits))

def pairTest (security : ℕ) (scalar : ℤ) (first second : Palette security) (sample : PairSeed security) : ℝ :=
  AFT.TrimmedSlice.averagedPair (Parameters.modulus security) 1 (pairStart security sample) scalar
    (Parameters.anchorWidth security) first second

theorem evaluate_cast (security colors width cutoff bits : ℕ) (scalar : ℤ) (first second : Fin colors) :
    (evaluate security colors width cutoff bits scalar first.val second.val : ℝ) =
      ((FiniteDist.uniform Bool).prod
        ((windowApproxLaw (WindowGaussianSampler.squaredWidth security) cutoff bits).prod
          (windowApproxLaw (WindowGaussianSampler.squaredWidth security) cutoff bits))).expectation
        (fun sample => AFT.TrimmedSlice.averagedPair colors 1
          ((if sample.1 then (width : ℤ) else -2 * (width : ℤ) + 1) + (sample.2.1.val - sample.2.2.val))
          scalar width first second) := by
  simp only [evaluate, Rat.cast_sum, Rat.cast_mul, Rat.cast_inv, Rat.cast_ofNat,
    RationalProposalProgram.gaussianWeight_eq, AFT.V7Calibration.averagedPairProgram_cast,
    FiniteDist.expectation, FiniteDist.prod_weight, Fintype.sum_prod_type, FiniteDist.uniform_weight,
    Fintype.card_bool, Nat.cast_ofNat, windowApproxLaw, one_div, mul_assoc]

theorem pair_cast (security bits : ℕ) (scalar : ℤ) (first second : Palette security) :
    (pair security bits scalar first.val second.val : ℝ) =
      (approximatePairSeed security bits).expectation (pairTest security scalar first second) := by
  unfold pair
  have hcut : ((security + 2)^2 - 1) / 2 = edgeCutoff security := by
    simp only [edgeCutoff, Parameters.sourceCutoff, Parameters.base]
  rw [hcut, PublicParameterProgram.modulus_value]
  have hw : (security + 2)^48 = Parameters.anchorWidth security := by
    simp only [Parameters.anchorWidth, Parameters.scale, Parameters.base, ← pow_mul]
  rw [hw, evaluate_cast]
  rfl

theorem pairTest_bound (security : ℕ) (scalar : ℤ) (first second : Palette security) (sample : PairSeed security) :
    |pairTest security scalar first second sample| ≤ 1 := by
  rw [pairTest, ← AFT.V7Calibration.averagedPairProgram_cast]
  exact AFT.V7Calibration.averagedPairProgram_abs_le_one _ _ _ _ _ _ _

theorem pair_bound (security bits : ℕ) (scalar : ℤ) (first second : Palette security) :
    |(pair security bits scalar first.val second.val : ℝ)| ≤ 1 := by
  rw [pair_cast]
  exact CalibrationCoordinateError.expectation_abs_bound _ _ 1 (pairTest_bound security scalar first second)

theorem pair_error (security bits : ℕ) (scalar : ℤ) (first second : Palette security) :
    |(pair security bits scalar first.val second.val : ℝ) - pairProfile security scalar first second| ≤ 2 / (2 : ℝ)^bits := by
  have hsingle : (∑ point, |(windowApproxLaw (WindowGaussianSampler.squaredWidth security) (edgeCutoff security) bits).weight point -
      (edgeLaw security).weight point|) ≤ 1 / (2 : ℝ)^bits :=
    windowApproxLaw_l1 _ _ _ _ (WindowGaussianSampler.squaredWidth_positive security)
      (WindowGaussianSampler.squaredWidth_real security).symm
  have hpair := FiniteDist.l1_prod_le
    (windowApproxLaw (WindowGaussianSampler.squaredWidth security) (edgeCutoff security) bits) (edgeLaw security)
    (windowApproxLaw (WindowGaussianSampler.squaredWidth security) (edgeCutoff security) bits) (edgeLaw security)
  have hprod := FiniteDist.l1_prod_le (FiniteDist.uniform Bool) (FiniteDist.uniform Bool)
    ((windowApproxLaw (WindowGaussianSampler.squaredWidth security) (edgeCutoff security) bits).prod
      (windowApproxLaw (WindowGaussianSampler.squaredWidth security) (edgeCutoff security) bits))
    ((edgeLaw security).prod (edgeLaw security))
  have hl1 : (∑ sample, |(approximatePairSeed security bits).weight sample - (pairSeedLaw security).weight sample|) ≤
      2 / (2 : ℝ)^bits := by
    unfold pairSeedLaw
    rw [ProposalSymmetry.directionLaw_eq_uniform]
    change (∑ sample, |((FiniteDist.uniform Bool).prod _).weight sample - ((FiniteDist.uniform Bool).prod _).weight sample|) ≤ _
    simp only [sub_self, abs_zero, Finset.sum_const_zero, zero_add] at hprod
    exact hprod.trans ((hpair.trans (add_le_add hsingle hsingle)).trans_eq (by ring))
  rw [pair_cast]
  change |(approximatePairSeed security bits).expectation (pairTest security scalar first second) -
    (pairSeedLaw security).expectation (pairTest security scalar first second)| ≤ _
  exact (CyclePatternProgram.expectation_difference_le_l1 _ _ _ 1
    (pairTest_bound security scalar first second)).trans (by simpa only [one_mul] using hl1)

theorem seed_cast (security bits : ℕ) (scalar : ℤ) (first second : Palette security) :
    (seed security bits scalar first.val second.val : ℝ) =
      SafePair.coreSeed (safeCore security)
        (fun first second : Palette security => (pair security bits scalar first.val second.val : ℝ)) first second := by
  rw [seed, PublicParameterProgram.modulus_value, rationalCanonicalPairProgram_fin, rationalCanonicalPair_cast]
  have href (color : Palette security) : (RationalBackgroundProfiles.safe security color.val : ℝ) =
      uniformFiniteProfile (safeCore security) color := by
    rw [RationalBackgroundProfiles.safe_cast]
    simp only [uniformFiniteProfile, safeCore_mem, safeCore_card, safeLaw_weight, safeHeight, one_div]
  simp only [href]
  unfold SafePair.coreSeed
  congr 1
  funext left right
  simp only [apply_ite, Rat.cast_zero, RationalBackgroundProfiles.safe_iff, SafePair.restrictPair, safeCore_mem]
  split_ifs <;> rfl

def pairBound (security : ℕ) : ℝ := ((Parameters.modulus security : ℝ) + 1)^2

theorem seed_bound (security bits : ℕ) (scalar : ℤ) (first second : Palette security) :
    |(seed security bits scalar first.val second.val : ℝ)| ≤ pairBound security := by
  rw [seed_cast]
  unfold SafePair.coreSeed
  have hm (left right : Palette security) :
      |SafePair.restrictPair (safeCore security) (fun first second => (pair security bits scalar first.val second.val : ℝ)) left right| ≤ 1 := by
    unfold SafePair.restrictPair
    split_ifs
    · exact pair_bound security bits scalar left right
    · norm_num
  simpa only [Fintype.card_fin, mul_one, pairBound] using
    canonicalPair_bound (uniformFiniteProfile (safeCore security)) _ 1 (by norm_num)
      (uniformFiniteProfile_abs_le_one _) hm first second

theorem seed_error (security bits : ℕ) (scalar : ℤ) (first second : Palette security) :
    |(seed security bits scalar first.val second.val : ℝ) - safePairProfile security scalar first second| ≤
      2 * pairBound security * (1 / (2 : ℝ)^bits) := by
  rw [seed_cast]
  have hdiff : SafePair.coreSeed (safeCore security)
      (fun first second : Palette security => (pair security bits scalar first.val second.val : ℝ)) first second -
        safePairProfile security scalar first second =
      SafePair.canonicalPair (uniformFiniteProfile (safeCore security))
        (fun first second => SafePair.restrictPair (safeCore security)
          (fun first second => (pair security bits scalar first.val second.val : ℝ)) first second -
          SafePair.restrictPair (safeCore security) (pairProfile security scalar) first second) first second := by
    rw [canonicalPair_sub]
    rfl
  rw [hdiff]
  have h := canonicalPair_bound (uniformFiniteProfile (safeCore security))
    (fun first second => SafePair.restrictPair (safeCore security)
      (fun first second => (pair security bits scalar first.val second.val : ℝ)) first second -
      SafePair.restrictPair (safeCore security) (pairProfile security scalar) first second)
    (2 / (2 : ℝ)^bits) (by positivity)
    (uniformFiniteProfile_abs_le_one _)
    (fun first second => by
      dsimp only
      simp only [SafePair.restrictPair]
      split_ifs
      · exact pair_error security bits scalar first second
      · simp only [sub_self, abs_zero]; positivity) first second
  exact h.trans_eq (by simp only [Fintype.card_fin, pairBound]; ring)

theorem uniformCanonical_cast (security bits : ℕ) (scalar : ℤ) (first second : Palette security) :
    (uniformCanonical security bits scalar first.val second.val : ℝ) =
      SafePair.canonicalPair (fun _ => 1 / (Parameters.modulus security : ℝ))
        (fun first second : Palette security => (pair security bits scalar first.val second.val : ℝ)) first second := by
  unfold uniformCanonical
  rw [PublicParameterProgram.modulus_value, rationalCanonicalPairProgram_fin, rationalCanonicalPair_cast]
  simp only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast]

theorem uniformCanonical_error (security bits : ℕ) (scalar : ℤ) (first second : Palette security) :
    |(uniformCanonical security bits scalar first.val second.val : ℝ) -
      SafePair.canonicalPair (fun _ => 1 / (Parameters.modulus security : ℝ)) (pairProfile security scalar) first second| ≤
      2 * pairBound security * (1 / (2 : ℝ)^bits) := by
  rw [uniformCanonical_cast, ← canonicalPair_sub]
  have hq : 1 ≤ (Parameters.modulus security : ℝ) := by exact_mod_cast (Parameters.modulus_spec security).2.pos
  have href (color : Palette security) : |(1 : ℝ) / Parameters.modulus security| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hq
  exact (canonicalPair_bound _ _ (2 / (2 : ℝ)^bits) (by positivity) href
    (pair_error security bits scalar) first second).trans_eq (by simp only [Fintype.card_fin, pairBound]; ring)

theorem smoothedSeed_cast (security bits : ℕ) (scalar : ℤ) (first second : Palette security) :
    (smoothedSeed security bits scalar first.val second.val : ℝ) =
      (RationalProposalProgram.approximateSeedLaw security bits).expectation (fun left =>
        (RationalProposalProgram.approximateSeedLaw security bits).expectation (fun right =>
          (seed security bits scalar
            (((shiftEquiv security (actualBlur security left)).symm first).val)
            (((shiftEquiv security (actualBlur security right)).symm second).val) : ℝ))) := by
  rw [smoothedSeed, RationalBackgroundProfiles.convolution_cast]
  apply congrArg (FiniteDist.expectation _)
  funext left
  exact RationalBackgroundProfiles.convolution_cast security bits _ second

theorem smoothedSeed_bound (security bits : ℕ) (scalar : ℤ) (first second : Palette security) :
    |(smoothedSeed security bits scalar first.val second.val : ℝ)| ≤ pairBound security := by
  rw [smoothedSeed_cast]
  exact CalibrationCoordinateError.expectation_abs_bound _ _ _ (fun left =>
    CalibrationCoordinateError.expectation_abs_bound _ _ _ (fun right => seed_bound security bits scalar _ _))

theorem smoothedSeed_error (security bits : ℕ) (scalar : ℤ) (first second : Palette security) :
    |(smoothedSeed security bits scalar first.val second.val : ℝ) -
      MarkedPairLeading.bodyConvolution security (fun left =>
        MarkedPairLeading.bodyConvolution security (safePairProfile security scalar left) second) first| ≤
      8 * pairBound security * (1 / (2 : ℝ)^bits) := by
  let B := pairBound security
  have hB : 0 ≤ B := by unfold B pairBound; positivity
  have hinner (left : Palette security) :
      |(RationalBackgroundProfiles.convolution security bits (seed security bits scalar left.val) second.val : ℝ) -
        BackgroundCertificates.rootConvolutionProfile security (safePairProfile security scalar left) second| ≤
        5 * B * (1 / (2 : ℝ)^bits) := by
    exact (RationalBackgroundProfiles.convolution_profile_error security bits (seed security bits scalar left.val)
      (safePairProfile security scalar left) B (2 * B * (1 / (2 : ℝ)^bits))
      (seed_bound security bits scalar left) (seed_error security bits scalar left) second).trans_eq (by ring)
  have hbound (left : Palette security) :
      |(RationalBackgroundProfiles.convolution security bits (seed security bits scalar left.val) second.val : ℝ)| ≤ B := by
    rw [RationalBackgroundProfiles.convolution_cast]
    exact CalibrationCoordinateError.expectation_abs_bound _ _ B (fun seed => seed_bound security bits scalar left _)
  unfold smoothedSeed
  change |(RationalBackgroundProfiles.convolution security bits
    (fun left => RationalBackgroundProfiles.convolution security bits (seed security bits scalar left) second.val) first.val : ℝ) -
      BackgroundCertificates.rootConvolutionProfile security (fun left =>
        BackgroundCertificates.rootConvolutionProfile security (safePairProfile security scalar left) second) first| ≤ _
  exact (RationalBackgroundProfiles.convolution_profile_error security bits
    (fun left => RationalBackgroundProfiles.convolution security bits (seed security bits scalar left) second.val)
    (fun left => BackgroundCertificates.rootConvolutionProfile security (safePairProfile security scalar left) second)
    B (5 * B * (1 / (2 : ℝ)^bits)) hbound hinner first).trans_eq (by ring)

theorem residual_error (security bits : ℕ) (scalar : ℤ) (first second : Palette security) :
    |(residual security bits scalar first.val second.val : ℝ) - finiteResidual security scalar first second| ≤
      10 * pairBound security * (1 / (2 : ℝ)^bits) := by
  have hideal : finiteResidual security scalar first second =
      SafePair.canonicalPair (fun _ => 1 / (Parameters.modulus security : ℝ)) (pairProfile security scalar) first second -
        MarkedPairLeading.bodyConvolution security (fun left =>
          MarkedPairLeading.bodyConvolution security (safePairProfile security scalar left) second) first := by
    change pullbackPair (Parameters.modulus security)
      (SafeConvolution.uniformCanonical (originalProfile security scalar)) first second -
      pullbackPair (Parameters.modulus security)
        (SafeConvolution.convolution (rootResiduePairLaw security).weight (seedProfile security scalar)) first second = _
    rw [← DiffusePairEvaluation.body_pair_convolution]
    congr 1
    exact congrFun (congrFun (DiffusePairEvaluation.pair_pullback_leading _ (pairProfile security scalar)) first) second
  rw [residual, Rat.cast_sub, hideal]
  have heq : (uniformCanonical security bits scalar first.val second.val : ℝ) -
      (smoothedSeed security bits scalar first.val second.val : ℝ) -
      (SafePair.canonicalPair (fun _ => 1 / (Parameters.modulus security : ℝ)) (pairProfile security scalar) first second -
        MarkedPairLeading.bodyConvolution security (fun left =>
          MarkedPairLeading.bodyConvolution security (safePairProfile security scalar left) second) first) =
      ((uniformCanonical security bits scalar first.val second.val : ℝ) -
        SafePair.canonicalPair (fun _ => 1 / (Parameters.modulus security : ℝ)) (pairProfile security scalar) first second) -
      ((smoothedSeed security bits scalar first.val second.val : ℝ) -
        MarkedPairLeading.bodyConvolution security (fun left =>
          MarkedPairLeading.bodyConvolution security (safePairProfile security scalar left) second) first) := by ring
  rw [heq]
  exact (abs_sub _ _).trans ((add_le_add (uniformCanonical_error security bits scalar first second)
    (smoothedSeed_error security bits scalar first second)).trans_eq (by ring))

end
end CurrentAFT.RationalDiffuseResidualProgram
