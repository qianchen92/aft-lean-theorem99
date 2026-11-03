import CurrentAFT.CurrentGaussianBits
import CurrentAFT.LocalPairProgram
import CurrentAFT.ProposalCenter
import CurrentAFT.RefinedPublicOutput

/-! # Rational tables for the actual current proposal

Gaussian entries are read from the checked Boolean/list table. The inward
anchor uses the real midpoint coin, uniform index and integer point; its
smoothed table is a finite rational sum. No real inverse is queried.
-/
namespace CurrentAFT.RationalProposalProgram

open AFT GaussianSource RationalNumerics DiffuseProfiles ProposalPrimary
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def gaussianWeight (security cutoff bits : ℕ) (point : Window cutoff) : ℚ :=
  ((CurrentGaussianBits.table security cutoff bits).data.get
    ((AFT.FiniteConvolutionProgram.windowIndexEquiv cutoff).symm point)).decode

theorem gaussianWeight_eq (security cutoff bits : ℕ) (point : Window cutoff) :
    gaussianWeight security cutoff bits point =
      windowApproxWeight (WindowGaussianSampler.squaredWidth security) cutoff bits point := by
  rw [gaussianWeight, CurrentGaussianBits.table_value]
  change windowApproxWeight _ _ _
    ((AFT.FiniteConvolutionProgram.windowIndexEquiv cutoff)
      ((AFT.FiniteConvolutionProgram.windowIndexEquiv cutoff).symm point)) = _
  rw [Equiv.apply_symm_apply]

def anchorKernel (colors width primary : ℕ) (shift : ℤ) (output : ℕ) : ℚ :=
  LocalMarkedProgram.blurEntry colors width primary (-shift) primary output 0

def anchorEvaluate (security colors width cutoff bits primary output : ℕ) : ℚ :=
  ∑ scalar : Window cutoff, gaussianWeight security cutoff bits scalar *
    anchorKernel colors width primary scalar.val output

def anchor (security bits primary output : ℕ) : ℚ :=
  anchorEvaluate security (PublicParameterProgram.modulus security).count ((security + 2)^48)
    ((security + 2)^2 - 1) bits primary output

def seedWeight (security bits : ℕ) (seed : ActualSeed security) : ℚ :=
  gaussianWeight security (edgeCutoff security) bits seed.1.1 *
    gaussianWeight security (edgeCutoff security) bits seed.1.2 *
      gaussianWeight security (Parameters.sourceCutoff security - 1) bits seed.2

def seedEvaluate (security bits : ℕ) (kernel : ActualSeed security → ℚ) : ℚ :=
  ∑ seed, seedWeight security bits seed * kernel seed

def safeEntry (colors margin output : ℕ) : ℚ :=
  AFT.V7Calibration.sliceProbabilityProgram colors margin 0 output

def bodyKernel (colors margin : ℕ) (shift : ℤ) (output : ℕ) : ℚ :=
  ∑ baseline : Fin colors,
    if ((baseline.val : ℤ) + shift) % colors = (output : ℤ) then safeEntry colors margin baseline.val else 0

def body (security bits : ℕ) (includeScalar : Bool) (output : ℕ) : ℚ :=
  seedEvaluate security bits (fun seed =>
    bodyKernel (PublicParameterProgram.modulus security).count (3 * (security + 2)^2)
      (seed.1.1.val - seed.1.2.val + if includeScalar then seed.2.val else 0) output)

def diffuseKernel (colors width : ℕ) (blur second : ℤ) (output : ℕ) : ℚ :=
  (AFT.V7Calibration.averagedSliceProgram colors 1 ((width : ℤ) + blur) second width output +
    AFT.V7Calibration.averagedSliceProgram colors 1 (-2 * (width : ℤ) + 1 + blur) second width output) / 2

def diffuse (security bits output : ℕ) : ℚ :=
  seedEvaluate security bits (fun seed => diffuseKernel (PublicParameterProgram.modulus security).count
    ((security + 2)^48) (seed.1.1.val - seed.1.2.val) seed.2.val output)

/-- The same explicit balancing numerator as the current primary profile,
with every Gaussian entry and the activation rationally computed. -/
def primaryRaw (security bits output : ℕ) : ℚ :=
  let colors := (PublicParameterProgram.modulus security).count
  let legs : ℕ := (security + 2)^128
  let bodyCount : ℕ := colors * (security + 2)^96
  let free : ℚ := (bodyCount : ℚ) - legs - colors
  let rate := LocalPairProgram.activationApprox security bits
  let marked : ℚ := (legs : ℚ) * rate
  (((bodyCount + 2 * legs : ℕ) : ℚ) / colors - (free + marked) * body security bits false output -
    ((legs + colors : ℕ) : ℚ) * body security bits true output -
      2 * (legs : ℚ) * (1 - rate) * diffuse security bits output) / marked

def primaryGood (security bits : ℕ) : Prop :=
  ∀ output : Fin (PublicParameterProgram.modulus security).count,
    (1 : ℚ) / (4 * (PublicParameterProgram.modulus security).count) ≤ primaryRaw security bits output.val

instance primaryGoodDecidable (security bits : ℕ) : Decidable (primaryGood security bits) := by
  unfold primaryGood
  infer_instance

/-- An exact rational positivity check has a uniform positive fallback.
At certified precision the check succeeds and this is `primaryRaw`. -/
def primary (security bits output : ℕ) : ℚ :=
  if primaryGood security bits then primaryRaw security bits output
  else 1 / ((PublicParameterProgram.modulus security).count : ℚ)

def anchorPrimary (security bits output : ℕ) : ℚ :=
  ∑ color : Fin (PublicParameterProgram.modulus security).count,
    primary security bits color.val * anchor security bits color.val output

def compensationApprox (security bits : ℕ) : ℚ :=
  let colors := (PublicParameterProgram.modulus security).count
  let legs : ℕ := (security + 2)^128
  let bodyCount : ℕ := colors * (security + 2)^96
  (legs : ℚ) * LocalPairProgram.activationApprox security bits / ((bodyCount : ℚ) - legs - colors)

def center (security bits output : ℕ) : ℚ :=
  (1 + compensationApprox security bits) *
    safeEntry (PublicParameterProgram.modulus security).count (3 * (security + 2)^2) output -
      compensationApprox security bits * anchorPrimary security bits output

noncomputable section
open scoped Classical
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff

theorem anchorKernel_bound (colors width primary output : ℕ) (shift : ℤ) :
    |(anchorKernel colors width primary shift output : ℝ)| ≤ 1 :=
  LocalMarkedProgram.blurEntry_bound colors width primary (-shift) primary output 0

theorem anchor_point_cast (security : ℕ) (primary output : FirstHistogram.Palette security)
    (shift : ℤ) (hshift : |shift| ≤ (Parameters.sourceCutoff security : ℤ) - 1)
    (coin : Bool) (index : InwardAnchor.Index security) :
    (LocalMarkedProgram.pointEntry (Parameters.modulus security) (Parameters.anchorWidth security)
      primary.val (-shift) 0 coin index primary.val output.val : ℝ) =
      if InwardAnchor.point security primary coin index shift hshift = output then 1 else 0 := by
  have hvalue : LocalMarkedProgram.companionValue (Parameters.modulus security)
      (Parameters.anchorWidth security) primary.val (-shift) 0 coin index =
        InwardAnchor.integerPoint security primary coin index shift := by
    unfold LocalMarkedProgram.companionValue InwardAnchor.integerPoint InwardAnchor.offset
    change (Parameters.modulus security : ℤ) - 1 - primary.val +
      (if InwardAnchor.positiveDirection security primary coin then
        (Parameters.anchorWidth security : ℤ) + index.val else -((Parameters.anchorWidth security : ℤ) + index.val)) +
      0 - -shift = _
    ring
  simp only [LocalMarkedProgram.pointEntry, hvalue, true_and, Fin.ext_iff, InwardAnchor.point]
  split_ifs <;> norm_num

theorem anchorKernel_cast (security : ℕ) (primary output : FirstHistogram.Palette security)
    (shift : ℤ) (hshift : |shift| ≤ (Parameters.sourceCutoff security : ℤ) - 1) :
    (anchorKernel (Parameters.modulus security) (Parameters.anchorWidth security) primary.val shift output.val : ℝ) =
      (InwardAnchor.shiftedAnchorLaw security primary shift hshift).weight output := by
  simp only [anchorKernel, LocalMarkedProgram.blurEntry, LocalMarkedProgram.coinEntry,
    Rat.cast_div, Rat.cast_add, Rat.cast_ofNat, Rat.cast_mul, Rat.cast_inv, Rat.cast_natCast,
    Rat.cast_sum, InwardAnchor.shiftedAnchorLaw, InwardAnchor.fixedCoinLaw,
    FiniteDist.mix_weight, FiniteDist.map_weight, FiniteDist.uniform_weight,
    Fintype.card_fin, Fintype.card_bool, Nat.cast_ofNat, Fintype.sum_bool, Finset.mul_sum]
  simp_rw [anchor_point_cast security primary output shift hshift]
  simp only [mul_ite, mul_one, mul_zero]
  rw [div_eq_mul_inv, add_mul]
  simp only [Finset.sum_mul, ite_mul, zero_mul]
  simp only [mul_comm]

def approximateAnchorLaw (security bits : ℕ) (primary : FirstHistogram.Palette security) :
    FiniteDist (FirstHistogram.Palette security) :=
  (windowApproxLaw (WindowGaussianSampler.squaredWidth security)
    (Parameters.sourceCutoff security - 1) bits).mix
      (fun scalar => InwardAnchor.shiftedAnchorLaw security primary scalar.val (InwardAnchor.scalar_bound security scalar))

theorem anchorEvaluate_cast (security bits : ℕ) (primary output : FirstHistogram.Palette security) :
    (anchorEvaluate security (Parameters.modulus security) (Parameters.anchorWidth security)
      (Parameters.sourceCutoff security - 1) bits primary.val output.val : ℝ) =
        (approximateAnchorLaw security bits primary).weight output := by
  simp only [anchorEvaluate, Rat.cast_sum, Rat.cast_mul, gaussianWeight_eq, approximateAnchorLaw,
    FiniteDist.mix_weight, windowApproxLaw]
  apply Finset.sum_congr rfl
  intro scalar _
  rw [anchorKernel_cast security primary output scalar.val (InwardAnchor.scalar_bound security scalar)]

theorem anchor_cast (security bits : ℕ) (primary output : FirstHistogram.Palette security) :
    (anchor security bits primary.val output.val : ℝ) = (approximateAnchorLaw security bits primary).weight output := by
  unfold anchor
  rw [PublicParameterProgram.modulus_value]
  have hA : (security + 2)^48 = Parameters.anchorWidth security := by
    simp only [anchorWidth_eq, Parameters.base]
  have hB : (security + 2)^2 = Parameters.sourceCutoff security := by
    simp only [Parameters.sourceCutoff, Parameters.base]
  rw [hA, hB]
  exact anchorEvaluate_cast security bits primary output

theorem anchor_error (security bits : ℕ) (primary output : FirstHistogram.Palette security) :
    |(anchor security bits primary.val output.val : ℝ) -
      (InwardAnchor.smoothedAnchorLaw security primary).weight output| ≤ 1 / (2 : ℝ)^bits := by
  rw [anchor_cast]
  have hl1 := windowApproxLaw_l1 (WindowGaussianSampler.squaredWidth security)
    (Parameters.sourceWidth security) (Parameters.sourceCutoff security - 1) bits
    (WindowGaussianSampler.squaredWidth_positive security) (WindowGaussianSampler.squaredWidth_real security).symm
  have h := CyclePatternProgram.expectation_difference_le_l1
    (windowApproxLaw (WindowGaussianSampler.squaredWidth security) (Parameters.sourceCutoff security - 1) bits)
    (scalarLaw security)
    (fun scalar => (InwardAnchor.shiftedAnchorLaw security primary scalar.val
      (InwardAnchor.scalar_bound security scalar)).weight output) 1 (fun scalar => by
      rw [abs_of_nonneg ((InwardAnchor.shiftedAnchorLaw security primary scalar.val
        (InwardAnchor.scalar_bound security scalar)).nonneg output)]
      exact (InwardAnchor.shiftedAnchorLaw security primary scalar.val
        (InwardAnchor.scalar_bound security scalar)).atom_le_one output)
  exact h.trans (by simpa only [one_mul] using hl1)

theorem anchor_nonneg (security bits : ℕ) (primary output : FirstHistogram.Palette security) :
    0 ≤ anchor security bits primary.val output.val := by
  have h := (approximateAnchorLaw security bits primary).nonneg output
  rw [← anchor_cast] at h
  exact_mod_cast h

theorem anchor_mass (security bits : ℕ) (primary : FirstHistogram.Palette security) :
    (∑ output : FirstHistogram.Palette security, anchor security bits primary.val output.val) = 1 := by
  have h := (approximateAnchorLaw security bits primary).sum_one
  simp_rw [← anchor_cast] at h
  exact_mod_cast h

theorem anchor_zero_outside (security bits : ℕ) (primary output : FirstHistogram.Palette security)
    (hunsafe : ¬InwardAnchor.SafeColor security output) :
    anchor security bits primary.val output.val = 0 := by
  have h : (anchor security bits primary.val output.val : ℝ) = 0 := by
    rw [anchor_cast]
    simp only [approximateAnchorLaw, FiniteDist.mix_weight,
      InwardAnchor.shiftedAnchorLaw_zero_outside security primary _ _ output hunsafe,
      mul_zero, Finset.sum_const_zero]
  exact_mod_cast h

def approximateSeedLaw (security bits : ℕ) : FiniteDist (ActualSeed security) :=
  ((windowApproxLaw (WindowGaussianSampler.squaredWidth security) (edgeCutoff security) bits).prod
    (windowApproxLaw (WindowGaussianSampler.squaredWidth security) (edgeCutoff security) bits)).prod
    (windowApproxLaw (WindowGaussianSampler.squaredWidth security) (Parameters.sourceCutoff security - 1) bits)

theorem seedWeight_cast (security bits : ℕ) (seed : ActualSeed security) :
    (seedWeight security bits seed : ℝ) = (approximateSeedLaw security bits).weight seed := by
  simp only [seedWeight, Rat.cast_mul, gaussianWeight_eq, approximateSeedLaw,
    FiniteDist.prod_weight, windowApproxLaw]

theorem seedEvaluate_cast (security bits : ℕ) (kernel : ActualSeed security → ℚ) :
    (seedEvaluate security bits kernel : ℝ) =
      (approximateSeedLaw security bits).expectation (fun seed => (kernel seed : ℝ)) := by
  simp only [seedEvaluate, Rat.cast_sum, Rat.cast_mul, seedWeight_cast, FiniteDist.expectation]

theorem seed_l1 (security bits : ℕ) :
    (∑ seed, |(approximateSeedLaw security bits).weight seed - (actualSeedLaw security).weight seed|) ≤
      3 / (2 : ℝ)^bits := by
  have he := windowApproxLaw_l1 (WindowGaussianSampler.squaredWidth security) (Parameters.sourceWidth security)
    (edgeCutoff security) bits (WindowGaussianSampler.squaredWidth_positive security)
    (WindowGaussianSampler.squaredWidth_real security).symm
  have hs := windowApproxLaw_l1 (WindowGaussianSampler.squaredWidth security) (Parameters.sourceWidth security)
    (Parameters.sourceCutoff security - 1) bits (WindowGaussianSampler.squaredWidth_positive security)
    (WindowGaussianSampler.squaredWidth_real security).symm
  have hp := FiniteDist.l1_prod_le
    (windowApproxLaw (WindowGaussianSampler.squaredWidth security) (edgeCutoff security) bits)
    (edgeLaw security)
    (windowApproxLaw (WindowGaussianSampler.squaredWidth security) (edgeCutoff security) bits) (edgeLaw security)
  have hall := FiniteDist.l1_prod_le
    ((windowApproxLaw (WindowGaussianSampler.squaredWidth security) (edgeCutoff security) bits).prod
      (windowApproxLaw (WindowGaussianSampler.squaredWidth security) (edgeCutoff security) bits))
    ((edgeLaw security).prod (edgeLaw security))
    (windowApproxLaw (WindowGaussianSampler.squaredWidth security) (Parameters.sourceCutoff security - 1) bits)
    (scalarLaw security)
  exact hall.trans ((add_le_add (hp.trans (add_le_add he he)) hs).trans_eq (by ring))

theorem shift_condition (security : ℕ) (shift : ℤ) (baseline output : FirstHistogram.Palette security) :
    shiftEquiv security shift baseline = output ↔
      ((baseline.val : ℤ) + shift) % Parameters.modulus security = (output.val : ℤ) := by
  rw [← (ZMod.finEquiv (Parameters.modulus security)).injective.eq_iff]
  change RefinedPublicOutput.embed security (shiftEquiv security shift baseline) =
    RefinedPublicOutput.embed security output ↔ _
  rw [RefinedPublicOutput.embed_shift, RefinedPublicOutput.embed_value, RefinedPublicOutput.embed_value]
  have hcast : (baseline.val : ZMod (Parameters.modulus security)) + (shift : ZMod (Parameters.modulus security)) =
      (((baseline.val : ℤ) + shift : ℤ) : ZMod (Parameters.modulus security)) := by push_cast; rfl
  rw [hcast]
  have hout : (output.val : ZMod (Parameters.modulus security)) =
      ((output.val : ℤ) : ZMod (Parameters.modulus security)) := by simp only [Int.cast_natCast]
  rw [hout]
  rw [ZMod.intCast_eq_intCast_iff', Int.emod_eq_of_lt (Int.natCast_nonneg _)
    (by exact_mod_cast output.isLt)]

theorem bodyKernel_cast (security : ℕ) (shift : ℤ) (output : FirstHistogram.Palette security) :
    (bodyKernel (Parameters.modulus security) (Parameters.safeMargin security) shift output.val : ℝ) =
      ((safeLaw security).map (shiftEquiv security shift)).weight output := by
  simp only [bodyKernel, Rat.cast_sum, FiniteDist.map_weight]
  apply Finset.sum_congr rfl
  intro baseline _
  rw [shift_condition]
  split_ifs
  · rw [safeEntry, AFT.V7Calibration.sliceProbabilityProgram_cast,
      safeLaw, TrimmedSlice.finiteLaw_weight]
  · norm_num

theorem bodyKernel_bound (security : ℕ) (shift : ℤ) (output : FirstHistogram.Palette security) :
    |(bodyKernel (Parameters.modulus security) (Parameters.safeMargin security) shift output.val : ℝ)| ≤ 1 := by
  rw [bodyKernel_cast, abs_of_nonneg (((safeLaw security).map (shiftEquiv security shift)).nonneg output)]
  exact ((safeLaw security).map (shiftEquiv security shift)).atom_le_one output

def approximateBodyLaw (security bits : ℕ) (includeScalar : Bool) : FiniteDist (FirstHistogram.Palette security) :=
  (approximateSeedLaw security bits).mix (fun seed => (safeLaw security).map
    (shiftEquiv security (actualBlur security seed + if includeScalar then actualSecond security seed else 0)))

theorem body_cast (security bits : ℕ) (includeScalar : Bool) (output : FirstHistogram.Palette security) :
    (body security bits includeScalar output.val : ℝ) = (approximateBodyLaw security bits includeScalar).weight output := by
  unfold body
  rw [seedEvaluate_cast, PublicParameterProgram.modulus_value]
  have hM : 3 * (security + 2)^2 = Parameters.safeMargin security := by
    simp only [Parameters.safeMargin, Parameters.sourceCutoff, Parameters.base]
  simp_rw [hM, bodyKernel_cast]
  rfl

theorem body_error (security bits : ℕ) (includeScalar : Bool) (output : FirstHistogram.Palette security) :
    |(body security bits includeScalar output.val : ℝ) - (bodyLaw security includeScalar).weight output| ≤
      3 / (2 : ℝ)^bits := by
  rw [body_cast]
  exact (CyclePatternProgram.expectation_difference_le_l1 (approximateSeedLaw security bits)
    (actualSeedLaw security) (fun seed => ((safeLaw security).map
      (shiftEquiv security (actualBlur security seed + if includeScalar then actualSecond security seed else 0))).weight output)
      1 (fun seed => by
        rw [abs_of_nonneg (FiniteDist.nonneg _ _)]
        exact FiniteDist.atom_le_one _ _)).trans (by simpa only [one_mul] using seed_l1 security bits)

theorem diffuseKernel_bound (colors width output : ℕ) (blur second : ℤ) :
    |(diffuseKernel colors width blur second output : ℝ)| ≤ 1 := by
  have hp := AFT.V7Calibration.averagedSliceProgram_abs_le_one colors 1
    ((width : ℤ) + blur) second width output
  have hm := AFT.V7Calibration.averagedSliceProgram_abs_le_one colors 1
    (-2 * (width : ℤ) + 1 + blur) second width output
  simp only [diffuseKernel, Rat.cast_div, Rat.cast_add, Rat.cast_ofNat, abs_div,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact (div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num : (0 : ℝ) ≤ 2)).trans
    (by linarith only [hp, hm])

def fairProfile (security : ℕ) (source : FiniteDist (ActualSeed security))
    (output : FirstHistogram.Palette security) : ℝ :=
  (profile (Parameters.modulus security) (Parameters.anchorWidth security) 1 true source
      (actualBlur security) (actualSecond security) output +
    profile (Parameters.modulus security) (Parameters.anchorWidth security) 1 false source
      (actualBlur security) (actualSecond security) output) / 2

theorem fairProfile_expectation (security : ℕ) (source : FiniteDist (ActualSeed security))
    (output : FirstHistogram.Palette security) :
    fairProfile security source output = source.expectation (fun seed =>
      (diffuseKernel (Parameters.modulus security) (Parameters.anchorWidth security)
        (actualBlur security seed) (actualSecond security seed) output.val : ℝ)) := by
  simp only [fairProfile, profile, TrimmedSlice.mixedLaw, FiniteDist.expectation,
    diffuseKernel, Rat.cast_div, Rat.cast_add, Rat.cast_ofNat,
    AFT.V7Calibration.averagedSliceProgram_cast, intervalStart,
    if_true, Bool.false_eq_true, if_false]
  simp only [mul_div, mul_add]
  rw [← Finset.sum_div, Finset.sum_add_distrib]

theorem fairProfile_mass (security : ℕ) (source : FiniteDist (ActualSeed security)) :
    ∑ output, fairProfile security source output = 1 := by
  have hm (positive : Bool) : ∑ color, profile (Parameters.modulus security) (Parameters.anchorWidth security)
      1 positive source (actualBlur security) (actualSecond security) color = 1 := by
    exact profile_mass _ _ _ _ _ _ _ ((Parameters.sourceCutoff security : ℤ) - 1)
      ((Parameters.sourceCutoff security : ℤ) - 1)
      (by rw [anchorWidth_eq]; exact pow_pos (Parameters.base_pos security) _)
      (by norm_num) (actualBlur_bound security) (actualSecond_bound security) (by
        have h := deletion_clearance security
        unfold deletion at h
        omega)
  simp only [fairProfile, ← Finset.sum_div, Finset.sum_add_distrib, hm]
  norm_num

def approximateDiffuseLaw (security bits : ℕ) : FiniteDist (FirstHistogram.Palette security) where
  weight := fairProfile security (approximateSeedLaw security bits)
  nonneg output := div_nonneg (add_nonneg (profile_nonneg _ _ _ _ _ _ _ _) (profile_nonneg _ _ _ _ _ _ _ _))
    (by norm_num)
  sum_one := fairProfile_mass security _

theorem diffuse_cast (security bits : ℕ) (output : FirstHistogram.Palette security) :
    (diffuse security bits output.val : ℝ) = (approximateDiffuseLaw security bits).weight output := by
  unfold diffuse
  rw [seedEvaluate_cast, PublicParameterProgram.modulus_value]
  have hA : (security + 2)^48 = Parameters.anchorWidth security := by
    simp only [anchorWidth_eq, Parameters.base]
  rw [hA]
  exact (fairProfile_expectation security (approximateSeedLaw security bits) output).symm

theorem diffuse_error (security bits : ℕ) (output : FirstHistogram.Palette security) :
    |(diffuse security bits output.val : ℝ) - diffuseMean security output| ≤ 3 / (2 : ℝ)^bits := by
  rw [diffuse_cast]
  change |fairProfile security (approximateSeedLaw security bits) output -
    fairProfile security (actualSeedLaw security) output| ≤ _
  rw [fairProfile_expectation, fairProfile_expectation]
  exact (CyclePatternProgram.expectation_difference_le_l1 _ _ _ 1
    (fun seed => diffuseKernel_bound _ _ _ _ _)).trans
      (by simpa only [one_mul] using seed_l1 security bits)

theorem activationApprox_pos (security bits : ℕ) :
    0 < (LocalPairProgram.activationApprox security bits : ℝ) := by
  have h : 0 < LocalPairProgram.activationApprox security bits :=
    mul_pos (by norm_num) (windowApproxWeight_positive _ _ _ _)
  exact_mod_cast h

theorem primaryRaw_cast (security bits : ℕ) (output : FirstHistogram.Palette security) :
    (primaryRaw security bits output.val : ℝ) =
      ((Parameters.dimension security : ℝ) / Parameters.modulus security -
        (freeMass security + (Parameters.legCount security : ℝ) * LocalPairProgram.activationApprox security bits) *
          (approximateBodyLaw security bits false).weight output -
        ((Parameters.legCount security : ℝ) + Parameters.modulus security) *
          (approximateBodyLaw security bits true).weight output -
        2 * Parameters.legCount security * (1 - (LocalPairProgram.activationApprox security bits : ℝ)) *
          (approximateDiffuseLaw security bits).weight output) /
        ((Parameters.legCount security : ℝ) * LocalPairProgram.activationApprox security bits) := by
  have hL : (security + 2)^128 = Parameters.legCount security := by
    simp only [Parameters.legCount_eq, Parameters.base]
  have hB : Parameters.modulus security * (security + 2)^96 = Parameters.bodySize security := by
    simp only [Parameters.bodySize_eq, Parameters.base]
  unfold primaryRaw
  dsimp only
  rw [PublicParameterProgram.modulus_value, hL, hB]
  simp only [Rat.cast_div, Rat.cast_sub, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast,
    Rat.cast_ofNat, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, body_cast, diffuse_cast]
  simp only [freeMass, Parameters.dimension, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Rat.cast_one]

theorem primaryRaw_mass (security bits : ℕ) :
    (∑ output : FirstHistogram.Palette security, primaryRaw security bits output.val) = 1 := by
  have hq : (Parameters.modulus security : ℝ) ≠ 0 := (FirstResponse.modulus_pos security).ne'
  have hl : (Parameters.legCount security : ℝ) ≠ 0 := by
    apply Nat.cast_ne_zero.mpr
    rw [Parameters.legCount_eq]
    exact (pow_pos (Parameters.base_pos security) 128).ne'
  have hr := (activationApprox_pos security bits).ne'
  have hmass : (∑ output : FirstHistogram.Palette security, (primaryRaw security bits output.val : ℝ)) = 1 := by
    simp_rw [primaryRaw_cast]
    simp only [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum,
      FiniteDist.sum_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    unfold freeMass
    simp only [Parameters.dimension, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    field_simp [hq, hl, hr]
    ring
  exact_mod_cast hmass

private theorem balancing_residual_bound
    (free legs colors dimension rate activation bzero bone diffuse primary
      bzero' bone' diffuse' epsilon : ℝ)
    (hfree : 0 ≤ free) (hlegs : 0 ≤ legs) (hcolors : 0 ≤ colors)
    (hdimension : free + 3 * legs + colors = dimension)
    (hrate : 0 ≤ rate ∧ rate ≤ 1) (hepsilon : 0 ≤ epsilon)
    (hbzero : 0 ≤ bzero ∧ bzero ≤ 1) (hdiffuse : 0 ≤ diffuse ∧ diffuse ≤ 1)
    (hprimary : 0 ≤ primary ∧ primary ≤ 1)
    (hzeroError : |bzero - bzero'| ≤ 3 * epsilon)
    (honeError : |bone - bone'| ≤ 3 * epsilon)
    (hdiffuseError : |diffuse - diffuse'| ≤ 3 * epsilon)
    (hrateError : |rate - activation| ≤ epsilon / 2)
    (hbalance : dimension / colors - (free + legs * activation) * bzero -
      (legs + colors) * bone - 2 * legs * (1 - activation) * diffuse = legs * activation * primary) :
    |dimension / colors - (free + legs * rate) * bzero' - (legs + colors) * bone' -
      2 * legs * (1 - rate) * diffuse' - legs * rate * primary| ≤ 8 * dimension * epsilon := by
  have hrateNonneg := hrate.1
  have hgap : |-bzero + 2 * diffuse - primary| ≤ 4 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have hzero : |(free + legs * rate) * (bzero - bzero')| ≤ (free + legs) * (3 * epsilon) := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ free + legs * rate)]
    exact mul_le_mul (by nlinarith) hzeroError (abs_nonneg _) (by positivity)
  have hone : |(legs + colors) * (bone - bone')| ≤ (legs + colors) * (3 * epsilon) := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ legs + colors)]
    exact mul_le_mul_of_nonneg_left honeError (by positivity)
  have hdiff : |(2 * legs * (1 - rate)) * (diffuse - diffuse')| ≤ (2 * legs) * (3 * epsilon) := by
    have hcoef : 0 ≤ 2 * legs * (1 - rate) := mul_nonneg (by positivity) (by linarith only [hrate.2])
    rw [abs_mul, abs_of_nonneg hcoef]
    exact mul_le_mul (by nlinarith [hrate.1]) hdiffuseError (abs_nonneg _) (by positivity)
  have hrateTerm : |legs * (rate - activation) * (-bzero + 2 * diffuse - primary)| ≤
      (legs * (epsilon / 2)) * 4 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hlegs]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hrateError hlegs) hgap (abs_nonneg _) (by positivity)
  have hdecompose : dimension / colors - (free + legs * rate) * bzero' - (legs + colors) * bone' -
      2 * legs * (1 - rate) * diffuse' - legs * rate * primary =
      (free + legs * rate) * (bzero - bzero') + (legs + colors) * (bone - bone') +
        (2 * legs * (1 - rate)) * (diffuse - diffuse') +
          legs * (rate - activation) * (-bzero + 2 * diffuse - primary) := by
    linear_combination hbalance
  rw [hdecompose]
  calc
    _ ≤ |(free + legs * rate) * (bzero - bzero')| + |(legs + colors) * (bone - bone')| +
        |(2 * legs * (1 - rate)) * (diffuse - diffuse')| +
          |legs * (rate - activation) * (-bzero + 2 * diffuse - primary)| :=
      (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
        (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
    _ ≤ (free + legs) * (3 * epsilon) + (legs + colors) * (3 * epsilon) +
        (2 * legs) * (3 * epsilon) + (legs * (epsilon / 2)) * 4 :=
      add_le_add (add_le_add (add_le_add hzero hone) hdiff) hrateTerm
    _ = (3 * free + 14 * legs + 3 * colors) * epsilon := by ring
    _ ≤ (8 * dimension) * epsilon :=
      mul_le_mul_of_nonneg_right (by nlinarith only [hdimension, hfree, hlegs, hcolors]) hepsilon
    _ = _ := by ring

theorem primaryRaw_error (security bits : ℕ) (output : FirstHistogram.Palette security)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ))) :
    |(primaryRaw security bits output.val : ℝ) - primaryProfile security output| ≤
      64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) := by
  let epsilon : ℝ := 1 / (2 : ℝ)^bits
  let rate : ℝ := LocalPairProgram.activationApprox security bits
  have hepsilon : 0 ≤ epsilon := by dsimp only [epsilon]; positivity
  have hb := FirstResponse.base_pos security
  have hrate := LocalPairProgram.activationApprox_bounds security bits
  have hrateError : |rate - DiffuseProfiles.activation security| ≤ epsilon / 2 := by
    exact (LocalPairProgram.activationApprox_error security bits).trans_eq (by dsimp only [epsilon]; ring)
  have hrateLower : 1 / (8 * (Parameters.base security : ℝ)) ≤ rate := by
    have ha := FirstResponse.activation_lower_simple security
    have hfrac : 1 / (8 * (Parameters.base security : ℝ)) = (1 / (4 * (Parameters.base security : ℝ))) / 2 := by ring
    rw [hfrac]
    linarith [(abs_le.mp hrateError).1, hprecision]
  have hlegsPos : (0 : ℝ) < Parameters.legCount security := by
    exact_mod_cast (show 0 < Parameters.legCount security by
      rw [Parameters.legCount_eq]; exact pow_pos (Parameters.base_pos security) _)
  have hlegsOne : (1 : ℝ) ≤ Parameters.legCount security := by
    exact_mod_cast (show 1 ≤ Parameters.legCount security by
      have h : 0 < Parameters.legCount security := Nat.cast_pos.mp hlegsPos; omega)
  have hden : 0 < (Parameters.legCount security : ℝ) * rate :=
    mul_pos hlegsPos (activationApprox_pos security bits)
  have hdenLower : 1 / (8 * (Parameters.base security : ℝ)) ≤
      (Parameters.legCount security : ℝ) * rate :=
    hrateLower.trans (by nlinarith [activationApprox_pos security bits])
  have hdimension : freeMass security + 3 * (Parameters.legCount security : ℝ) +
      Parameters.modulus security = Parameters.dimension security := by
    unfold freeMass Parameters.dimension
    push_cast
    ring
  have hbalance : (Parameters.dimension security : ℝ) / Parameters.modulus security -
      (freeMass security + (Parameters.legCount security : ℝ) * DiffuseProfiles.activation security) * (bodyLaw security false).weight output -
      ((Parameters.legCount security : ℝ) + Parameters.modulus security) * (bodyLaw security true).weight output -
      2 * Parameters.legCount security * (1 - DiffuseProfiles.activation security) * diffuseMean security output =
      (Parameters.legCount security : ℝ) * DiffuseProfiles.activation security * primaryProfile security output := by
    unfold primaryProfile markMass
    field_simp [(DiffuseProfiles.activation_pos security).ne', hlegsPos.ne']
  have hprimary : 0 ≤ primaryProfile security output ∧ primaryProfile security output ≤ 1 :=
    ⟨(primaryLaw security).nonneg output, (primaryLaw security).atom_le_one output⟩
  have hdiffuse : 0 ≤ diffuseMean security output ∧ diffuseMean security output ≤ 1 := by
    refine ⟨diffuseMean_nonneg security output, ?_⟩
    rw [← diffuseMean_mass security]
    exact Finset.single_le_sum (fun color _ => diffuseMean_nonneg security color) (Finset.mem_univ output)
  have hzeroError : |(bodyLaw security false).weight output - (approximateBodyLaw security bits false).weight output| ≤
      3 * epsilon := by
    rw [abs_sub_comm, ← body_cast]
    exact (body_error security bits false output).trans_eq (by dsimp only [epsilon]; ring)
  have honeError : |(bodyLaw security true).weight output - (approximateBodyLaw security bits true).weight output| ≤
      3 * epsilon := by
    rw [abs_sub_comm, ← body_cast]
    exact (body_error security bits true output).trans_eq (by dsimp only [epsilon]; ring)
  have hdiffuseError : |diffuseMean security output - (approximateDiffuseLaw security bits).weight output| ≤
      3 * epsilon := by
    rw [abs_sub_comm, ← diffuse_cast]
    exact (diffuse_error security bits output).trans_eq (by dsimp only [epsilon]; ring)
  have hresidual := balancing_residual_bound (freeMass security) (Parameters.legCount security)
    (Parameters.modulus security) (Parameters.dimension security) rate (DiffuseProfiles.activation security)
    ((bodyLaw security false).weight output) ((bodyLaw security true).weight output)
    (diffuseMean security output) (primaryProfile security output)
    ((approximateBodyLaw security bits false).weight output) ((approximateBodyLaw security bits true).weight output)
    ((approximateDiffuseLaw security bits).weight output) epsilon (freeMass_nonneg security) hlegsPos.le
    (Nat.cast_nonneg _) hdimension ⟨hrate.1, by linarith only [hrate.2]⟩ hepsilon
    ⟨(bodyLaw security false).nonneg output, (bodyLaw security false).atom_le_one output⟩ hdiffuse hprimary
    hzeroError honeError hdiffuseError hrateError hbalance
  rw [primaryRaw_cast]
  have hquotient (numerator : ℝ) : |numerator / ((Parameters.legCount security : ℝ) * rate) -
      primaryProfile security output| =
      |numerator - (Parameters.legCount security : ℝ) * rate * primaryProfile security output| /
        ((Parameters.legCount security : ℝ) * rate) := by
    rw [div_sub' hden.ne', abs_div, abs_of_pos hden]
  rw [hquotient]
  calc
    _ ≤ (8 * Parameters.dimension security * epsilon) / ((Parameters.legCount security : ℝ) * rate) :=
      div_le_div_of_nonneg_right hresidual hden.le
    _ ≤ (8 * Parameters.dimension security * epsilon) / (1 / (8 * (Parameters.base security : ℝ))) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hdenLower
    _ = _ := by dsimp only [epsilon]; field_simp; ring

theorem primaryRaw_lower (security bits : ℕ)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) (output : FirstHistogram.Palette security) :
    1 / (4 * (Parameters.modulus security : ℝ)) ≤ (primaryRaw security bits output.val : ℝ) := by
  have herr := (abs_le.mp (primaryRaw_error security bits output hprecision)).1
  have hp := primaryProfile_atom_lower security output
  have hfrac : (1 : ℝ) / (2 * Parameters.modulus security) = 2 * (1 / (4 * Parameters.modulus security)) := by ring
  rw [hfrac] at hp
  linarith

theorem primaryGood_of_precision (security bits : ℕ)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) : primaryGood security bits := by
  unfold primaryGood
  rw [PublicParameterProgram.modulus_value]
  intro output
  apply (Rat.cast_le (K := ℝ)).mp
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast] using
    primaryRaw_lower security bits hprecision hbudget output

theorem primary_lower (security bits : ℕ) (output : FirstHistogram.Palette security) :
    1 / (4 * (Parameters.modulus security : ℝ)) ≤ (primary security bits output.val : ℝ) := by
  unfold primary
  split_ifs with hgood
  · unfold primaryGood at hgood
    rw [PublicParameterProgram.modulus_value] at hgood
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast] using
      (Rat.cast_le (K := ℝ)).mpr (hgood output)
  · simp only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast, PublicParameterProgram.modulus_value]
    have hq := FirstResponse.modulus_pos security
    apply one_div_le_one_div_of_le hq
    nlinarith

theorem primary_mass (security bits : ℕ) :
    (∑ output : FirstHistogram.Palette security, primary security bits output.val) = 1 := by
  unfold primary
  by_cases hgood : primaryGood security bits
  · simp only [if_pos hgood]
    exact primaryRaw_mass security bits
  · simp only [if_neg hgood, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, PublicParameterProgram.modulus_value]
    have hq : (Parameters.modulus security : ℚ) ≠ 0 := by
      exact_mod_cast (Parameters.modulus_spec security).2.ne_zero
    field_simp

def approximatePrimaryLaw (security bits : ℕ) : FiniteDist (FirstHistogram.Palette security) where
  weight output := primary security bits output.val
  nonneg output := (by positivity : (0 : ℝ) ≤ 1 / (4 * (Parameters.modulus security : ℝ))).trans
    (primary_lower security bits output)
  sum_one := by exact_mod_cast primary_mass security bits

theorem primary_error (security bits : ℕ) (output : FirstHistogram.Palette security)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) :
    |(primary security bits output.val : ℝ) - primaryProfile security output| ≤
      64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) := by
  rw [primary, if_pos (primaryGood_of_precision security bits hprecision hbudget)]
  exact primaryRaw_error security bits output hprecision

theorem approximateAnchorLaw_height (security bits : ℕ) (primary output : FirstHistogram.Palette security) :
    (approximateAnchorLaw security bits primary).weight output ≤ 1 / (Parameters.anchorWidth security : ℝ) := by
  unfold approximateAnchorLaw
  simp only [FiniteDist.mix_weight]
  calc
    _ ≤ ∑ scalar, (windowApproxLaw (WindowGaussianSampler.squaredWidth security)
        (Parameters.sourceCutoff security - 1) bits).weight scalar * (1 / (Parameters.anchorWidth security : ℝ)) :=
      Finset.sum_le_sum (fun scalar _ => mul_le_mul_of_nonneg_left
        (InwardAnchor.shiftedAnchorLaw_height security primary scalar.val
          (InwardAnchor.scalar_bound security scalar) output) (FiniteDist.nonneg _ _))
    _ = _ := by rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]

def approximateAnchorPrimaryLaw (security bits : ℕ) : FiniteDist (FirstHistogram.Palette security) :=
  (approximatePrimaryLaw security bits).mix (approximateAnchorLaw security bits)

theorem anchorPrimary_cast (security bits : ℕ) (output : FirstHistogram.Palette security) :
    (anchorPrimary security bits output.val : ℝ) = (approximateAnchorPrimaryLaw security bits).weight output := by
  unfold anchorPrimary
  rw [PublicParameterProgram.modulus_value]
  simp only [Rat.cast_sum, Rat.cast_mul, anchor_cast, approximateAnchorPrimaryLaw, FiniteDist.mix_weight]
  rfl

theorem approximateAnchorPrimaryLaw_height (security bits : ℕ) (output : FirstHistogram.Palette security) :
    (approximateAnchorPrimaryLaw security bits).weight output ≤ 1 / (Parameters.anchorWidth security : ℝ) := by
  unfold approximateAnchorPrimaryLaw
  simp only [FiniteDist.mix_weight]
  calc
    _ ≤ ∑ primary, (approximatePrimaryLaw security bits).weight primary * (1 / (Parameters.anchorWidth security : ℝ)) :=
      Finset.sum_le_sum (fun primary _ => mul_le_mul_of_nonneg_left
        (approximateAnchorLaw_height security bits primary output) (FiniteDist.nonneg _ _))
    _ = _ := by rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]

theorem approximateAnchorPrimaryLaw_zero_outside (security bits : ℕ) (output : FirstHistogram.Palette security)
    (hunsafe : ¬InwardAnchor.SafeColor security output) :
    (approximateAnchorPrimaryLaw security bits).weight output = 0 := by
  simp only [approximateAnchorPrimaryLaw, FiniteDist.mix_weight, ← anchor_cast,
    anchor_zero_outside security bits _ output hunsafe, Rat.cast_zero, mul_zero, Finset.sum_const_zero]

theorem compensationApprox_cast (security bits : ℕ) :
    (compensationApprox security bits : ℝ) =
      (Parameters.legCount security : ℝ) * LocalPairProgram.activationApprox security bits / freeMass security := by
  have hL : (security + 2)^128 = Parameters.legCount security := by
    simp only [Parameters.legCount_eq, Parameters.base]
  have hB : Parameters.modulus security * (security + 2)^96 = Parameters.bodySize security := by
    simp only [Parameters.bodySize_eq, Parameters.base]
  unfold compensationApprox
  dsimp only
  rw [PublicParameterProgram.modulus_value, hL, hB]
  simp only [Rat.cast_div, Rat.cast_mul, Rat.cast_sub, Rat.cast_natCast, freeMass]

theorem compensationApprox_nonneg (security bits : ℕ) : 0 ≤ (compensationApprox security bits : ℝ) := by
  rw [compensationApprox_cast]
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (activationApprox_pos security bits).le) (freeMass_pos security).le

theorem compensationApprox_le_leg_body (security bits : ℕ) :
    (compensationApprox security bits : ℝ) ≤ (Parameters.legCount security : ℝ) / Parameters.bodySize security := by
  have hnum : (Parameters.legCount security : ℝ) * LocalPairProgram.activationApprox security bits ≤
      (Parameters.legCount security : ℝ) / 2 := by
    nlinarith [mul_le_mul_of_nonneg_left (LocalPairProgram.activationApprox_bounds security bits).2
      (Nat.cast_nonneg (Parameters.legCount security) : (0 : ℝ) ≤ Parameters.legCount security)]
  rw [compensationApprox_cast]
  calc
    _ ≤ ((Parameters.legCount security : ℝ) / 2) / freeMass security :=
      div_le_div_of_nonneg_right hnum (freeMass_pos security).le
    _ ≤ ((Parameters.legCount security : ℝ) / 2) / ((Parameters.bodySize security : ℝ) / 2) :=
      div_le_div_of_nonneg_left (by positivity) (half_pos (bodySize_pos security)) (freeMass_lower security)
    _ = _ := by ring

theorem compensationApprox_le_one (security bits : ℕ) : (compensationApprox security bits : ℝ) ≤ 1 := by
  apply (compensationApprox_le_leg_body security bits).trans
  apply (div_le_one (bodySize_pos security)).mpr
  exact_mod_cast (show Parameters.legCount security ≤ Parameters.bodySize security by
    have := population_room security; omega)

theorem compensationApprox_anchor_cost (security bits : ℕ) :
    (compensationApprox security bits : ℝ) / Parameters.anchorWidth security ≤ safeHeight security / 2 := by
  have hA : (0 : ℝ) < Parameters.anchorWidth security := by exact_mod_cast InwardAnchor.anchorWidth_pos security
  have hB := bodySize_pos security
  have hq := FirstResponse.modulus_pos security
  have hbudget : 2 * (Parameters.legCount security : ℝ) * Parameters.modulus security ≤
      Parameters.bodySize security * Parameters.anchorWidth security := by
    exact_mod_cast anchor_center_budget security
  have hfirst : ((Parameters.legCount security : ℝ) / Parameters.bodySize security) /
      Parameters.anchorWidth security ≤ 1 / (2 * (Parameters.modulus security : ℝ)) := by
    rw [div_div]
    apply (div_le_div_iff₀ (mul_pos hB hA) (by positivity)).mpr
    nlinarith only [hbudget]
  have hs : (Parameters.modulus security : ℝ) - 2 * Parameters.safeMargin security ≤ Parameters.modulus security := by
    have hM : (0 : ℝ) ≤ Parameters.safeMargin security := Nat.cast_nonneg _
    linarith
  have hsafe : 1 / (Parameters.modulus security : ℝ) ≤ safeHeight security := by
    unfold safeHeight
    apply one_div_le_one_div_of_le
    · have h := Nat.cast_lt (α := ℝ).mpr (safe_clearance security)
      push_cast at h
      linarith
    · exact hs
  exact (div_le_div_of_nonneg_right (compensationApprox_le_leg_body security bits) hA.le).trans
    (hfirst.trans (by convert div_le_div_of_nonneg_right hsafe (by norm_num : (0 : ℝ) ≤ 2) using 1; ring))

def approximateCenterProfile (security bits : ℕ) (output : FirstHistogram.Palette security) : ℝ :=
  (1 + (compensationApprox security bits : ℝ)) * (safeLaw security).weight output -
    (compensationApprox security bits : ℝ) * (approximateAnchorPrimaryLaw security bits).weight output

theorem center_cast (security bits : ℕ) (output : FirstHistogram.Palette security) :
    (center security bits output.val : ℝ) = approximateCenterProfile security bits output := by
  unfold center
  rw [PublicParameterProgram.modulus_value]
  have hM : 3 * (security + 2)^2 = Parameters.safeMargin security := by
    simp only [Parameters.safeMargin, Parameters.sourceCutoff, Parameters.base]
  rw [hM]
  simp only [Rat.cast_sub, Rat.cast_mul, Rat.cast_add, Rat.cast_one, anchorPrimary_cast]
  rw [safeEntry, AFT.V7Calibration.sliceProbabilityProgram_cast]
  change (1 + (compensationApprox security bits : ℝ)) * TrimmedSlice.law _ _ _ _ - _ = _
  rw [← TrimmedSlice.finiteLaw_weight _ _ _ (by positivity)
    (by have := safe_clearance security; simp only [abs_zero]; omega)]
  rfl

theorem approximateCenterProfile_bounds (security bits : ℕ) (output : FirstHistogram.Palette security) :
    (safeLaw security).weight output / 2 ≤ approximateCenterProfile security bits output ∧
      approximateCenterProfile security bits output ≤
        (1 + (compensationApprox security bits : ℝ)) * (safeLaw security).weight output := by
  have hc := compensationApprox_nonneg security bits
  have hanchor := (approximateAnchorPrimaryLaw security bits).nonneg output
  constructor
  · by_cases hsafe : InwardAnchor.SafeColor security output
    · have hcost := mul_le_mul_of_nonneg_left (approximateAnchorPrimaryLaw_height security bits output) hc
      rw [mul_one_div] at hcost
      have hcost' := compensationApprox_anchor_cost security bits
      unfold approximateCenterProfile
      rw [safeLaw_weight, if_pos hsafe]
      nlinarith only [hcost, hcost', mul_nonneg hc (safeHeight_pos security).le]
    · unfold approximateCenterProfile
      rw [safeLaw_weight, if_neg hsafe, approximateAnchorPrimaryLaw_zero_outside security bits output hsafe]
      simp
  · unfold approximateCenterProfile
    exact sub_le_self _ (mul_nonneg hc hanchor)

theorem center_mass (security bits : ℕ) :
    (∑ output : FirstHistogram.Palette security, center security bits output.val) = 1 := by
  have hm : (∑ output : FirstHistogram.Palette security, (center security bits output.val : ℝ)) = 1 := by
    simp_rw [center_cast]
    simp only [approximateCenterProfile, Finset.sum_sub_distrib, ← Finset.mul_sum, FiniteDist.sum_one, mul_one]
    ring
  exact_mod_cast hm

theorem center_nonneg (security bits : ℕ) (output : FirstHistogram.Palette security) :
    0 ≤ center security bits output.val := by
  have h := (div_nonneg ((safeLaw security).nonneg output) (by norm_num : (0 : ℝ) ≤ 2)).trans
    (approximateCenterProfile_bounds security bits output).1
  rw [← center_cast] at h
  exact_mod_cast h

theorem center_zero_outside (security bits : ℕ) (output : FirstHistogram.Palette security)
    (hunsafe : ¬InwardAnchor.SafeColor security output) : center security bits output.val = 0 := by
  have h : (center security bits output.val : ℝ) = 0 := by
    rw [center_cast]
    unfold approximateCenterProfile
    rw [safeLaw_weight, if_neg hunsafe, approximateAnchorPrimaryLaw_zero_outside security bits output hunsafe]
    ring
  exact_mod_cast h

theorem center_lower_safe (security bits : ℕ) (output : ActualControls.SafePalette security) :
    1 / (2 * (Parameters.modulus security : ℝ)) ≤ (center security bits output.val.val : ℝ) := by
  rw [center_cast]
  apply le_trans _ (approximateCenterProfile_bounds security bits output.val).1
  rw [safeLaw_weight, if_pos output.property]
  have hsafe : 1 / (Parameters.modulus security : ℝ) ≤ safeHeight security := by
    unfold safeHeight
    apply one_div_le_one_div_of_le
    · have h := Nat.cast_lt (α := ℝ).mpr (safe_clearance security)
      push_cast at h
      linarith
    · have hM : (0 : ℝ) ≤ Parameters.safeMargin security := Nat.cast_nonneg _
      linarith
  convert div_le_div_of_nonneg_right hsafe (by norm_num : (0 : ℝ) ≤ 2) using 1; ring

def approximateCenterLaw (security bits : ℕ) : FiniteDist (FirstHistogram.Palette security) where
  weight output := center security bits output.val
  nonneg output := by exact_mod_cast center_nonneg security bits output
  sum_one := by exact_mod_cast center_mass security bits

def approximateBodyReference (security bits : ℕ) : FiniteDist (ActualControls.SafePalette security) :=
  ActualControls.supportedLaw (approximateCenterLaw security bits) (InwardAnchor.SafeColor security)
    (fun output hunsafe => by
      change (center security bits output.val : ℝ) = 0
      exact_mod_cast center_zero_outside security bits output hunsafe)

def approximateAnchorReference (security bits : ℕ) (primary : FirstHistogram.Palette security) :
    FiniteDist (ActualControls.SafePalette security) :=
  ActualControls.supportedLaw (approximateAnchorLaw security bits primary) (InwardAnchor.SafeColor security)
    (fun output hunsafe => by rw [← anchor_cast, anchor_zero_outside security bits primary output hunsafe, Rat.cast_zero])

theorem compensationApprox_error (security bits : ℕ) :
    |(compensationApprox security bits : ℝ) - compensation security| ≤ (1 / (2 : ℝ)^bits) / 2 := by
  have hfree := freeMass_pos security
  have hLfree : (Parameters.legCount security : ℝ) ≤ freeMass security := by
    have hp := Nat.cast_le (α := ℝ).mpr (population_room security)
    push_cast at hp
    unfold freeMass
    linarith
  have hratio : (Parameters.legCount security : ℝ) / freeMass security ≤ 1 := (div_le_one hfree).mpr hLfree
  rw [compensationApprox_cast]
  unfold compensation markMass
  have hrewrite : (Parameters.legCount security : ℝ) * LocalPairProgram.activationApprox security bits / freeMass security -
      (Parameters.legCount security : ℝ) * DiffuseProfiles.activation security / freeMass security =
      ((Parameters.legCount security : ℝ) / freeMass security) *
        ((LocalPairProgram.activationApprox security bits : ℝ) - DiffuseProfiles.activation security) := by ring
  rw [hrewrite, abs_mul, abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hfree.le)]
  calc
    _ ≤ ((Parameters.legCount security : ℝ) / freeMass security) *
        ((1 / 2 : ℝ) * (1 / (2 : ℝ)^bits)) :=
      mul_le_mul_of_nonneg_left (LocalPairProgram.activationApprox_error security bits)
        (div_nonneg (Nat.cast_nonneg _) hfree.le)
    _ ≤ 1 * ((1 / 2 : ℝ) * (1 / (2 : ℝ)^bits)) := mul_le_mul_of_nonneg_right hratio (by positivity)
    _ = _ := by ring

theorem anchorPrimary_error (security bits : ℕ) (output : FirstHistogram.Palette security)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) :
    |(anchorPrimary security bits output.val : ℝ) - (anchorPrimaryLaw security).weight output| ≤
      (Parameters.modulus security : ℝ) *
        (64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits)) +
          1 / (2 : ℝ)^bits := by
  let epsilon : ℝ := 1 / (2 : ℝ)^bits
  let error : ℝ := 64 * (Parameters.base security : ℝ) * Parameters.dimension security * epsilon
  have hpoint (color : FirstHistogram.Palette security) :
      |(approximatePrimaryLaw security bits).weight color * (approximateAnchorLaw security bits color).weight output -
        (primaryLaw security).weight color * (InwardAnchor.smoothedAnchorLaw security color).weight output| ≤
          error + (primaryLaw security).weight color * epsilon := by
    have hp : |(approximatePrimaryLaw security bits).weight color - (primaryLaw security).weight color| ≤ error :=
      primary_error security bits color hprecision hbudget
    have hk : |(approximateAnchorLaw security bits color).weight output -
        (InwardAnchor.smoothedAnchorLaw security color).weight output| ≤ epsilon := by
      rw [← anchor_cast]
      exact anchor_error security bits color output
    calc
      _ = |((approximatePrimaryLaw security bits).weight color - (primaryLaw security).weight color) *
          (approximateAnchorLaw security bits color).weight output +
          (primaryLaw security).weight color * ((approximateAnchorLaw security bits color).weight output -
            (InwardAnchor.smoothedAnchorLaw security color).weight output)| := by congr 1; ring
      _ ≤ |(approximatePrimaryLaw security bits).weight color - (primaryLaw security).weight color| *
          (approximateAnchorLaw security bits color).weight output +
          (primaryLaw security).weight color * |(approximateAnchorLaw security bits color).weight output -
            (InwardAnchor.smoothedAnchorLaw security color).weight output| := by
        simpa only [abs_mul, abs_of_nonneg (FiniteDist.nonneg _ _)] using abs_add_le
          (((approximatePrimaryLaw security bits).weight color - (primaryLaw security).weight color) *
            (approximateAnchorLaw security bits color).weight output)
          ((primaryLaw security).weight color * ((approximateAnchorLaw security bits color).weight output -
            (InwardAnchor.smoothedAnchorLaw security color).weight output))
      _ ≤ error * 1 + (primaryLaw security).weight color * epsilon :=
        add_le_add (mul_le_mul hp ((approximateAnchorLaw security bits color).atom_le_one output)
          (FiniteDist.nonneg _ _) (by dsimp only [error, epsilon]; positivity))
          (mul_le_mul_of_nonneg_left hk ((primaryLaw security).nonneg color))
      _ = _ := by ring
  rw [anchorPrimary_cast]
  change |(∑ color, (approximatePrimaryLaw security bits).weight color *
    (approximateAnchorLaw security bits color).weight output) -
    ∑ color, (primaryLaw security).weight color * (InwardAnchor.smoothedAnchorLaw security color).weight output| ≤ _
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ color, (error + (primaryLaw security).weight color * epsilon) :=
      Finset.sum_le_sum (fun color _ => hpoint color)
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, ← Finset.sum_mul, FiniteDist.sum_one, one_mul]
      rfl

theorem center_error (security bits : ℕ) (output : FirstHistogram.Palette security)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) :
    |(center security bits output.val : ℝ) - centerProfile security output| ≤
      (64 * (Parameters.base security : ℝ) * Parameters.dimension security * Parameters.modulus security + 2) *
        (1 / (2 : ℝ)^bits) := by
  have hcomp := compensationApprox_error security bits
  have hanchor := anchorPrimary_error security bits output hprecision hbudget
  rw [anchorPrimary_cast] at hanchor
  have hgap : |(safeLaw security).weight output - (anchorPrimaryLaw security).weight output| ≤ 2 := by
    exact (abs_sub _ _).trans (by
      rw [abs_of_nonneg ((safeLaw security).nonneg output),
        abs_of_nonneg ((anchorPrimaryLaw security).nonneg output)]
      linarith [(safeLaw security).atom_le_one output, (anchorPrimaryLaw security).atom_le_one output])
  rw [center_cast]
  have hdecompose : approximateCenterProfile security bits output - centerProfile security output =
      ((compensationApprox security bits : ℝ) - compensation security) *
        ((safeLaw security).weight output - (anchorPrimaryLaw security).weight output) -
      (compensationApprox security bits : ℝ) *
        ((approximateAnchorPrimaryLaw security bits).weight output - (anchorPrimaryLaw security).weight output) := by
    unfold approximateCenterProfile centerProfile
    ring
  rw [hdecompose]
  calc
    _ ≤ |(compensationApprox security bits : ℝ) - compensation security| *
        |(safeLaw security).weight output - (anchorPrimaryLaw security).weight output| +
      (compensationApprox security bits : ℝ) *
        |(approximateAnchorPrimaryLaw security bits).weight output - (anchorPrimaryLaw security).weight output| := by
      simpa only [abs_mul, abs_of_nonneg (compensationApprox_nonneg security bits)] using abs_sub
        (((compensationApprox security bits : ℝ) - compensation security) *
          ((safeLaw security).weight output - (anchorPrimaryLaw security).weight output))
        ((compensationApprox security bits : ℝ) *
          ((approximateAnchorPrimaryLaw security bits).weight output - (anchorPrimaryLaw security).weight output))
    _ ≤ ((1 / (2 : ℝ)^bits) / 2) * 2 + 1 *
        ((Parameters.modulus security : ℝ) *
          (64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits)) +
          1 / (2 : ℝ)^bits) :=
      add_le_add (mul_le_mul hcomp hgap (abs_nonneg _) (by positivity))
        (mul_le_mul (compensationApprox_le_one security bits) hanchor (abs_nonneg _) (by positivity))
    _ = _ := by ring

theorem anchorReference_error (security bits : ℕ) (primary : FirstHistogram.Palette security)
    (output : ActualControls.SafePalette security) :
    |(approximateAnchorReference security bits primary).weight output -
      (ActualControls.anchorReference security primary).weight output| ≤ 1 / (2 : ℝ)^bits := by
  change |(approximateAnchorLaw security bits primary).weight output.val -
    (InwardAnchor.smoothedAnchorLaw security primary).weight output.val| ≤ _
  rw [← anchor_cast]
  exact anchor_error security bits primary output.val

theorem bodyReference_error (security bits : ℕ) (output : ActualControls.SafePalette security)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) :
    |(approximateBodyReference security bits).weight output - (ActualControls.bodyReference security).weight output| ≤
      (64 * (Parameters.base security : ℝ) * Parameters.dimension security * Parameters.modulus security + 2) *
        (1 / (2 : ℝ)^bits) :=
  center_error security bits output.val hprecision hbudget

theorem bodyReference_lower (security bits : ℕ) (output : ActualControls.SafePalette security) :
    1 / (2 * (Parameters.modulus security : ℝ)) ≤ (approximateBodyReference security bits).weight output :=
  center_lower_safe security bits output

end
end CurrentAFT.RationalProposalProgram
