import CurrentAFT.MarkedPairCertificates
import CurrentAFT.LocalReferenceEnergy

/-! Exact leading mass of the fixed-scalar marked mixed certificate. -/

namespace CurrentAFT.MarkedPairLeading

open AFT AFT.SafePair DiffuseProfiles ProposalPrimary ActualControls FirstResponse FringeCertificate
  BackgroundCertificates BackgroundTranslations MarkedPairSeed MarkedPairCertificates
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw ProposalPrimary.centerLaw
  ActualControls.bodyReference InwardAnchor.shiftedAnchorLaw DiffuseProfiles.actualSeedLaw

def paletteAnchor (security : ℕ) (scalar : MarkedPairSeed.Scalar security) (primary : ActualControls.Palette security) :
    FiniteDist (ActualControls.Palette security) :=
  InwardAnchor.shiftedAnchorLaw security primary (-scalar.val)
    (by simpa only [abs_neg] using InwardAnchor.scalar_bound security scalar)

def anchorMean (security : ℕ) (scalar : MarkedPairSeed.Scalar security) : FiniteDist (ActualControls.Palette security) :=
  (primaryLaw security).mix (paletteAnchor security scalar)

def seedProfile (security : ℕ) (scalar : MarkedPairSeed.Scalar security)
    (primary center : ActualControls.Palette security) : ℝ :=
  (primaryLaw security).weight primary * (paletteAnchor security scalar primary).weight center -
    uniformProfile security primary * (anchorMean security scalar).weight center -
    (primaryLaw security).weight primary * (centerLaw security).weight center +
    uniformProfile security primary * (centerLaw security).weight center

theorem secondMean_formula (security : ℕ) (scalar : MarkedPairSeed.Scalar security) (center : SafePalette security) :
    MarkedPairSeed.secondMean security scalar center =
      (anchorMean security scalar).weight center.val / (bodyReference security).weight center - 1 := by
  unfold MarkedPairSeed.secondMean FiniteDist.expectation MarkedPairSeed.secondCentered MarkedPairSeed.rawDensity
  simp only [mul_sub, ← mul_div_assoc, Finset.sum_sub_distrib, ← Finset.sum_div, mul_one, FiniteDist.sum_one]
  rfl

theorem seedDensity_profile (security : ℕ) (scalar : MarkedPairSeed.Scalar security)
    (primary : ActualControls.Palette security) (center : SafePalette security) :
    (primaryLaw security).weight primary * (bodyReference security).weight center * seedDensity security scalar primary center =
      seedProfile security scalar primary center.val := by
  rw [seedDensity, secondMean_formula]
  unfold MarkedPairSeed.secondCentered MarkedPairSeed.rawDensity MarkedPairSeed.uniformRelative seedProfile
  have hanchor : (fixedAnchor security scalar primary).weight center = (paletteAnchor security scalar primary).weight center.val := rfl
  have hbody : (bodyReference security).weight center = (centerLaw security).weight center.val := by
    simp only [bodyReference, supportedLaw]
  rw [hanchor, ← hbody]
  field_simp [(primaryReference_positive security primary).ne', (bodyReference_positive security center).ne']
  ring

theorem seedProfile_zero_outside (security : ℕ) (scalar : MarkedPairSeed.Scalar security)
    (primary center : ActualControls.Palette security) (hunsafe : ¬InwardAnchor.SafeColor security center) :
    seedProfile security scalar primary center = 0 := by
  have hanchor (color : ActualControls.Palette security) :
      (paletteAnchor security scalar color).weight center = 0 :=
    InwardAnchor.shiftedAnchorLaw_zero_outside security color _ _ center hunsafe
  have hmean : (anchorMean security scalar).weight center = 0 := by
    simp only [anchorMean, FiniteDist.mix_weight, hanchor, mul_zero, Finset.sum_const_zero]
  have hbody : (centerLaw security).weight center = 0 := by
    simp only [centerLaw]
    exact centerProfile_zero_outside security center hunsafe
  simp only [seedProfile, hanchor, hmean, hbody, mul_zero, sub_self, add_zero]

def bodyConvolution (security : ℕ) : Module.End ℝ (ActualControls.Palette security → ℝ) where
  toFun := rootConvolutionProfile security
  map_add' first second := by
    funext output
    simp only [rootConvolutionProfile, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' scalar profile := by
    funext output
    simp only [rootConvolutionProfile, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro seed _
    ring

theorem bodyConvolution_mass (security : ℕ) (profile : ActualControls.Palette security → ℝ) :
    (∑ output, bodyConvolution security profile output) = ∑ color, profile color :=
  rootConvolutionProfile_mass security profile

theorem bodyConvolution_uniform (security : ℕ) :
    bodyConvolution security (uniformProfile security) = uniformProfile security := by
  funext output
  simp only [bodyConvolution, LinearMap.coe_mk, AddHom.coe_mk, rootConvolutionProfile, uniformProfile,
    ← Finset.sum_mul, FiniteDist.sum_one, one_mul]

theorem markedCompanionAt_convolution (security : ℕ) (scalar : MarkedPairSeed.Scalar security)
    (primary output : ActualControls.Palette security) :
    (LocalReferenceEnergy.markedCompanionAt security primary scalar).weight output =
      bodyConvolution security (paletteAnchor security scalar primary).weight output := by
  unfold LocalReferenceEnergy.markedCompanionAt LocalReferenceEnergy.publicBlurLaw
  simp only [FiniteDist.mix_weight, FiniteDist.map_equiv_weight]
  change ((edgeLaw security).prod (edgeLaw security)).expectation
    (fun edge => (paletteAnchor security scalar primary).weight
      ((shiftEquiv security (edge.1.val - edge.2.val)).symm output)) = _
  unfold bodyConvolution
  change _ = (actualSeedLaw security).expectation (fun seed =>
    (paletteAnchor security scalar primary).weight ((shiftEquiv security (actualBlur security seed)).symm output))
  simp only [actualSeedLaw, FiniteDist.expectation_prod, actualBlur, FiniteDist.expectation_const]

theorem inverseDensity_stored_leading (security : ℕ) (scalar : MarkedPairSeed.Scalar security)
    (primary : ActualControls.Palette security) (center : SafePalette security) :
    (primaryLaw security).weight primary * (bodyReference security).weight center *
      PrimaryTensorInverse.densityResponse security (fun color => inverseDensity security scalar color center) primary =
        seedProfile security scalar primary center.val := by
  rw [inverseDensity_primary_response]
  exact seedDensity_profile security scalar primary center

def mixedSeedProfile {Color : Type*} [Fintype Color]
    (primary body uniform : FiniteDist Color) (anchor : Color → FiniteDist Color) (first second : Color) : ℝ :=
  primary.weight first * (anchor first).weight second - uniform.weight first * (primary.mix anchor).weight second -
    primary.weight first * body.weight second + uniform.weight first * body.weight second

theorem mixedSeedProfile_convolution {Color : Type*} [Fintype Color]
    (primary body uniform : FiniteDist Color) (anchor : Color → FiniteDist Color)
    (operator : Module.End ℝ (Color → ℝ))
    (hmass : ∀ profile, (∑ color, operator profile color) = ∑ color, profile color) :
    canonicalPair uniform.weight (fun first second => primary.weight first * operator (anchor first).weight second) =
      fun first second => operator (mixedSeedProfile primary body uniform anchor first) second +
        (primary.weight first - uniform.weight first) * (operator body.weight second - uniform.weight second) := by
  have hrow (first : Color) : (∑ second, primary.weight first * operator (anchor first).weight second) = primary.weight first := by
    rw [← Finset.mul_sum, hmass, FiniteDist.sum_one, mul_one]
  have hmean : (primary.mix anchor).weight = ∑ first, primary.weight first • (anchor first).weight := by
    funext second
    simp only [FiniteDist.mix_weight, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hcolumn (second : Color) : (∑ first, primary.weight first * operator (anchor first).weight second) =
      operator (primary.mix anchor).weight second := by
    rw [hmean, map_sum]
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hseed (first : Color) : mixedSeedProfile primary body uniform anchor first =
      primary.weight first • (anchor first).weight - uniform.weight first • (primary.mix anchor).weight -
        primary.weight first • body.weight + uniform.weight first • body.weight := by
    funext second
    rfl
  funext first second
  simp only [canonicalPair, hrow, hcolumn, FiniteDist.sum_one, one_mul]
  rw [hseed, map_add, map_sub, map_sub, map_smul, map_smul, map_smul, map_smul]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem marked_pair_canonical_decomposition (security : ℕ) (scalar : MarkedPairSeed.Scalar security) :
    canonicalPair (uniformProfile security) (fun primary output =>
      (primaryLaw security).weight primary * (LocalReferenceEnergy.markedCompanionAt security primary scalar).weight output) =
      fun primary output => bodyConvolution security (seedProfile security scalar primary) output +
        ((primaryLaw security).weight primary - uniformProfile security primary) *
          ((convolvedCenterLaw security).weight output - uniformProfile security output) := by
  let uniform : FiniteDist (ActualControls.Palette security) := FiniteDist.uniform _
  have huniform : uniform.weight = uniformProfile security := by
    funext color
    simp only [uniform, FiniteDist.uniform_weight, Fintype.card_fin, uniformProfile]
  have hseed (primary : ActualControls.Palette security) :
      mixedSeedProfile (primaryLaw security) (centerLaw security) uniform (paletteAnchor security scalar) primary =
        seedProfile security scalar primary := by
    funext center
    simp only [mixedSeedProfile, seedProfile, huniform, anchorMean]
  have hbody : bodyConvolution security (centerLaw security).weight = (convolvedCenterLaw security).weight := by
    funext output
    exact (convolvedCenterLaw_weight security output).symm
  have h := mixedSeedProfile_convolution (primaryLaw security) (centerLaw security) uniform (paletteAnchor security scalar)
    (bodyConvolution security) (bodyConvolution_mass security)
  simp only [huniform, hseed, hbody] at h
  simpa only [markedCompanionAt_convolution] using h

end

end CurrentAFT.MarkedPairLeading
