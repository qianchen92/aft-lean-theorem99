import CurrentAFT.RootTaggedSelectedChannel
import CurrentAFT.RootReferenceExpectation
import CurrentAFT.IndependentReferenceEnergy

/-! # The zero-tag selected primary channel is its independent-root response

Both actual modular roots are averaged before applying the same finite
normalization. This is an equality of coefficient families, not merely an
equality after polynomial evaluation.
-/
namespace CurrentAFT.RootSelectedZeroTag
open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion FirstHistogram
  LocalReferenceEnergy PairedReferenceEnergy FixedPairedFirst IndependentPairedReference
  RootTaggedSelected RootTaggedSelectedChannel RootReferenceExpectation
  ControlCoordinates ControlProduct GradedControlAlgebra GradedControlNorm GradedControlStability
  LocalCoefficientFamily LocalRaisingLinear LocalRaisingFirst LocalRaisingBounds CoefficientHilbert
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw rootReference
abbrev Palette (security : ℕ) := ActualControls.Palette security

theorem pairedMassAt_periodic (security : ℕ) (firstComp secondComp firstAttach secondAttach : ℤ)
    (hcomp : (firstComp : Root security) = (secondComp : Root security))
    (hattach : (firstAttach : Root security) = (secondAttach : Root security))
    (scalar : FirstHistogram.Scalar security) (score : Palette security → ℝ) :
    pairedMassAt security firstComp firstAttach scalar score =
      pairedMassAt security secondComp secondAttach scalar score := by
  have hc := RootBackgroundPolynomial.shiftEquiv_eq_of_cast security firstComp secondComp hcomp
  have ha : attachmentAt security firstAttach scalar = attachmentAt security secondAttach scalar := by
    unfold attachmentAt
    rw [RootBackgroundPolynomial.shiftEquiv_eq_of_cast security (firstAttach + scalar.val) (secondAttach + scalar.val)
      (by simp only [Int.cast_add, hattach])]
  funext word
  simp only [pairedMassAt_control_sum, hc, ha]

theorem mass_zeroTag (security : ℕ) (score : Palette security → ℝ) :
    mass security (liftZero security score) = independentSignedMass security score := by
  funext word
  rw [IndependentReferenceEnergy.independentSigned_mixture]
  rw [mass_eq_joint]
  change (sourceLaw security).expectation (fun sample => pairedMassAt security
    (sample.1.1.val : ℤ) (sample.1.2.val : ℤ) sample.2 score word) = _
  unfold sourceLaw rootsLaw IndependentReferenceEnergy.rootLaw
  rw [FiniteDist.expectation_prod, FiniteDist.expectation_comm]
  rw [FiniteDist.expectation_prod]
  apply congrArg (scalarLaw security).expectation
  funext scalar
  rw [FiniteDist.expectation_prod]
  calc
    _ = (actualSeedLaw security).expectation (fun comp =>
        (rootReference security).expectation (fun attach => pairedMassAt security
          (actualBlur security comp) (attach.val : ℤ) scalar score word)) := by
      apply rootReference_seed_expectation security (fun comp : ℤ =>
        (rootReference security).expectation (fun attach => pairedMassAt security comp (attach.val : ℤ) scalar score word))
      intro first second hequal
      apply congrArg (rootReference security).expectation
      funext attach
      exact congrFun (pairedMassAt_periodic security first second (attach.val : ℤ) (attach.val : ℤ)
        hequal rfl scalar score) word
    _ = _ := by
      rw [FiniteDist.expectation_prod]
      apply congrArg (actualSeedLaw security).expectation
      funext comp
      apply rootReference_seed_expectation security (fun attach : ℤ => pairedMassAt security (actualBlur security comp) attach scalar score word)
      intro first second hequal
      exact congrFun (pairedMassAt_periodic security (actualBlur security comp) (actualBlur security comp)
        first second rfl hequal scalar score) word

theorem normalizedResponse_zeroTag (security order : ℕ) (score : Palette security → ℝ) :
    normalizedResponse security order (liftZero security score) =
      NormalizedLocalPolynomial.independentNormalized security order score := by
  unfold normalizedResponse NormalizedLocalPolynomial.independentNormalized
  rw [mass_zeroTag]

theorem zeroChannel_eq (security order : ℕ) (score : Palette security → ℝ) :
    zeroChannel security order score = NormalizedLocalPolynomial.independentNormalized security order
      (centerLinear (primaryLaw security) score) := by
  change normalizedResponse security order
    (RootTaggedSelectedChannel.controlCenterLinear security
      (RootTaggedSelectedChannel.curryLinear security (zeroLiftLinear security score))) = _
  exact normalizedResponse_zeroTag security order (centerLinear (primaryLaw security) score)

theorem zeroChannel_eq_leading_add_raised (security order : ℕ) (horder : 1 ≤ order)
    (score : Palette security → ℝ) :
    zeroChannel security order score = RaisingChannels.primaryLeading security order horder score +
      RaisingChannels.primaryRaised security order horder score := by
  rw [zeroChannel_eq]
  change _ = _ + (NormalizedLocalPolynomial.independentNormalized security order
    (centerLinear (primaryLaw security) score) - _)
  unfold RaisingChannels.primaryLeading
  simp only [LinearMap.comp_apply]
  abel

private theorem primaryFactor_nonneg (security : ℕ) : 0 ≤ BackgroundRates.primaryFactor security :=
  (RaisingPatternBudget.primaryFactor_pos security).le

private theorem bodyFactor_nonneg (security : ℕ) : 0 ≤ BackgroundRates.bodyFactor security :=
  (RaisingPatternBudget.bodyFactor_pos security).le

theorem zeroChannel_norm_sharp (security order : ℕ) (horder : 1 ≤ order)
    (hlarge : 2 * positiveConstant ≤ (Parameters.base security : ℝ))
    (hsmall : raisingConstant ≤ (Parameters.base security : ℝ)^38)
    (score : Palette security → ℝ) :
    coefficientNorm security order (zeroChannel security order score) ≤
      (2 * BackgroundRates.primaryFactor security) * Real.sqrt ((primaryLaw security).l2Sq score) := by
  rw [zeroChannel_eq_leading_add_raised security order horder]
  apply (familyNorm_add_le _ _ order _ _ (primaryFactor_nonneg security) (bodyFactor_nonneg security) _ _).trans
  have hcost : raisingConstant / (Parameters.base security : ℝ)^102 ≤ BackgroundRates.primaryFactor security := by
    rw [BackgroundRates.primaryFactor_eq]
    apply (div_le_iff₀ (pow_pos (FirstResponse.base_pos security) _)).mpr
    convert hsmall using 1
    field_simp [(FirstResponse.base_pos security).ne']
  calc
    _ ≤ BackgroundRates.primaryFactor security * Real.sqrt ((primaryLaw security).l2Sq score) +
        (raisingConstant / (Parameters.base security : ℝ)^102) * Real.sqrt ((primaryLaw security).l2Sq score) :=
      add_le_add (RaisingChannels.primaryLeading_norm security order horder score)
        (RaisingChannels.primaryRaised_norm security order horder hlarge score)
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hcost (Real.sqrt_nonneg ((primaryLaw security).l2Sq score))]

end
end CurrentAFT.RootSelectedZeroTag
