import CurrentAFT.PairQuadraticFamilies

/-! The quadratic certificates use the actual fixed-scalar primary-averaged pair law. -/

namespace CurrentAFT.ActualPairBridge

open AFT AFT.TrimmedSlice DiffuseProfiles ProposalPrimary ActualControls ProposalSymmetry
  FirstHistogram LocalReferenceEnergy DiffusePair
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff
  ProposalPrimary.primaryLaw DiffuseProfiles.edgeLaw LocalReferenceEnergy.diffusePairAt
  FirstHistogram.diffuseSeedPair ProposalSymmetry.directionLaw DiffusePair.pairProfile

theorem map_prod_expectation {Primary Coin Direction Blur : Type*}
    [Fintype Primary] [Fintype Coin] [Fintype Direction] [Fintype Blur]
    (primary : FiniteDist Primary) (coin : FiniteDist Coin) (blur : FiniteDist Blur)
    (direction : Primary × Coin → Direction) (kernel : Direction → Blur → ℝ) :
    (((primary.prod coin).map direction).prod blur).expectation (fun seed => kernel seed.1 seed.2) =
      primary.expectation (fun color => coin.expectation (fun bit => blur.expectation (kernel (direction (color, bit))))) := by
  rw [FiniteDist.expectation_prod, FiniteDist.expectation_map, FiniteDist.expectation_prod]
  rfl

theorem signedDiffusePair_eq_actual (security : ℕ) (scalar : LocalReferenceEnergy.Scalar security)
    (first second : ActualControls.Palette security) :
    signedDiffusePair security scalar (fun _ => 1) first second = pairProfile security scalar.val first second := by
  have h := map_prod_expectation (primaryLaw security) (FiniteDist.uniform Bool)
    ((edgeLaw security).prod (edgeLaw security))
    (fun point => InwardAnchor.positiveDirection security point.1 point.2)
    (fun sign edge => averagedPair (Parameters.modulus security) 1
      (intervalStart sign (Parameters.anchorWidth security) (edge.1.val - edge.2.val)) scalar.val
        (Parameters.anchorWidth security) first second)
  have hleft : signedDiffusePair security scalar (fun _ => 1) first second =
      (primaryLaw security).expectation (fun color => (FiniteDist.uniform Bool).expectation (fun coin =>
        ((edgeLaw security).prod (edgeLaw security)).expectation (fun edge => averagedPair (Parameters.modulus security) 1
          (intervalStart (InwardAnchor.positiveDirection security color coin) (Parameters.anchorWidth security)
            (edge.1.val - edge.2.val)) scalar.val (Parameters.anchorWidth security) first second))) := by
    simp only [signedDiffusePair, mul_one, LocalReferenceEnergy.diffusePairAt, FiniteDist.mix_weight,
      diffuseSeedPair_weight, actualBlur, actualSecond, publicBlurLaw, FiniteDist.expectation]
  have hright : pairProfile security scalar.val first second =
      (((primaryLaw security).prod (FiniteDist.uniform Bool)).map
        (fun point => InwardAnchor.positiveDirection security point.1 point.2) |>.prod
          ((edgeLaw security).prod (edgeLaw security))).expectation (fun seed => averagedPair (Parameters.modulus security) 1
            (intervalStart seed.1 (Parameters.anchorWidth security) (seed.2.1.val - seed.2.2.val)) scalar.val
              (Parameters.anchorWidth security) first second) := by
    simp only [pairProfile, mixedPair, pairStart, pairBlur, pairSeedLaw, directionLaw, FiniteDist.expectation]
  exact hleft.trans (h.symm.trans hright.symm)

theorem signedPairAt_actual_decomposition (security : ℕ) (scalar : LocalReferenceEnergy.Scalar security)
    (first second : ActualControls.Palette security) :
    signedPairAt security scalar (fun _ => 1) first second =
      (1 - activation security) * pairProfile security scalar.val first second +
        activation security * (primaryLaw security).weight first * (markedCompanionAt security first scalar).weight second := by
  rw [signedPairAt_decomposition, signedDiffusePair_eq_actual]
  simp only [signedMarkedPair, mul_one]

end

end CurrentAFT.ActualPairBridge
