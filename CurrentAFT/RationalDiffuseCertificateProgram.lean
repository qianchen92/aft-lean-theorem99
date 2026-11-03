import CurrentAFT.RationalDiffuseResidualProgram
import CurrentAFT.RationalBackgroundDensities

/-! # The original safe diffuse-pair body certificate, evaluated rationally -/
namespace CurrentAFT.RationalDiffuseCertificateProgram
open AFT GaussianSource RationalNumerics DiffuseProfiles ProposalPrimary ActualControls
  DiffusePair DiffusePairBounds RationalDiffuseResidualProgram
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff Parameters.safeMargin
  PublicParameterProgram.modulus primaryLaw centerLaw

theorem ideal_pair_bound (security : ℕ) (scalar : ℤ) (first second : Palette security) :
    |pairProfile security scalar first second| ≤ 1 := by
  change |(pairSeedLaw security).expectation (pairTest security scalar first second)| ≤ 1
  exact CalibrationCoordinateError.expectation_abs_bound _ _ _ (pairTest_bound security scalar first second)

theorem ideal_seed_bound (security : ℕ) (scalar : ℤ) (first second : Palette security) :
    |safePairProfile security scalar first second| ≤ pairBound security := by
  unfold safePairProfile SafePair.coreSeed
  have hm (left right : Palette security) : |SafePair.restrictPair (safeCore security) (pairProfile security scalar) left right| ≤ 1 := by
    simp only [SafePair.restrictPair]
    split_ifs
    · exact ideal_pair_bound security scalar left right
    · norm_num
  simpa only [Fintype.card_fin, mul_one, pairBound] using
    canonicalPair_bound (uniformFiniteProfile (safeCore security)) _ 1 (by norm_num)
      (uniformFiniteProfile_abs_le_one _) hm first second

theorem center_bound (security bits : ℕ) (color : Palette security) :
    |(RationalProposalProgram.center security bits color.val : ℝ)| ≤ 1 := by
  change |(RationalProposalProgram.approximateCenterLaw security bits).weight color| ≤ 1
  rw [abs_of_nonneg ((RationalProposalProgram.approximateCenterLaw security bits).nonneg color)]
  exact (RationalProposalProgram.approximateCenterLaw security bits).atom_le_one color

def bodyErrorConstant (security : ℕ) : ℝ :=
  2 * pairBound security * (4 * (Parameters.modulus security : ℝ)^2) +
    pairBound security * (2 * RationalBackgroundDensities.centerErrorConstant security) *
      (4 * (Parameters.modulus security : ℝ)^2)^2

theorem bodyDensity_error (security bits : ℕ) (scalar : ℤ) (first second : SafePalette security)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) :
    |(bodyDensity security bits scalar first.val.val second.val.val : ℝ) - bodyPairDensity security scalar first second| ≤
      bodyErrorConstant security * (1 / (2 : ℝ)^bits) := by
  let q : ℝ := Parameters.modulus security
  let epsilon : ℝ := 1 / (2 : ℝ)^bits
  let B := pairBound security
  let C := RationalBackgroundDensities.centerErrorConstant security
  let lower : ℝ := 1 / (4 * q^2)
  have hq : 0 < q := FirstResponse.modulus_pos security
  have hB : 0 ≤ B := by unfold B pairBound; positivity
  have hC : 0 ≤ C := by unfold C RationalBackgroundDensities.centerErrorConstant; positivity
  have he : 0 ≤ epsilon := by positivity
  have hqcenter (color : SafePalette security) :
      |(RationalProposalProgram.center security bits color.val.val : ℝ) - (bodyReference security).weight color| ≤ C * epsilon := by
    simpa only [C, epsilon, bodyReference, supportedLaw, centerLaw, RationalBackgroundDensities.centerErrorConstant] using
      RationalProposalProgram.center_error security bits color.val hprecision hbudget
  have hactual (color : SafePalette security) : |(bodyReference security).weight color| ≤ 1 := by
    rw [abs_of_nonneg ((bodyReference security).nonneg color)]
    exact (bodyReference security).atom_le_one color
  have hd : |(RationalProposalProgram.center security bits first.val.val : ℝ) *
      (RationalProposalProgram.center security bits second.val.val : ℝ) -
      (bodyReference security).weight first * (bodyReference security).weight second| ≤ 2 * C * epsilon := by
    calc
      _ = |((RationalProposalProgram.center security bits first.val.val : ℝ) - (bodyReference security).weight first) *
          (RationalProposalProgram.center security bits second.val.val : ℝ) + (bodyReference security).weight first *
          ((RationalProposalProgram.center security bits second.val.val : ℝ) - (bodyReference security).weight second)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
      _ ≤ (C * epsilon) * 1 + 1 * (C * epsilon) := by
        simp only [abs_mul]
        exact add_le_add (mul_le_mul (hqcenter first) (center_bound security bits second.val) (abs_nonneg _) (by positivity))
          (mul_le_mul (hactual first) (hqcenter second) (abs_nonneg _) (by norm_num))
      _ = _ := by ring
  have hlowQ : lower ≤ (RationalProposalProgram.center security bits first.val.val : ℝ) *
      (RationalProposalProgram.center security bits second.val.val : ℝ) := by
    calc
      _ = (1 / (2*q)) * (1 / (2*q)) := by dsimp only [lower]; field_simp; ring
      _ ≤ _ := mul_le_mul (RationalProposalProgram.center_lower_safe security bits first)
        (RationalProposalProgram.center_lower_safe security bits second) (by positivity)
        ((by positivity : (0 : ℝ) ≤ 1 / (2*q)).trans (RationalProposalProgram.center_lower_safe security bits first))
  have hlow : lower ≤ (bodyReference security).weight first * (bodyReference security).weight second := by
    calc
      _ = (1 / (2*q)) * (1 / (2*q)) := by dsimp only [lower]; field_simp; ring
      _ ≤ _ := mul_le_mul (bodyReference_lower security first) (bodyReference_lower security second)
        (by positivity) ((bodyReference security).nonneg first)
  have h := RationalDensityInverseProgram.quotient_error
    (seed security bits scalar first.val.val second.val.val : ℝ) (safePairProfile security scalar first.val second.val)
    ((RationalProposalProgram.center security bits first.val.val : ℝ) * (RationalProposalProgram.center security bits second.val.val : ℝ))
    ((bodyReference security).weight first * (bodyReference security).weight second)
    lower (2 * B * epsilon) (2 * C * epsilon) B (by dsimp only [lower]; positivity) hlowQ hlow
    (by positivity) (by positivity) hB (seed_error security bits scalar first.val second.val) hd
    (ideal_seed_bound security scalar first.val second.val)
  rw [bodyDensity, Rat.cast_div, Rat.cast_mul, bodyPairDensity]
  exact h.trans_eq (by unfold bodyErrorConstant; dsimp only [lower, q, B, C, epsilon]; ring_nf; simp only [inv_inv])

end
end CurrentAFT.RationalDiffuseCertificateProgram
