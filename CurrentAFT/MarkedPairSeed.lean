import CurrentAFT.PrimaryTensorInverse
import CurrentAFT.DiffusePairBounds
import AFT.MixtureTail

/-!
# The actual fixed-scalar marked mixed seed

The first coordinate is centered at the full uniform mass profile and the
safe second coordinate at the actual body law. The resulting mixed density
is canonical under the actual positive primary/body product reference.
-/

namespace CurrentAFT.MarkedPairSeed

open AFT DiffuseProfiles ProposalPrimary ActualControls FirstResponse FringeCertificate
  PrimaryTensorInverse
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff
  ProposalPrimary.primaryLaw ProposalPrimary.centerLaw ActualControls.bodyReference
  InwardAnchor.shiftedAnchorLaw

abbrev Scalar (security : ℕ) := GaussianSource.Window (Parameters.sourceCutoff security - 1)

def fixedAnchor (security : ℕ) (scalar : Scalar security) (primary : ActualControls.Palette security) :
    FiniteDist (SafePalette security) :=
  supportedLaw (InwardAnchor.shiftedAnchorLaw security primary (-scalar.val)
    (by simpa only [abs_neg] using InwardAnchor.scalar_bound security scalar))
      (InwardAnchor.SafeColor security)
      (InwardAnchor.shiftedAnchorLaw_zero_outside security primary _ _)

theorem fixedAnchor_height (security : ℕ) (scalar : Scalar security)
    (primary : ActualControls.Palette security) (center : SafePalette security) :
    (fixedAnchor security scalar primary).weight center ≤ 1 / (Parameters.anchorWidth security : ℝ) :=
  InwardAnchor.shiftedAnchorLaw_height security primary _ _ center.val

def rawDensity (security : ℕ) (scalar : Scalar security) (primary : ActualControls.Palette security)
    (center : SafePalette security) : ℝ :=
  (fixedAnchor security scalar primary).weight center / (bodyReference security).weight center

def secondCentered (security : ℕ) (scalar : Scalar security) (primary : ActualControls.Palette security)
    (center : SafePalette security) : ℝ := rawDensity security scalar primary center - 1

def secondMean (security : ℕ) (scalar : Scalar security) (center : SafePalette security) : ℝ :=
  (primaryLaw security).expectation (fun primary => secondCentered security scalar primary center)

def uniformRelative (security : ℕ) (primary : ActualControls.Palette security) : ℝ :=
  uniformProfile security primary / (primaryLaw security).weight primary

def seedDensity (security : ℕ) (scalar : Scalar security) (primary : ActualControls.Palette security)
    (center : SafePalette security) : ℝ :=
  secondCentered security scalar primary center - uniformRelative security primary * secondMean security scalar center

theorem rawDensity_mean (security : ℕ) (scalar : Scalar security) (primary : ActualControls.Palette security) :
    (bodyReference security).expectation (rawDensity security scalar primary) = 1 := by
  unfold FiniteDist.expectation rawDensity
  simp only [mul_div_cancel₀ _ (bodyReference_positive security _).ne']
  exact (fixedAnchor security scalar primary).sum_one

theorem secondCentered_mean (security : ℕ) (scalar : Scalar security) (primary : ActualControls.Palette security) :
    (bodyReference security).expectation (secondCentered security scalar primary) = 0 := by
  change (bodyReference security).expectation (fun center => rawDensity security scalar primary center - 1) = 0
  rw [FiniteDist.expectation_sub, rawDensity_mean, FiniteDist.expectation_const, sub_self]

theorem uniformRelative_mean (security : ℕ) : (primaryLaw security).expectation (uniformRelative security) = 1 := by
  have hq := (FirstResponse.modulus_pos security).ne'
  unfold FiniteDist.expectation uniformRelative
  simp only [mul_div_cancel₀ _ (primaryReference_positive security _).ne', uniformProfile,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

theorem uniformRelative_energy (security : ℕ) : (primaryLaw security).l2Sq (uniformRelative security) ≤ 2 := by
  have heq : (primaryLaw security).l2Sq (uniformRelative security) =
      profileSquareNorm (primaryLaw security).weight (uniformProfile security) := by
    exact densityScore_square _ _
  rw [heq]
  exact uniformProfile_square_le_two security

theorem seedDensity_centered_primary (security : ℕ) (scalar : Scalar security) (center : SafePalette security) :
    (primaryLaw security).expectation (fun primary => seedDensity security scalar primary center) = 0 := by
  simp only [FiniteDist.expectation, seedDensity, mul_sub, Finset.sum_sub_distrib,
    ← mul_assoc, ← Finset.sum_mul]
  change secondMean security scalar center - (primaryLaw security).expectation (uniformRelative security) *
    secondMean security scalar center = 0
  rw [uniformRelative_mean, one_mul, sub_self]

theorem secondMean_mean (security : ℕ) (scalar : Scalar security) :
    (bodyReference security).expectation (secondMean security scalar) = 0 := by
  change (bodyReference security).expectation (fun center =>
    (primaryLaw security).expectation (fun primary => secondCentered security scalar primary center)) = 0
  rw [FiniteDist.expectation_comm]
  simp only [secondCentered_mean, FiniteDist.expectation_const]

theorem seedDensity_centered_body (security : ℕ) (scalar : Scalar security) (primary : ActualControls.Palette security) :
    (bodyReference security).expectation (seedDensity security scalar primary) = 0 := by
  change (bodyReference security).expectation (fun center => secondCentered security scalar primary center -
    uniformRelative security primary * secondMean security scalar center) = 0
  rw [FiniteDist.expectation_sub, FiniteDist.expectation_const_mul, secondCentered_mean, secondMean_mean, mul_zero, sub_self]

theorem mismatch_center_energy {Color : Type*} [Fintype Color] (law : FiniteDist Color)
    (multiplier kernel : Color → ℝ) (hbound : law.l2Sq multiplier ≤ 2) :
    law.l2Sq (fun color => kernel color - multiplier color * law.expectation kernel) ≤ 6 * law.l2Sq kernel := by
  have hpoint (color : Color) : (kernel color - multiplier color * law.expectation kernel) ^ 2 ≤
      2 * kernel color ^ 2 + 2 * multiplier color ^ 2 * law.expectation kernel ^ 2 := by
    nlinarith [sq_nonneg (kernel color + multiplier color * law.expectation kernel)]
  have hsum : law.l2Sq (fun color => kernel color - multiplier color * law.expectation kernel) ≤
      2 * law.l2Sq kernel + 2 * law.l2Sq multiplier * law.expectation kernel ^ 2 := by
    unfold FiniteDist.l2Sq FiniteDist.expectation
    calc
      _ ≤ ∑ color, law.weight color *
          (2 * kernel color ^ 2 + 2 * multiplier color ^ 2 * (∑ point, law.weight point * kernel point) ^ 2) :=
        Finset.sum_le_sum fun color _ => mul_le_mul_of_nonneg_left (hpoint color) (law.nonneg color)
      _ = _ := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro color _
        ring
  have hmean := HistogramNormalization.expectation_square_le law kernel
  have hprod := mul_le_mul_of_nonneg_right hbound (sq_nonneg (law.expectation kernel))
  nlinarith

theorem rawDensity_energy (security : ℕ) (scalar : Scalar security) (primary : ActualControls.Palette security) :
    (bodyReference security).l2Sq (rawDensity security scalar primary) ≤
      2 * (Parameters.modulus security : ℝ) / Parameters.anchorWidth security := by
  have hq := FirstResponse.modulus_pos security
  have ha : (0 : ℝ) < Parameters.anchorWidth security := Nat.cast_pos.mpr (InwardAnchor.anchorWidth_pos security)
  have hratio (center : SafePalette security) : (fixedAnchor security scalar primary).weight center ≤
      (2 * (Parameters.modulus security : ℝ) / Parameters.anchorWidth security) * (bodyReference security).weight center := by
    calc
      _ ≤ 1 / (Parameters.anchorWidth security : ℝ) := fixedAnchor_height security scalar primary center
      _ = (2 * (Parameters.modulus security : ℝ) / Parameters.anchorWidth security) *
          (1 / (2 * (Parameters.modulus security : ℝ))) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (bodyReference_lower security center) (by positivity)
  have h := BlockDensity.profile_energy_le_ratio (bodyReference security).weight
    (fixedAnchor security scalar primary).weight (2 * (Parameters.modulus security : ℝ) / Parameters.anchorWidth security)
    (bodyReference_positive security) (fixedAnchor security scalar primary).nonneg hratio
  rw [FiniteDist.sum_one, mul_one] at h
  exact (densityScore_square _ _).le.trans h

theorem secondCentered_energy (security : ℕ) (scalar : Scalar security) (primary : ActualControls.Palette security) :
    (bodyReference security).l2Sq (secondCentered security scalar primary) ≤
      2 * (Parameters.modulus security : ℝ) / Parameters.anchorWidth security := by
  have hcenter : secondCentered security scalar primary =
      TensorChannel.center (bodyReference security) (rawDensity security scalar primary) := by
    funext center
    simp only [secondCentered, TensorChannel.center_apply, rawDensity_mean]
  rw [hcenter]
  exact (TensorChannel.center_energy_le _ _).trans (rawDensity_energy security scalar primary)

theorem seedDensity_energy (security : ℕ) (scalar : Scalar security) :
    (∑ primary, ∑ center, (primaryLaw security).weight primary * (bodyReference security).weight center *
      seedDensity security scalar primary center ^ 2) ≤
        12 * (Parameters.modulus security : ℝ) / Parameters.anchorWidth security := by
  have hcolumn (center : SafePalette security) :
      (primaryLaw security).l2Sq (fun primary => seedDensity security scalar primary center) ≤
        6 * (primaryLaw security).l2Sq (fun primary => secondCentered security scalar primary center) :=
    mismatch_center_energy (primaryLaw security) (uniformRelative security) _ (uniformRelative_energy security)
  calc
    _ = ∑ center, (bodyReference security).weight center *
        (primaryLaw security).l2Sq (fun primary => seedDensity security scalar primary center) := by
      rw [Finset.sum_comm]
      simp only [FiniteDist.l2Sq, FiniteDist.expectation, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro center _
      apply Finset.sum_congr rfl
      intro primary _
      ring
    _ ≤ ∑ center, (bodyReference security).weight center *
        (6 * (primaryLaw security).l2Sq (fun primary => secondCentered security scalar primary center)) :=
      Finset.sum_le_sum fun center _ => mul_le_mul_of_nonneg_left (hcolumn center) ((bodyReference security).nonneg center)
    _ = 6 * ∑ primary, (primaryLaw security).weight primary *
        (bodyReference security).l2Sq (secondCentered security scalar primary) := by
      simp only [FiniteDist.l2Sq, FiniteDist.expectation, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro primary _
      apply Finset.sum_congr rfl
      intro center _
      ring
    _ ≤ 6 * ∑ primary, (primaryLaw security).weight primary *
        (2 * (Parameters.modulus security : ℝ) / Parameters.anchorWidth security) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum fun primary _ => mul_le_mul_of_nonneg_left
        (secondCentered_energy security scalar primary) ((primaryLaw security).nonneg primary)
    _ = _ := by rw [← Finset.sum_mul, FiniteDist.sum_one, one_mul]; ring

end

end CurrentAFT.MarkedPairSeed
