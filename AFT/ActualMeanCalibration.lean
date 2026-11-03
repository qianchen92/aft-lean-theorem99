import AFT.ActualTripleMarginals
import AFT.BodyTranslation

/-! # The actual endpoint and body calibration gives the reference mean -/

namespace AFT.V7Calibration

open Filter GaussianSource TrimmedSlice
open scoped BigOperators Classical Topology

noncomputable section


def actualSliceAtSource (cutoffScale : ℝ) (parameter : ℕ) (source : ℤ)
    (color : Fin (Parameters.modulus parameter)) : ℝ :=
  fairMixedLaw (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter)
    (fun sample => (Parameters.anchorWidth parameter : ℤ) + bodyShift cutoffScale parameter sample)
    (fun sample => -(2 * (Parameters.anchorWidth parameter : ℤ)) + 1 + bodyShift cutoffScale parameter sample)
    (fun _ => source) (bodyBlur cutoffScale parameter).weight (Parameters.anchorWidth parameter) color.val

def actualSliceMean (cutoffScale : ℝ) (parameter : ℕ)
    (color : Fin (Parameters.modulus parameter)) : ℝ :=
  fairMixedLaw (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter)
    (startsPlus cutoffScale parameter) (startsMinus cutoffScale parameter)
    (pairSourceShift cutoffScale parameter) (pairSourceLaw cutoffScale parameter).weight
    (Parameters.anchorWidth parameter) color.val

def actualZeroSliceMean (cutoffScale : ℝ) (parameter : ℕ)
    (color : Fin (Parameters.modulus parameter)) : ℝ :=
  fairMixedLaw (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter)
    (startsPlus cutoffScale parameter) (startsMinus cutoffScale parameter)
    (fun _ => 0) (pairSourceLaw cutoffScale parameter).weight
    (Parameters.anchorWidth parameter) color.val

/-- The calibrated slice is the literal Gaussian average of the physical
fixed-source endpoint marginal. -/
theorem actualSliceMean_expectation (cutoffScale : ℝ) (parameter : ℕ)
    (color : Fin (Parameters.modulus parameter)) :
    actualSliceMean cutoffScale parameter color =
      (windowGaussian (10 * parameter) (legCutoff cutoffScale parameter - 1)).expectation
        (fun source => actualSliceAtSource cutoffScale parameter source color) := by
  simp only [actualSliceMean, actualSliceAtSource, fairMixedLaw, mixedLaw,
    pairSourceLaw, pairSample, Fintype.sum_prod_type, FiniteDist.prod_weight,
    startsPlus, startsMinus, pairSourceShift, FiniteDist.expectation,
    ← mul_div_assoc, mul_add, Finset.sum_add_distrib, ← Finset.sum_div]
  congr 1
  apply congrArg₂ (· + ·)
  all_goals
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro source _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro sample _
    ring

theorem actualZeroSliceMean_eq (cutoffScale : ℝ) (parameter : ℕ)
    (color : Fin (Parameters.modulus parameter)) :
    actualZeroSliceMean cutoffScale parameter color = actualSliceAtSource cutoffScale parameter 0 color := by
  simp only [actualZeroSliceMean, actualSliceAtSource, fairMixedLaw, mixedLaw,
    pairSourceLaw, pairSample, Fintype.sum_prod_type, FiniteDist.prod_weight,
    startsPlus, startsMinus]
  congr 1
  apply congrArg₂ (· + ·)
  all_goals
    apply Finset.sum_congr rfl
    intro sample _
    simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, FiniteDist.sum_one, one_mul]

/-- Exact one-endpoint marginal, retaining the true finite trimmed windows. -/
theorem inactivePairAtSource_marginal (cutoffScale : ℝ) (parameter : ℕ)
    (hboundary : 0 ≤ boundaryHalf cutoffScale parameter) (source : ℤ)
    (color : Fin (Parameters.modulus parameter)) :
    (∑ second, inactivePairAtSource cutoffScale parameter source color second) =
      actualSliceAtSource cutoffScale parameter source color := by
  simp only [inactivePairAtSource, ← Finset.sum_div, Finset.sum_add_distrib,
    mixedPair_first_marginal _ _ _ _ _ _ hboundary, actualSliceAtSource, fairMixedLaw]

/-- Removing the activation atom produces precisely the calibration's
unshifted subtraction, with its full activation coefficient. -/
theorem actual_inactive_marginal_calibration (cutoffScale : ℝ) (parameter : ℕ)
    (hboundary : 0 ≤ boundaryHalf cutoffScale parameter) (color : Fin (Parameters.modulus parameter)) :
    (1 - v7Activation cutoffScale parameter) *
        (∑ second, averagedInactivePair cutoffScale parameter color second) =
      actualSliceMean cutoffScale parameter color -
        v7Activation cutoffScale parameter * actualZeroSliceMean cutoffScale parameter color := by
  unfold averagedInactivePair
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, inactivePairAtSource_marginal cutoffScale parameter hboundary]
  rw [actualSliceMean_expectation, actualZeroSliceMean_eq]
  simp only [FiniteDist.expectation, Finset.mul_sum, ← mul_assoc]
  have hweight (source : Window (legCutoff cutoffScale parameter - 1)) :=
    inactiveLegSource_mixture cutoffScale parameter source
  calc
    _ = ∑ source : Window (legCutoff cutoffScale parameter - 1),
        ((windowGaussian (10 * parameter) (legCutoff cutoffScale parameter - 1)).weight source -
          if source = windowZero (legCutoff cutoffScale parameter - 1) then v7Activation cutoffScale parameter else 0) *
        actualSliceAtSource cutoffScale parameter source color := by
      apply Finset.sum_congr rfl
      intro source _
      rw [show (1 - v7Activation cutoffScale parameter) * (inactiveLegSource cutoffScale parameter).weight source =
        (windowGaussian (10 * parameter) (legCutoff cutoffScale parameter - 1)).weight source -
          (if source = windowZero (legCutoff cutoffScale parameter - 1) then v7Activation cutoffScale parameter else 0) by linarith [hweight source]]
    _ = _ := by
      simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, windowZero]

set_option backward.isDefEq.respectTransparency false in
/-- The actual base and beta repair solve their calibration equation. -/
theorem actual_calibration_identity (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (hactivation : v7Activation cutoffScale parameter ≠ 0) (color : Fin (Parameters.modulus parameter)) :
    ((Parameters.bodies parameter : ℝ) + Parameters.legs parameter * v7Activation cutoffScale parameter) *
        actualBodyMean cutoffScale parameter color +
      Parameters.legs parameter * (2 * actualSliceMean cutoffScale parameter color -
        2 * v7Activation cutoffScale parameter * actualZeroSliceMean cutoffScale parameter color) +
      (Parameters.legs parameter * v7Activation cutoffScale parameter) * actualPrimary cutoffScale parameter beta color =
        Parameters.dimension parameter * actualReferenceMean cutoffScale parameter beta color := by
  have hm : (Parameters.legs parameter : ℝ) ≠ 0 := by
    unfold Parameters.legs
    exact_mod_cast (pow_ne_zero 30 (by have := Parameters.security_ge_two parameter; omega : Parameters.security parameter ≠ 0))
  have hn : (Parameters.dimension parameter : ℝ) ≠ 0 := by
    exact_mod_cast (show Parameters.dimension parameter ≠ 0 by have := Parameters.population_identity parameter; have := Parameters.bodies_positive parameter; omega)
  have hpop : (Parameters.bodies parameter : ℝ) + 2 * Parameters.legs parameter = Parameters.dimension parameter := by
    exact_mod_cast Parameters.population_identity parameter
  have h := congrFun (calibratedPrimaryProfile_mean_identity (Parameters.dimension parameter)
    (Parameters.bodies parameter) (Parameters.legs parameter) (v7Activation cutoffScale parameter)
    (repairedBoundaryMass parameter cutoffScale beta (boundaryHalf cutoffScale parameter) -
      v7BaseBoundaryMass cutoffScale parameter (boundaryHalf cutoffScale parameter))
    (fun _ : Fin (Parameters.modulus parameter) => 1 / (Parameters.modulus parameter : ℝ))
    (actualBodyMean cutoffScale parameter) (actualSliceMean cutoffScale parameter)
    (actualZeroSliceMean cutoffScale parameter)
    (uniformFiniteProfile (boundaryPalette (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter)))
    (uniformFiniteProfile (boundaryPalette (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter))ᶜ)
    (mul_ne_zero hm hactivation) hn) color
  dsimp only [actualPrimary, primary, basePrimary, actualFairBasePrimary, actualBodyMean, bodyMean,
    actualSliceMean, actualZeroSliceMean, actualReferenceMean, referenceMean, diffuseEndpointMean,
    calibratedPrimaryProfile, basePrimaryProfile, calibratedReferenceMean] at h ⊢
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h ⊢
  dsimp only [basePrimary, actualFairBasePrimary, basePrimaryProfile, bodyMean,
    actualSliceMean, actualZeroSliceMean] at h ⊢
  by_cases hc : color ∈ boundaryPalette (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter)
  · simpa only [Int.cast_natCast, hpop, uniformFiniteProfile, Finset.mem_compl, hc, not_true_eq_false, if_true, if_false] using h
  · simpa only [Int.cast_natCast, hpop, uniformFiniteProfile, Finset.mem_compl, hc, not_false_eq_true, if_true, if_false] using h

/-- The fully blurred actual body center used by the physical mixture. -/
def actualFullBodyProfile (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (color : Fin (Parameters.modulus parameter)) : ℝ :=
  (bodyBlur cutoffScale parameter).expectation (fun sample =>
    integerShiftProfile parameter (actualBodyCenter cutoffScale parameter beta) (bodyShift cutoffScale parameter sample) color)

/-- Body compensation survives the real finite integer blur exactly. -/
theorem actualFullBodyProfile_formula (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (color : Fin (Parameters.modulus parameter)) :
    actualFullBodyProfile cutoffScale parameter beta color =
      (1 + bodyCompensation parameter cutoffScale) * actualBodyMean cutoffScale parameter color -
      bodyCompensation parameter cutoffScale *
        blurredAnchorMean (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
          (bodyShift cutoffScale parameter) (bodyBlur cutoffScale parameter)
          (actualPrimary cutoffScale parameter beta) color.val := by
  have hp : actualBodyCenter cutoffScale parameter beta =
      fun center => actualBodyIntegerProfile cutoffScale parameter beta center.val :=
    funext fun center => (actualBodyIntegerProfile_on_palette cutoffScale parameter beta center).symm
  unfold actualFullBodyProfile FiniteDist.expectation
  rw [hp]
  simp_rw [integerShiftProfile_function parameter _ (actualBodyIntegerProfile_support cutoffScale parameter beta)]
  simp only [actualBodyIntegerProfile, mul_sub, Finset.sum_sub_distrib]
  apply congrArg₂ (· - ·)
  · simp only [actualBodyMean, bodyMean, blurredSafeLaw, coreIntegerProfile,
      coreIntegerProfile_safeSize, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro sample _
    ring
  · simp only [anchorMean, blurredAnchorMean, blurredAnchorKernel, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro primary _
    apply Finset.sum_congr rfl
    intro sample _
    ring


/-- Both endpoint marginals, including the marked companion, are exactly
those used in the calibration numerator. -/
theorem actual_pair_total_marginal (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (hboundary : 0 ≤ boundaryHalf cutoffScale parameter)
    (hanchor : ∀ first : Fin (Parameters.modulus parameter),
      (∑ second : Fin (Parameters.modulus parameter),
        blurredAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
          (bodyShift cutoffScale parameter) (bodyBlur cutoffScale parameter) first second.val) = 1)
    (color : Fin (Parameters.modulus parameter)) :
    (∑ second, localPairMixture cutoffScale parameter beta color second) +
      (∑ first, localPairMixture cutoffScale parameter beta first color) =
      2 * (actualSliceMean cutoffScale parameter color -
        v7Activation cutoffScale parameter * actualZeroSliceMean cutoffScale parameter color) +
      v7Activation cutoffScale parameter * actualPrimary cutoffScale parameter beta color +
      v7Activation cutoffScale parameter *
        blurredAnchorMean (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
          (bodyShift cutoffScale parameter) (bodyBlur cutoffScale parameter)
          (actualPrimary cutoffScale parameter beta) color.val := by
  have hsym (first second) : averagedInactivePair cutoffScale parameter first second =
      averagedInactivePair cutoffScale parameter second first := by
    simp only [averagedInactivePair, inactivePairAtSource,
      mixedPair_symmetric _ _ _ _ _ _ first second]
  have hin := actual_inactive_marginal_calibration cutoffScale parameter hboundary color
  have hin' : (1 - v7Activation cutoffScale parameter) *
      (∑ first, averagedInactivePair cutoffScale parameter first color) =
        actualSliceMean cutoffScale parameter color -
          v7Activation cutoffScale parameter * actualZeroSliceMean cutoffScale parameter color := by
    simpa only [hsym _ color] using hin
  have hm : (∑ second, actualMarkedPair cutoffScale parameter beta color second) =
      actualPrimary cutoffScale parameter beta color := by
    simp only [actualMarkedPair, ← Finset.mul_sum, hanchor color, mul_one]
  have hm' : (∑ first, actualMarkedPair cutoffScale parameter beta first color) =
      blurredAnchorMean (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
        (bodyShift cutoffScale parameter) (bodyBlur cutoffScale parameter)
        (actualPrimary cutoffScale parameter beta) color.val := rfl
  simp only [localPairMixture, Finset.sum_add_distrib, ← Finset.mul_sum, hin, hin', hm, hm']
  ring

/-- The literal full body blur and both physical endpoint marginals have
exactly the declared reference mean, at the actual V7 populations. -/
theorem actual_total_mean_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) :
    ∀ᶠ parameter : ℕ in atTop, ∀ beta : ℝ, ∀ color : Fin (Parameters.modulus parameter),
      (Parameters.bodies parameter : ℝ) * actualFullBodyProfile cutoffScale parameter beta color +
        Parameters.legs parameter *
          ((∑ second, localPairMixture cutoffScale parameter beta color second) +
            (∑ first, localPairMixture cutoffScale parameter beta first color)) =
        Parameters.dimension parameter * actualReferenceMean cutoffScale parameter beta color := by
  filter_upwards [actual_full_anchor_safe_eventually cutoffScale hscale,
    actual_physical_supports_eventually cutoffScale hscale, eventually_ge_atTop 1]
    with parameter ha hs hp beta color
  have hactivation : v7Activation cutoffScale parameter ≠ 0 :=
    (activation_positive _ _ _ _ (legFeatureCount_positive cutoffScale parameter hscale hp)).ne'
  have hb : (Parameters.bodies parameter : ℝ) ≠ 0 := by
    exact_mod_cast (Parameters.bodies_positive parameter).ne'
  have hc := actual_calibration_identity cutoffScale parameter beta hactivation color
  rw [actualFullBodyProfile_formula,
    actual_pair_total_marginal cutoffScale parameter beta hs.1.1.1 (fun first => (ha first).1) color]
  calc
    _ = ((Parameters.bodies parameter : ℝ) + Parameters.legs parameter * v7Activation cutoffScale parameter) *
          actualBodyMean cutoffScale parameter color +
        Parameters.legs parameter * (2 * actualSliceMean cutoffScale parameter color -
          2 * v7Activation cutoffScale parameter * actualZeroSliceMean cutoffScale parameter color) +
        (Parameters.legs parameter * v7Activation cutoffScale parameter) * actualPrimary cutoffScale parameter beta color := by
      unfold bodyCompensation
      field_simp
      ring
    _ = _ := hc

end

end AFT.V7Calibration
