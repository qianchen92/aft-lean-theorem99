import AFT.ActualWeightedTriples
import AFT.ActualMeanCalibration

/-! # Actual weighted chart endpoint marginals and calibrated sign response -/

namespace AFT.V7Calibration

open GaussianSource BoundaryCalibration Filter TrimmedSlice
open scoped BigOperators Classical Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance actualScoreFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
attribute [local instance] actualModulusNeZero

def signedSliceAtSource (cutoffScale : ℝ) (parameter : ℕ) (source : ℤ)
    (color : Fin (Parameters.modulus parameter)) : ℝ :=
  (mixedLaw (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter)
    (fun sample => (Parameters.anchorWidth parameter : ℤ) + bodyShift cutoffScale parameter sample)
    (fun _ => source) (bodyBlur cutoffScale parameter).weight (Parameters.anchorWidth parameter) color.val -
   mixedLaw (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter)
    (fun sample => -(2 * (Parameters.anchorWidth parameter : ℤ)) + 1 + bodyShift cutoffScale parameter sample)
    (fun _ => source) (bodyBlur cutoffScale parameter).weight (Parameters.anchorWidth parameter) color.val) / 2

theorem signedPairAtSource_marginal (cutoffScale : ℝ) (parameter : ℕ)
    (hboundary : 0 ≤ boundaryHalf cutoffScale parameter) (source : ℤ)
    (color : Fin (Parameters.modulus parameter)) :
    (∑ second, signedPairAtSource cutoffScale parameter source color second) =
      signedSliceAtSource cutoffScale parameter source color := by
  simp only [signedPairAtSource, ← Finset.sum_div, Finset.sum_sub_distrib,
    mixedPair_first_marginal _ _ _ _ _ _ hboundary, signedSliceAtSource]

theorem signedPairAtSource_symm (cutoffScale : ℝ) (parameter : ℕ) (source : ℤ)
    (first second : Fin (Parameters.modulus parameter)) :
    signedPairAtSource cutoffScale parameter source first second =
      signedPairAtSource cutoffScale parameter source second first := by
  simp only [signedPairAtSource, mixedPair_symmetric _ _ _ _ _ _ first second]

theorem inactiveLegSource_expectation (cutoffScale : ℝ) (parameter : ℕ)
    (f : Window (legCutoff cutoffScale parameter - 1) → ℝ) :
    (1 - v7Activation cutoffScale parameter) *
        (∑ source, (inactiveLegSource cutoffScale parameter).weight source * f source) =
      (∑ source, (windowGaussian (10 * parameter) (legCutoff cutoffScale parameter - 1)).weight source * f source) -
        v7Activation cutoffScale parameter * f (windowZero _) := by
  simp only [Finset.mul_sum, ← mul_assoc]
  calc
    _ = ∑ source, ((windowGaussian (10 * parameter) (legCutoff cutoffScale parameter - 1)).weight source -
        if source = windowZero _ then v7Activation cutoffScale parameter else 0) * f source := by
      apply Finset.sum_congr rfl
      intro source _
      congr 1
      have hh := inactiveLegSource_mixture cutoffScale parameter source
      linarith
    _ = _ := by
      simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem sourceMixedLaw_expectation (cutoffScale : ℝ) (parameter : ℕ)
    (start : bodySample cutoffScale parameter → ℤ) (color : Fin (Parameters.modulus parameter)) :
    mixedLaw (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter)
        (fun sample : pairSample cutoffScale parameter => start sample.1)
        (pairSourceShift cutoffScale parameter) (pairSourceLaw cutoffScale parameter).weight
        (Parameters.anchorWidth parameter) color.val =
      ∑ source, (windowGaussian (10 * parameter) (legCutoff cutoffScale parameter - 1)).weight source *
        mixedLaw (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter)
          start (fun _ => (source : ℤ)) (bodyBlur cutoffScale parameter).weight (Parameters.anchorWidth parameter) color.val := by
  simp only [mixedLaw, pairSourceLaw, pairSample, Fintype.sum_prod_type,
    FiniteDist.prod_weight, pairSourceShift, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro source _
  apply Finset.sum_congr rfl
  intro sample _
  ring

theorem zeroMixedLaw_expectation (cutoffScale : ℝ) (parameter : ℕ)
    (start : bodySample cutoffScale parameter → ℤ) (color : Fin (Parameters.modulus parameter)) :
    mixedLaw (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter)
        (fun sample : pairSample cutoffScale parameter => start sample.1)
        (fun _ => 0) (pairSourceLaw cutoffScale parameter).weight (Parameters.anchorWidth parameter) color.val =
      mixedLaw (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter)
        start (fun _ => 0) (bodyBlur cutoffScale parameter).weight (Parameters.anchorWidth parameter) color.val := by
  simp only [mixedLaw, pairSourceLaw, pairSample, Fintype.sum_prod_type, FiniteDist.prod_weight]
  apply Finset.sum_congr rfl
  intro sample _
  simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, FiniteDist.sum_one, one_mul]

/-- The sign part of the actual chart response is exactly the calibrated
rank-one response; its activation subtraction follows from the real source law. -/
theorem actualSignResponse_source_average (cutoffScale : ℝ) (parameter : ℕ)
    (color : Fin (Parameters.modulus parameter)) :
    2 * (1 - v7Activation cutoffScale parameter) *
        (∑ source, (inactiveLegSource cutoffScale parameter).weight source *
          signedSliceAtSource cutoffScale parameter source color) =
      signResponse parameter cutoffScale (boundaryHalf cutoffScale parameter)
        (startsPlus cutoffScale parameter) (startsMinus cutoffScale parameter)
        (pairSourceShift cutoffScale parameter) (pairSourceLaw cutoffScale parameter) color := by
  rw [mul_assoc, inactiveLegSource_expectation]
  unfold signResponse actualSignResponse calibratedSignResponse
  unfold GaussianSource.startsPlus GaussianSource.startsMinus
  rw [sourceMixedLaw_expectation cutoffScale parameter (fun sample => (Parameters.anchorWidth parameter : ℤ) + bodyShift cutoffScale parameter sample) color,
    sourceMixedLaw_expectation cutoffScale parameter (fun sample => -(2 * (Parameters.anchorWidth parameter : ℤ)) + 1 + bodyShift cutoffScale parameter sample) color,
    zeroMixedLaw_expectation cutoffScale parameter (fun sample => (Parameters.anchorWidth parameter : ℤ) + bodyShift cutoffScale parameter sample) color,
    zeroMixedLaw_expectation cutoffScale parameter (fun sample => -(2 * (Parameters.anchorWidth parameter : ℤ)) + 1 + bodyShift cutoffScale parameter sample) color]
  simp only [signedSliceAtSource, windowZero]
  ring_nf
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul]
  ring

theorem signedDiffuseJoint_marginals (cutoffScale : ℝ) (parameter : ℕ)
    (hboundary : 0 ≤ boundaryHalf cutoffScale parameter) (color : Fin (Parameters.modulus parameter)) :
    (∑ second, signedDiffuseJoint cutoffScale parameter (fun _ => 1) color second) +
        (∑ first, signedDiffuseJoint cutoffScale parameter (fun _ => 1) first color) =
      signResponse parameter cutoffScale (boundaryHalf cutoffScale parameter)
        (startsPlus cutoffScale parameter) (startsMinus cutoffScale parameter)
        (pairSourceShift cutoffScale parameter) (pairSourceLaw cutoffScale parameter) color := by
  have hfirst : (∑ second, signedDiffuseJoint cutoffScale parameter (fun _ => 1) color second) =
      (1 - v7Activation cutoffScale parameter) *
        ∑ source, (inactiveLegSource cutoffScale parameter).weight source *
          signedSliceAtSource cutoffScale parameter source color := by
    simp only [signedDiffuseJoint, mul_one, ← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, signedPairAtSource_marginal cutoffScale parameter hboundary]
  have hsecond : (∑ first, signedDiffuseJoint cutoffScale parameter (fun _ => 1) first color) =
      ∑ second, signedDiffuseJoint cutoffScale parameter (fun _ => 1) color second := by
    simp only [signedDiffuseJoint, signedPairAtSource_symm cutoffScale parameter _ _ color]
  rw [hsecond, hfirst]
  convert actualSignResponse_source_average cutoffScale parameter color using 1
  ring

/-- The full marked and diffuse primary numerator has exactly the physical
first response, including both endpoint positions. -/
theorem primaryJointNumerator_marginals (cutoffScale : ℝ) (parameter : ℕ)
    (hboundary : 0 ≤ boundaryHalf cutoffScale parameter)
    (hmass : ∀ color : Fin (Parameters.modulus parameter),
      (∑ output : Fin (Parameters.modulus parameter), blurredAnchorKernel (Parameters.modulus parameter)
        (Parameters.anchorWidth parameter) (bodyShift cutoffScale parameter) (bodyBlur cutoffScale parameter) color output.val) = 1)
    (profile : Fin (Parameters.modulus parameter) → ℝ) (color : Fin (Parameters.modulus parameter)) :
    (∑ second, primaryJointNumerator cutoffScale parameter profile (fun _ => 1) color second) +
      (∑ first, primaryJointNumerator cutoffScale parameter profile (fun _ => 1) first color) =
      v7Activation cutoffScale parameter * profile color +
        signResponse parameter cutoffScale (boundaryHalf cutoffScale parameter)
          (startsPlus cutoffScale parameter) (startsMinus cutoffScale parameter)
          (pairSourceShift cutoffScale parameter) (pairSourceLaw cutoffScale parameter) color *
            (∑ mark, paletteSign (Parameters.modulus parameter) mark * profile mark) +
        v7Activation cutoffScale parameter * blurredAnchorMean (Parameters.modulus parameter)
          (Parameters.anchorWidth parameter) (bodyShift cutoffScale parameter) (bodyBlur cutoffScale parameter) profile color.val := by
  have hd := signedDiffuseJoint_marginals cutoffScale parameter hboundary color
  simp only [primaryJointNumerator, mul_one, Finset.sum_add_distrib, ← Finset.mul_sum, hmass]
  have he : (∑ first, v7Activation cutoffScale parameter * profile first *
      blurredAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
        (bodyShift cutoffScale parameter) (bodyBlur cutoffScale parameter) first color.val) =
      v7Activation cutoffScale parameter * blurredAnchorMean (Parameters.modulus parameter)
        (Parameters.anchorWidth parameter) (bodyShift cutoffScale parameter) (bodyBlur cutoffScale parameter) profile color.val := by
    simp only [blurredAnchorMean, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro first _
    ring
  rw [he]
  rw [← hd]
  ring

end
end AFT.V7Calibration
