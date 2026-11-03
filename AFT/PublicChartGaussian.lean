import AFT.PublicChartOutput

/-! # The complete positive chart and public-anchor conditional output -/

namespace AFT.V7Calibration

open GaussianSource BoundaryCalibration Filter
open scoped BigOperators Classical Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
local instance publicGaussianFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
attribute [local instance] actualModulusNeZero

abbrev PublicOffsets (cutoffScale : ℝ) (parameter : ℕ) (mark : Fin (Parameters.modulus parameter))
    (sample : bodySample cutoffScale parameter × Bool) :=
  {offset : ℤ // offset ∈ anchorInterval (conditionalPairStart cutoffScale parameter mark sample) (Parameters.anchorWidth parameter)}

theorem sum_publicOffsets (cutoffScale : ℝ) (parameter : ℕ) (mark : Fin (Parameters.modulus parameter))
    (sample : bodySample cutoffScale parameter × Bool) (function : ℤ → ℝ) :
    (∑ offset : PublicOffsets cutoffScale parameter mark sample, function offset) =
      ∑ offset ∈ anchorInterval (conditionalPairStart cutoffScale parameter mark sample) (Parameters.anchorWidth parameter), function offset := by
  exact Finset.sum_coe_sort _ function

def publicOffsetLaw (cutoffScale : ℝ) (parameter : ℕ) (mark : Fin (Parameters.modulus parameter))
    (sample : bodySample cutoffScale parameter × Bool) : FiniteDist (PublicOffsets cutoffScale parameter mark sample) where
  weight offset := intervalAnchorLaw (conditionalPairStart cutoffScale parameter mark sample) (Parameters.anchorWidth parameter) offset
  nonneg offset := intervalAnchorLaw_nonneg _ _ _
  sum_one := by
    rw [Finset.sum_coe_sort]
    apply intervalAnchorLaw_mass
    unfold Parameters.anchorWidth
    exact pow_ne_zero _ (by have hh := Parameters.security_ge_two parameter; omega)

abbrev PublicChartFamily (cutoffScale : ℝ) (parameter : ℕ) (mark : Fin (Parameters.modulus parameter)) :=
  (sample : bodySample cutoffScale parameter × Bool) → PublicOffsets cutoffScale parameter mark sample →
    FiniteDist (Chart (ZMod (Parameters.modulus parameter)))

/-- A literal expectation over the actual public body blur, midpoint coin,
uniform anchor, two Gaussian errors, and positive affine chart. -/
def publicChartRaw (cutoffScale : ℝ) (parameter : ℕ) (mark : Fin (Parameters.modulus parameter))
    (charts : PublicChartFamily cutoffScale parameter mark)
    (attached : Window (legCutoff cutoffScale parameter - 1) → ℝ)
    (first second : Fin (Parameters.modulus parameter)) : ℝ :=
  ∑ sample, (errorLaw (bodyBlur cutoffScale parameter)).weight sample *
    ∑ offset, (publicOffsetLaw cutoffScale parameter mark sample).weight offset *
      ∑ input, (protectedGaussianLaw cutoffScale parameter).weight input *
        (chartPairOutput cutoffScale parameter offset (charts sample offset) input).weight (first,second) * attached input.2

/-- The conditional local law keeps the primary-dependent sign and the
same second-source variable in the pair and attached body. -/
def conditionalJointOutput (cutoffScale : ℝ) (parameter : ℕ) (mark : Fin (Parameters.modulus parameter))
    (attached : Window (legCutoff cutoffScale parameter - 1) → ℝ)
    (first second : Fin (Parameters.modulus parameter)) : ℝ :=
  (1 - v7Activation cutoffScale parameter) *
    (∑ source, (inactiveLegSource cutoffScale parameter).weight source *
      conditionalPairAtSource cutoffScale parameter mark source first second * attached source) +
  v7Activation cutoffScale parameter * (if first = mark then 1 else 0) *
    blurredAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
      (bodyShift cutoffScale parameter) (bodyBlur cutoffScale parameter) mark second.val * attached (windowZero _)

theorem public_diffuse_average (cutoffScale : ℝ) (parameter : ℕ) (mark : Fin (Parameters.modulus parameter))
    (attached : Window (legCutoff cutoffScale parameter - 1) → ℝ)
    (first second : Fin (Parameters.modulus parameter)) :
    (∑ sample, (errorLaw (bodyBlur cutoffScale parameter)).weight sample *
      ∑ offset, (publicOffsetLaw cutoffScale parameter mark sample).weight offset *
        ∑ source, (inactiveLegSource cutoffScale parameter).weight source *
          (TrimmedSlice.orderedPairSlice (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter)
            ((offset : ℤ) - source) first second * attached source)) =
    ∑ source, (inactiveLegSource cutoffScale parameter).weight source *
      conditionalPairAtSource cutoffScale parameter mark source first second * attached source := by
  have hsample (sample : bodySample cutoffScale parameter × Bool) :
      (∑ offset, (publicOffsetLaw cutoffScale parameter mark sample).weight offset *
        ∑ source, (inactiveLegSource cutoffScale parameter).weight source *
          (TrimmedSlice.orderedPairSlice (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter)
            ((offset : ℤ) - source) first second * attached source)) =
      ∑ source, (inactiveLegSource cutoffScale parameter).weight source *
        TrimmedSlice.averagedPair (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter)
          (conditionalPairStart cutoffScale parameter mark sample) source (Parameters.anchorWidth parameter) first second * attached source := by
    change (∑ offset : PublicOffsets cutoffScale parameter mark sample,
      intervalAnchorLaw (conditionalPairStart cutoffScale parameter mark sample) (Parameters.anchorWidth parameter) offset * _) = _
    calc
      _ = ∑ offset ∈ anchorInterval (conditionalPairStart cutoffScale parameter mark sample) (Parameters.anchorWidth parameter),
          intervalAnchorLaw (conditionalPairStart cutoffScale parameter mark sample) (Parameters.anchorWidth parameter) offset *
            ∑ source, (inactiveLegSource cutoffScale parameter).weight source *
              (TrimmedSlice.orderedPairSlice (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter)
                (offset - source) first second * attached source) :=
        sum_publicOffsets cutoffScale parameter mark sample (fun offset =>
          intervalAnchorLaw (conditionalPairStart cutoffScale parameter mark sample) (Parameters.anchorWidth parameter) offset *
            ∑ source, (inactiveLegSource cutoffScale parameter).weight source *
              (TrimmedSlice.orderedPairSlice (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter)
                (offset - source) first second * attached source))
      _ = _ := by
        simp only [TrimmedSlice.averagedPair, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro source _
        apply Finset.sum_congr rfl
        intro offset _
        ring
  calc
    _ = ∑ sample, (errorLaw (bodyBlur cutoffScale parameter)).weight sample *
        ∑ source, (inactiveLegSource cutoffScale parameter).weight source *
          TrimmedSlice.averagedPair (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter)
            (conditionalPairStart cutoffScale parameter mark sample) source (Parameters.anchorWidth parameter) first second * attached source := by
      apply Finset.sum_congr rfl
      intro sample _
      exact congrArg ((errorLaw (bodyBlur cutoffScale parameter)).weight sample * ·) (hsample sample)
    _ = _ := by
      simp only [conditionalPairAtSource, TrimmedSlice.mixedPair, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro source _
      apply Finset.sum_congr rfl
      intro sample _
      ring

/-- Real public parameters construct a positive chart family whose entire
source-dependent joint response is the asserted conditional law. -/
theorem public_chart_joint_output_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) :
    ∀ᶠ parameter in atTop, ∀ mark : Fin (Parameters.modulus parameter),
      ∃ charts : PublicChartFamily cutoffScale parameter mark,
      ∀ (attached : Window (legCutoff cutoffScale parameter - 1) → ℝ) (first second : Fin (Parameters.modulus parameter)),
        publicChartRaw cutoffScale parameter mark charts attached first second =
          conditionalJointOutput cutoffScale parameter mark attached first second := by
  filter_upwards [conditional_chart_legal_eventually cutoffScale hscale,
    body_support_scales_eventually cutoffScale hscale, eventually_ge_atTop 1] with parameter hc hs hp
  intro mark
  choose charts hcharts using (fun (sample : bodySample cutoffScale parameter × Bool)
    (offset : PublicOffsets cutoffScale parameter mark sample) =>
      gaussian_chart_joint_output cutoffScale parameter hscale hp (boundaryHalf cutoffScale parameter) offset hc.1 mark
        (hc.2 mark sample offset offset.property))
  refine ⟨charts, ?_⟩
  intro attached first second
  unfold publicChartRaw
  simp_rw [hcharts]
  simp only [mul_add, Finset.sum_add_distrib]
  have hfirst : (∑ sample, (errorLaw (bodyBlur cutoffScale parameter)).weight sample *
      ∑ offset, (publicOffsetLaw cutoffScale parameter mark sample).weight offset *
        ((1 - v7Activation cutoffScale parameter) *
          ∑ source, (inactiveLegSource cutoffScale parameter).weight source *
            (TrimmedSlice.orderedPairSlice (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter)
              ((offset : ℤ) - source) first second * attached source))) =
      (1 - v7Activation cutoffScale parameter) *
        ∑ source, (inactiveLegSource cutoffScale parameter).weight source *
          conditionalPairAtSource cutoffScale parameter mark source first second * attached source := by
    rw [← public_diffuse_average]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro sample _
    apply Finset.sum_congr rfl
    intro offset _
    apply Finset.sum_congr rfl
    intro source _
    ring
  rw [hfirst]
  unfold conditionalJointOutput
  congr 1
  have ha := public_marked_anchor_average cutoffScale parameter (by exact_mod_cast hs.2.1) mark second
  rw [← ha]
  simp only [publicOffsetLaw, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro sample _
  calc
    _ = ∑ offset ∈ anchorInterval (conditionalPairStart cutoffScale parameter mark sample) (Parameters.anchorWidth parameter),
      (errorLaw (bodyBlur cutoffScale parameter)).weight sample *
        (intervalAnchorLaw (conditionalPairStart cutoffScale parameter mark sample) (Parameters.anchorWidth parameter) offset *
          (v7Activation cutoffScale parameter * (((if first = mark then 1 else 0) *
            if second = paletteEmbedding parameter ((Parameters.modulus parameter : ℤ) - 1 + offset - mark.val) then 1 else 0) *
              attached (windowZero _)))) :=
      sum_publicOffsets cutoffScale parameter mark sample (fun offset =>
        (errorLaw (bodyBlur cutoffScale parameter)).weight sample *
          (intervalAnchorLaw (conditionalPairStart cutoffScale parameter mark sample) (Parameters.anchorWidth parameter) offset *
            (v7Activation cutoffScale parameter * (((if first = mark then 1 else 0) *
              if second = paletteEmbedding parameter ((Parameters.modulus parameter : ℤ) - 1 + offset - mark.val) then 1 else 0) *
                attached (windowZero _)))))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro offset _
      ring

end
end AFT.V7Calibration
