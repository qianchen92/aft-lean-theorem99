import AFT.ChartSupport

/-! # Legal-support chart families with the exact joint public response -/
namespace AFT.BoundaryCalibration
open GaussianSource Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
local instance supportedPublicFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
attribute [local instance] actualModulusNeZero

theorem gaussian_chart_joint_output_supported (cutoffScale : ℝ) (parameter : ℕ)
    (hscale : 1 ≤ cutoffScale) (hp : 1 ≤ parameter) (boundary baseline : ℤ)
    (hb : 0 ≤ boundary) (mark : Fin (Parameters.modulus parameter))
    (hchart : V7ChartExists cutoffScale parameter boundary baseline
      ((ZMod.finEquiv (Parameters.modulus parameter)) mark)) :
    ∃ chartLaw : FiniteDist (Chart (ZMod (Parameters.modulus parameter))),
      ProtectedChartSupport cutoffScale parameter boundary baseline mark chartLaw ∧
      ∀ first second : Fin (Parameters.modulus parameter),
      ∀ attached : Window (legCutoff cutoffScale parameter - 1) → ℝ,
      (∑ input : V7Input cutoffScale parameter, (protectedGaussianLaw cutoffScale parameter).weight input *
        (chartPairOutput cutoffScale parameter baseline chartLaw input).weight (first,second) * attached input.2) =
      (1 - v7Activation cutoffScale parameter) *
        (∑ source, (inactiveLegSource cutoffScale parameter).weight source *
          (TrimmedSlice.orderedPairSlice (Parameters.modulus parameter) boundary (baseline - source) first second * attached source)) +
      v7Activation cutoffScale parameter *
        ((if first = mark then 1 else 0) *
          (if second = paletteEmbedding parameter ((Parameters.modulus parameter : ℤ) - 1 + baseline - mark.val) then 1 else 0) *
          attached (windowZero _)) := by
  obtain ⟨law, hsupport, hlaw⟩ := chart_joint_output_supported cutoffScale parameter boundary baseline hb mark hchart
  refine ⟨law, hsupport, ?_⟩
  intro first second attached
  have hh := protected_gaussian_marked_average cutoffScale parameter hscale hp
    (fun source => TrimmedSlice.orderedPairSlice (Parameters.modulus parameter) boundary (baseline - source) first second * attached source)
    (fun source => (if first = mark then 1 else 0) *
      (if second = paletteEmbedding parameter ((Parameters.modulus parameter : ℤ) - 1 + baseline - source - mark.val) then 1 else 0) * attached source)
  calc
    _ = ∑ input : V7Input cutoffScale parameter, (protectedGaussianLaw cutoffScale parameter).weight input *
        ((1 - if input = (windowZero _,windowZero _) then chartAtom (V7Input cutoffScale parameter) else 0) *
            (TrimmedSlice.orderedPairSlice (Parameters.modulus parameter) boundary (baseline - input.2) first second * attached input.2) +
          (if input = (windowZero _,windowZero _) then chartAtom (V7Input cutoffScale parameter) else 0) *
            ((if first = mark then 1 else 0) *
              (if second = paletteEmbedding parameter ((Parameters.modulus parameter : ℤ) - 1 + baseline - input.2 - mark.val) then 1 else 0) * attached input.2)) := by
      apply Finset.sum_congr rfl
      intro input _
      rw [hlaw]
      ring
    _ = _ := by simpa only [windowZero, sub_zero] using hh

end
end AFT.BoundaryCalibration
namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
local instance supportedPublicFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
attribute [local instance] actualModulusNeZero

theorem public_chart_supported_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) :
    ∀ᶠ parameter in atTop, ∀ mark : Fin (Parameters.modulus parameter),
      ∃ charts : PublicChartFamily cutoffScale parameter mark,
      (∀ (sample : bodySample cutoffScale parameter × Bool) (offset : PublicOffsets cutoffScale parameter mark sample),
        ProtectedChartSupport cutoffScale parameter (boundaryHalf cutoffScale parameter) offset mark (charts sample offset)) ∧
      ∀ (attached : Window (legCutoff cutoffScale parameter - 1) → ℝ) (first second : Fin (Parameters.modulus parameter)),
        publicChartRaw cutoffScale parameter mark charts attached first second =
          conditionalJointOutput cutoffScale parameter mark attached first second := by
  filter_upwards [conditional_chart_legal_eventually cutoffScale hscale,
    body_support_scales_eventually cutoffScale hscale, eventually_ge_atTop 1] with parameter hc hs hp
  intro mark
  choose charts hsupport hcharts using (fun (sample : bodySample cutoffScale parameter × Bool)
    (offset : PublicOffsets cutoffScale parameter mark sample) =>
      gaussian_chart_joint_output_supported cutoffScale parameter hscale hp (boundaryHalf cutoffScale parameter) offset hc.1 mark
        (hc.2 mark sample offset offset.property))
  refine ⟨charts, hsupport, ?_⟩
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
