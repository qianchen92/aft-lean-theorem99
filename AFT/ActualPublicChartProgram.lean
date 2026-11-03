import AFT.ActualChartSamplerCertificate
import AFT.PublicChartSupport
import AFT.ActualSliceMeanProgram

/-! # The executable chart law inside the actual public-anchor family -/
namespace AFT.BoundaryCalibration
open GaussianSource Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
theorem gaussian_chart_joint_output_of_pair_formula (cutoffScale : ℝ) (parameter : ℕ)
    (hscale : 1 ≤ cutoffScale) (hp : 1 ≤ parameter) (boundary baseline : ℤ)
    (mark : Fin (Parameters.modulus parameter))
    (chartLaw : FiniteDist (Chart (ZMod (Parameters.modulus parameter))))
    (hlaw : ∀ input : V7Input cutoffScale parameter,∀ first second : Fin (Parameters.modulus parameter),
      (chartPairOutput cutoffScale parameter baseline chartLaw input).weight (first,second)=
        (1-if input=(windowZero _,windowZero _) then chartAtom (V7Input cutoffScale parameter) else 0)*
          TrimmedSlice.orderedPairSlice (Parameters.modulus parameter) boundary (baseline-input.2) first second+
        (if input=(windowZero _,windowZero _) then chartAtom (V7Input cutoffScale parameter) else 0)*(if first=mark then 1 else 0)*
          (if second=paletteEmbedding parameter ((Parameters.modulus parameter : ℤ)-1+baseline-input.2-mark.val) then 1 else 0)) :
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
open scoped BigOperators

def actualPublicChartDraw (constant n : ℕ) (baseline : ℤ) (mark : Fin (Parameters.modulus n))
    (word : Fin (n+Parameters.modulus n*(Parameters.modulus n*Parameters.modulus n)+1) → Fin 2) :
      Chart (ZMod (Parameters.modulus n)) :=
  actualPhysicalChartDraw constant n (actualBoundaryHalfProgram constant n) baseline n n mark word

noncomputable section
open scoped Classical Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000

theorem actualPublicChartDraw_eq (constant n : ℕ) (baseline : ℤ) (mark : Fin (Parameters.modulus n)) :
    actualPublicChartDraw constant n baseline mark=
      actualPhysicalChartDraw constant n (boundaryHalf (constant : ℝ) n) baseline n n mark := by
  unfold actualPublicChartDraw
  rw [actualBoundaryHalfProgram_eq]


theorem public_chart_raw_of_joint_formula (cutoffScale : ℝ) (parameter : ℕ)
    (mark : Fin (Parameters.modulus parameter)) (charts : PublicChartFamily cutoffScale parameter mark)
    (hmax : (maxBodyShift cutoffScale parameter : ℤ)≤Parameters.anchorWidth parameter)
    (hcharts : ∀ (sample : bodySample cutoffScale parameter × Bool)
      (offset : PublicOffsets cutoffScale parameter mark sample)
      (first second : Fin (Parameters.modulus parameter))
      (attached : Window (legCutoff cutoffScale parameter-1) → ℝ),
      (∑ input : V7Input cutoffScale parameter,(protectedGaussianLaw cutoffScale parameter).weight input*
        (chartPairOutput cutoffScale parameter offset (charts sample offset) input).weight (first,second)*attached input.2)=
      (1-v7Activation cutoffScale parameter)*(∑ source,(inactiveLegSource cutoffScale parameter).weight source*
        (TrimmedSlice.orderedPairSlice (Parameters.modulus parameter) (boundaryHalf cutoffScale parameter) (offset-source) first second*attached source))+
      v7Activation cutoffScale parameter*((if first=mark then 1 else 0)*
        (if second=paletteEmbedding parameter ((Parameters.modulus parameter : ℤ)-1+offset-mark.val) then 1 else 0)*attached (windowZero _))) :
    ∀ attached first second,publicChartRaw cutoffScale parameter mark charts attached first second=
      conditionalJointOutput cutoffScale parameter mark attached first second := by
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
  have ha := public_marked_anchor_average cutoffScale parameter hmax mark second
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
      split_ifs <;> ring


attribute [local irreducible] actualPhysicalChartDraw safeFiniteAffineChartDraw actualPublicChartDraw

theorem actual_public_chart_sampler_eventually (constant : ℕ) (hconstant : 1≤constant) :
    ∀ᶠ parameter in atTop, ∀ mark : Fin (Parameters.modulus parameter),
      ∃ charts : PublicChartFamily (constant : ℝ) parameter mark,
      (∀ (sample : bodySample (constant : ℝ) parameter × Bool)
        (offset : PublicOffsets (constant : ℝ) parameter mark sample),
        ProtectedChartSupport (constant : ℝ) parameter (boundaryHalf (constant : ℝ) parameter) offset mark (charts sample offset)) ∧
      (∀ (attached : Window (legCutoff (constant : ℝ) parameter - 1) → ℝ)
        (first second : Fin (Parameters.modulus parameter)),
        publicChartRaw (constant : ℝ) parameter mark charts attached first second =
          conditionalJointOutput (constant : ℝ) parameter mark attached first second) ∧
      (∀ (sample : bodySample (constant : ℝ) parameter × Bool)
        (offset : PublicOffsets (constant : ℝ) parameter mark sample),
        (∑ chart, |((FiniteDist.independent (fun _ : Fin (parameter+Parameters.modulus parameter*(Parameters.modulus parameter*Parameters.modulus parameter)+1) =>
          FiniteDist.uniform (Fin 2))).map (actualPublicChartDraw constant parameter offset mark)).weight chart-(charts sample offset).weight chart|)≤
            actualChartNumericalError parameter) := by
  have hscale : (1 : ℝ)≤constant := by exact_mod_cast hconstant
  filter_upwards [actual_physical_chart_sampler_eventually constant hconstant,
    body_support_scales_eventually (constant : ℝ) hscale,eventually_ge_atTop 1] with parameter hc hs hp
  intro mark
  have hoffset (sample : bodySample (constant : ℝ) parameter × Bool)
      (offset : PublicOffsets (constant : ℝ) parameter mark sample) : |(offset : ℤ)|≤3*Parameters.anchorWidth parameter := by
    have hb := abs_le.mp (bodyShift_abs_le (constant : ℝ) parameter sample.1)
    have hmax : (maxBodyShift (constant : ℝ) parameter : ℤ)≤Parameters.anchorWidth parameter := by exact_mod_cast hs.2.1
    have hbase := offset.property
    simp only [conditionalPairStart,conditionalBaselineStart_formula] at hbase
    split_ifs at hbase <;> simp only [anchorInterval,Finset.mem_Ico] at hbase <;>
      exact abs_le.mpr (by constructor <;> omega)
  choose charts hsupport hformula hlegal herror using (fun (sample : bodySample (constant : ℝ) parameter × Bool)
    (offset : PublicOffsets (constant : ℝ) parameter mark sample) =>
      hc (boundaryHalf (constant : ℝ) parameter) offset hs.2.2.1 hs.2.2.2 (hoffset sample offset) mark)
  have hcharts (sample : bodySample (constant : ℝ) parameter × Bool)
      (offset : PublicOffsets (constant : ℝ) parameter mark sample) :=
    gaussian_chart_joint_output_of_pair_formula (constant : ℝ) parameter hscale hp
      (boundaryHalf (constant : ℝ) parameter) offset mark (charts sample offset) (hformula sample offset)
  refine ⟨charts,hsupport,?_,?_⟩
  · exact public_chart_raw_of_joint_formula (constant : ℝ) parameter mark charts (by exact_mod_cast hs.2.1) hcharts

  · intro sample offset
    rw [actualPublicChartDraw_eq]
    exact herror sample offset

end
end AFT.V7Calibration
