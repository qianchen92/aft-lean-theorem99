import AFT.BoundaryChartParameters
import AFT.BodyBlurParameters

/-! # Actual marked charts at the public anchor and blur samples -/

namespace AFT.BoundaryCalibration

open Filter
open scoped BigOperators Classical Topology

noncomputable section

/-- The protected alphabet has exactly the paper's number of features. -/
theorem v7Input_card (cutoffScale : ℝ) (parameter : ℕ)
    (hscale : 1 ≤ cutoffScale) (hp : 1 ≤ parameter) :
    Fintype.card (V7Input cutoffScale parameter) = GaussianSource.legFeatureCount cutoffScale parameter := by
  rw [protectedInputs_card, GaussianSource.legFeatureCount]
  have hc := GaussianSource.legCutoff_positive cutoffScale parameter hscale hp
  congr 1
  omega

theorem v7_chartAtom_eq (cutoffScale : ℝ) (parameter : ℕ)
    (hscale : 1 ≤ cutoffScale) (hp : 1 ≤ parameter) :
    chartAtom (V7Input cutoffScale parameter) =
      (100 * (GaussianSource.legFeatureCount cutoffScale parameter : ℝ))⁻¹ := by
  rw [chartAtom, v7Input_card cutoffScale parameter hscale hp]

/-- Every public sign/offset and actual blur sample yields a legal baseline
for the previously constructed chart.  The boundary width is the actual
safe margin minus the complete root/leg/queue support bound. -/
theorem actual_marked_chart_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) :
    ∀ᶠ parameter : ℕ in atTop,
      ∀ sample : GaussianSource.bodySample cutoffScale parameter,
      ∀ offset : ℤ, offset ∈ anchorInterval (Parameters.anchorWidth parameter)
        (Parameters.anchorWidth parameter) →
      ∀ sign : ℤ, |sign| ≤ 1 →
      ∀ mark : ZMod (Parameters.modulus parameter),
        V7ChartExists cutoffScale parameter (GaussianSource.boundaryHalf cutoffScale parameter)
          (sign * offset + GaussianSource.bodyShift cutoffScale parameter sample) mark := by
  filter_upwards [v7_marked_chart_eventually cutoffScale hscale,
    GaussianSource.body_support_scales_eventually cutoffScale hscale] with parameter hchart hscales
  intro sample offset hoffset sign hsign mark
  apply hchart _ _ hscales.2.2.1 hscales.2.2.2
  have hb := GaussianSource.bodyShift_abs_le cutoffScale parameter sample
  have hb' : |GaussianSource.bodyShift cutoffScale parameter sample| ≤
      (Parameters.anchorWidth parameter : ℤ) := hb.trans (by exact_mod_cast hscales.2.1)
  have ho := Finset.mem_Ico.mp hoffset
  have hoabs : |offset| ≤ 2 * (Parameters.anchorWidth parameter : ℤ) := by
    rw [abs_of_nonneg (by omega)]
    omega
  calc
    _ ≤ |sign * offset| + |GaussianSource.bodyShift cutoffScale parameter sample| := abs_add_le _ _
    _ = |sign| * |offset| + |GaussianSource.bodyShift cutoffScale parameter sample| := by rw [abs_mul]
    _ ≤ 1 * (2 * (Parameters.anchorWidth parameter : ℤ)) + Parameters.anchorWidth parameter :=
      add_le_add (mul_le_mul hsign hoabs (abs_nonneg _) (by norm_num)) hb'
    _ = _ := by ring

end

end AFT.BoundaryCalibration
