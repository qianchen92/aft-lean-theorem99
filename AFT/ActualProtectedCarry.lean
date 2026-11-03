import AFT.ChartCarry
import AFT.ActualPhysicalMean

/-! # Uniform carry correctness on the actual protected public sampler -/
namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
attribute [local instance] actualModulusNeZero

/-- The true public anchor interval makes the marked companion an ordinary
integer palette element, including the midpoint coin and complete body blur. -/
theorem public_marked_baseline_safe (C : ℝ) (n : ℕ)
    (hblur : (maxBodyShift C n : ℤ) ≤ Parameters.anchorWidth n)
    (mark : Fin (Parameters.modulus n)) (sample : bodySample C n × Bool)
    (offset : PublicOffsets C n mark sample) :
    0 ≤ (Parameters.modulus n : ℤ)-1+offset-mark.val ∧
      (Parameters.modulus n : ℤ)-1+offset-mark.val < Parameters.modulus n := by
  apply publicAnchorStart_safe _ _ mark sample.2 (bodyShift C n sample.1) 0
    (Parameters.anchor_clearance n)
    (by simpa only [zero_add] using (bodyShift_abs_le C n sample.1).trans hblur)
  have hh := offset.property
  simp only [anchorInterval,Finset.mem_Ico,conditionalPairStart,conditionalBaselineStart] at hh ⊢
  constructor <;> omega

/-- One and the same positive chart family has the exact source-dependent
response, nonzero affine scale, and cancelling carries at every protected input. -/
theorem actual_public_chart_carry_eventually (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ n in atTop,∀ mark : Fin (Parameters.modulus n),
      ∃ charts : PublicChartFamily C n mark,
      (∀ (attached : Window (legCutoff C n-1) → ℝ) (first second : Fin (Parameters.modulus n)),
        publicChartRaw C n mark charts attached first second=conditionalJointOutput C n mark attached first second) ∧
      ∀ (sample : bodySample C n × Bool) (offset : PublicOffsets C n mark sample)
        (chart : Chart (ZMod (Parameters.modulus n))),
        (charts sample offset).weight chart ≠ 0 → chart.2.1 ≠ 0 ∧
        ∀ input : V7Input C n,
          chartIntegerLoad chart input.1 input.2/(Parameters.modulus n : ℤ)+
            ((Parameters.modulus n : ℤ)-1+offset-input.2-chartIntegerLoad chart input.1 input.2)/
              (Parameters.modulus n : ℤ)=0 := by
  filter_upwards [public_chart_supported_eventually C hC,body_support_scales_eventually C hC]
    with n hc hs mark
  obtain ⟨charts,hsupport,hresponse⟩ := hc mark
  refine ⟨charts,hresponse,?_⟩
  intro sample offset chart hchart
  exact protected_chart_carry C n (boundaryHalf C n) offset hs.2.2.1 mark (charts sample offset)
    (hsupport sample offset) (public_marked_baseline_safe C n (by exact_mod_cast hs.2.1) mark sample offset) chart hchart

/-- Every safe body center has zero carry throughout its genuine bounded shift. -/
theorem safe_body_carry (n : ℕ) (center : Fin (Parameters.modulus n)) (hc : center ∈ safePalette n)
    (shift : ℤ) (hs : |shift| ≤ (Parameters.safeMargin n : ℤ)) :
    ((center.val : ℤ)+shift)/(Parameters.modulus n : ℤ)=0 := by
  have hh := (Finset.mem_filter.mp hc).2
  change (center.val : ℤ) ∈ TrimmedSlice.slice _ _ _ at hh
  rw [TrimmedSlice.mem_slice] at hh
  obtain ⟨hs0,hs1⟩ := abs_le.mp hs
  apply Int.ediv_eq_zero_of_lt <;> omega

/-- Root, retained leg source and the shared queue are simultaneously
covered by the actual safety margin; no coordinate independence is needed. -/
theorem actual_protected_body_carry_eventually (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ n in atTop,∀ center : Fin (Parameters.modulus n),center ∈ safePalette n →
      ∀ root queue : ℤ,|root| ≤ (v7RootCutoff n : ℤ) → |queue| ≤ (queueCutoff n : ℤ) →
      ∀ source : Option (Window (legCutoff C n-1)),
        ((center.val : ℤ)+root+optionalShift source+queue)/(Parameters.modulus n : ℤ)=0 := by
  filter_upwards [body_support_scales_eventually C hC] with n hs center hc root queue hr hq source
  have hb : |root+optionalShift source+queue| ≤ (maxBodyShift C n : ℤ) := by
    cases source with
    | none => exact actualBodyBranch_shift_bound C n root queue hr hq (.inl ())
    | some value => exact actualBodyBranch_shift_bound C n root queue hr hq (.inr value)
  have hm : (maxBodyShift C n : ℤ) ≤ Parameters.safeMargin n := by exact_mod_cast hs.1
  have hh := safe_body_carry n center hc (root+optionalShift source+queue) (hb.trans hm)
  simpa only [add_assoc] using hh

end
end AFT.V7Calibration
