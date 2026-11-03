import AFT.ConditionalPairOutput

/-! # Actual public anchor averaging of the chart output -/

namespace AFT.V7Calibration

open GaussianSource BoundaryCalibration Filter
open scoped BigOperators Classical Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance publicChartFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
attribute [local instance] actualModulusNeZero

/-- The actual bounded integer interval, pushed through the palette
embedding, is the same literal translated interval law. -/
theorem interval_companion_probability (parameter width : ℕ) (start shift : ℤ)
    (hsafe : ∀ offset ∈ anchorInterval start width,
      0 ≤ offset + shift ∧ offset + shift < Parameters.modulus parameter)
    (output : Fin (Parameters.modulus parameter)) :
    (∑ offset ∈ anchorInterval start width, intervalAnchorLaw start width offset *
      (if output = paletteEmbedding parameter (offset + shift) then 1 else 0)) =
      intervalAnchorLaw (start + shift) width output.val := by
  have hrow (offset : ℤ) (ho : offset ∈ anchorInterval start width) :
      intervalAnchorLaw start width offset * (if output = paletteEmbedding parameter (offset + shift) then 1 else 0) =
        if offset = (output.val : ℤ) - shift then intervalAnchorLaw start width offset else 0 := by
    have heq : output = paletteEmbedding parameter (offset + shift) ↔ offset = (output.val : ℤ) - shift := by
      have hv := paletteEmbedding_val parameter (offset + shift) (hsafe offset ho).1 (hsafe offset ho).2
      constructor
      · intro he
        have hh := congrArg (fun c : Fin (Parameters.modulus parameter) => (c.val : ℤ)) he
        dsimp only at hh
        rw [hv] at hh
        omega
      · intro he
        apply Fin.ext
        exact_mod_cast (show (output.val : ℤ) = ((paletteEmbedding parameter (offset+shift)).val : ℤ) by omega)
    simp only [heq, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_congr rfl hrow, Finset.sum_ite_eq', intervalAnchorLaw_translate]
  by_cases h : (output.val : ℤ) - shift ∈ anchorInterval start width <;>
    simp [h, intervalAnchorLaw]

/-- The baseline law has the same endpoint anchor as the literal public
construction; this equality includes every blur sample and midpoint coin. -/
theorem conditional_marked_anchor (cutoffScale : ℝ) (parameter : ℕ)
    (hblur : (maxBodyShift cutoffScale parameter : ℤ) ≤ Parameters.anchorWidth parameter)
    (mark second : Fin (Parameters.modulus parameter)) (sample : bodySample cutoffScale parameter × Bool) :
    (∑ baseline ∈ anchorInterval (conditionalPairStart cutoffScale parameter mark sample) (Parameters.anchorWidth parameter),
      intervalAnchorLaw (conditionalPairStart cutoffScale parameter mark sample) (Parameters.anchorWidth parameter) baseline *
        (if second = paletteEmbedding parameter ((Parameters.modulus parameter : ℤ) - 1 + baseline - mark.val) then 1 else 0)) =
      intervalAnchorLaw (publicAnchorStart (Parameters.modulus parameter) (Parameters.anchorWidth parameter) mark sample.2)
        (Parameters.anchorWidth parameter) ((second.val : ℤ) - bodyShift cutoffScale parameter sample.1) := by
  have hstart : conditionalPairStart cutoffScale parameter mark sample + ((Parameters.modulus parameter : ℤ) - 1 - mark.val) =
      publicAnchorStart (Parameters.modulus parameter) (Parameters.anchorWidth parameter) mark sample.2 +
        bodyShift cutoffScale parameter sample.1 := by unfold conditionalPairStart conditionalBaselineStart; ring
  have hshift (baseline : ℤ) : (Parameters.modulus parameter : ℤ) - 1 + baseline - mark.val =
      baseline + ((Parameters.modulus parameter : ℤ) - 1 - mark.val) := by ring
  simp_rw [hshift]
  rw [interval_companion_probability parameter (Parameters.anchorWidth parameter)
    (conditionalPairStart cutoffScale parameter mark sample) ((Parameters.modulus parameter : ℤ) - 1 - mark.val)]
  · rw [hstart, intervalAnchorLaw_translate]
  · intro offset ho
    apply publicAnchorStart_safe _ _ mark sample.2 (bodyShift cutoffScale parameter sample.1) 0
      (Parameters.anchor_clearance parameter)
      (by simpa only [zero_add] using (bodyShift_abs_le cutoffScale parameter sample.1).trans hblur)
    have hh : offset + ((Parameters.modulus parameter : ℤ) - 1 - mark.val) ∈
        anchorInterval (conditionalPairStart cutoffScale parameter mark sample + ((Parameters.modulus parameter : ℤ) - 1 - mark.val))
          (Parameters.anchorWidth parameter) := by
      simp only [anchorInterval, Finset.mem_Ico] at ho ⊢
      omega
    simpa only [hstart, sub_zero] using hh

/-- The actual conditional marked companion, averaged over the complete
public body blur and midpoint coin, is the established anchor kernel. -/
theorem public_marked_anchor_average (cutoffScale : ℝ) (parameter : ℕ)
    (hblur : (maxBodyShift cutoffScale parameter : ℤ) ≤ Parameters.anchorWidth parameter)
    (mark second : Fin (Parameters.modulus parameter)) :
    (∑ sample, (errorLaw (bodyBlur cutoffScale parameter)).weight sample *
      (∑ baseline ∈ anchorInterval (conditionalPairStart cutoffScale parameter mark sample) (Parameters.anchorWidth parameter),
        intervalAnchorLaw (conditionalPairStart cutoffScale parameter mark sample) (Parameters.anchorWidth parameter) baseline *
          (if second = paletteEmbedding parameter ((Parameters.modulus parameter : ℤ) - 1 + baseline - mark.val) then 1 else 0))) =
      blurredAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
        (bodyShift cutoffScale parameter) (bodyBlur cutoffScale parameter) mark second.val := by
  simp_rw [conditional_marked_anchor cutoffScale parameter hblur]
  simp only [errorLaw, Fintype.sum_prod_type, FiniteDist.prod_weight, FiniteDist.uniform_weight,
    Fintype.card_bool, Nat.cast_ofNat, Fintype.sum_bool, blurredAnchorKernel, publicAnchorKernel]
  apply Finset.sum_congr rfl
  intro sample _
  ring

end
end AFT.V7Calibration
