import AFT.ActualBodySampleProgram
import AFT.ActualAnchorProgram
import AFT.PublicChartGaussian
import AFT.RationalPaletteSampler

/-! # Exact integer public offsets and their finite-bit interval sampler -/
namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration RationalNumerics RationalPaletteSampler Filter
open scoped BigOperators

 def anchorIndexEquiv (start : ℤ) (width : ℕ) : Fin width≃{value : ℤ // value∈anchorInterval start width} where
  toFun index := ⟨start+index.val,by simp only [anchorInterval,Finset.mem_Ico];constructor <;> omega⟩
  invFun point := ⟨(point.val-start).toNat,by have hh := point.property;simp only [anchorInterval,Finset.mem_Ico] at hh;omega⟩
  left_inv index := by ext;simp only;omega
  right_inv point := by ext;simp only;have hh := point.property;simp only [anchorInterval,Finset.mem_Ico] at hh;omega

 def bodyShiftIntegerProgram (constant n : ℕ) (point : bodySample (constant : ℝ) n) : ℤ :=
  point.1.val+(match point.2.1 with | none => 0 | some z => z.val)+
    (match point.2.2 with | none => 0 | some z => z.val)

 def actualPublicBaselineProgram (constant n : ℕ) (mark : Fin (Parameters.modulus n))
    (sample : bodySample (constant : ℝ) n × Bool) : ℤ :=
  publicAnchorStartProgram (ParameterProgram.modulus n).value (actualAnchorWidthProgram n) mark.val sample.2+
    mark.val-((ParameterProgram.modulus n).value-1 : ℤ)+bodyShiftIntegerProgram constant n sample.1

 theorem actualPublicBaselineProgram_eq (constant n : ℕ) (mark : Fin (Parameters.modulus n))
    (sample : bodySample (constant : ℝ) n × Bool) :
    actualPublicBaselineProgram constant n mark sample=conditionalPairStart (constant : ℝ) n mark sample := by
  simp only [actualPublicBaselineProgram,ParameterProgram.modulus_value,actualAnchorWidthProgram_eq,publicAnchorStartProgram_eq,
    conditionalPairStart,conditionalBaselineStart]
  congr 1
  rcases sample.1 with ⟨root,leg,queue⟩
  cases leg <;> cases queue <;> simp only [bodyShiftIntegerProgram,bodyShift,extraShift,optionalShift]
  all_goals ring

 theorem actualAnchorWidthProgram_positive (n : ℕ) : 0<actualAnchorWidthProgram n := by
   unfold actualAnchorWidthProgram
   have : 2 ≤ max 2 n := le_max_left _ _
   positivity

 def actualPublicOffsetDraw (constant n : ℕ) (mark : Fin (Parameters.modulus n))
    (sample : bodySample (constant : ℝ) n × Bool) (bits : ℕ)
    (word : Fin (bits+actualAnchorWidthProgram n+1) → Fin 2) : PublicOffsets (constant : ℝ) n mark sample :=
  let index := draw (actualAnchorWidthProgram n) (actualAnchorWidthProgram_positive n)
    (fun _ => (actualAnchorWidthProgram n : ℚ)⁻¹) bits word
  ⟨actualPublicBaselineProgram constant n mark sample+index.val,by
    rw [actualPublicBaselineProgram_eq]
    have hi : index.val<Parameters.anchorWidth n := index.isLt.trans_eq (actualAnchorWidthProgram_eq n)
    simp only [anchorInterval,Finset.mem_Ico]
    constructor <;> omega⟩

noncomputable section
open scoped Classical Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

 def actualPublicOffsetEquiv (constant n : ℕ) (mark : Fin (Parameters.modulus n))
    (sample : bodySample (constant : ℝ) n × Bool) : Fin (actualAnchorWidthProgram n)≃PublicOffsets (constant : ℝ) n mark sample :=
  (finCongr (actualAnchorWidthProgram_eq n)).trans (anchorIndexEquiv (conditionalPairStart (constant : ℝ) n mark sample) (Parameters.anchorWidth n))

 theorem actualPublicOffsetDraw_eq (constant n : ℕ) (mark : Fin (Parameters.modulus n))
    (sample : bodySample (constant : ℝ) n × Bool) (bits : ℕ) :
    actualPublicOffsetDraw constant n mark sample bits=
      (fun word => actualPublicOffsetEquiv constant n mark sample
        (draw (actualAnchorWidthProgram n) (actualAnchorWidthProgram_positive n)
          (fun _ => (actualAnchorWidthProgram n : ℚ)⁻¹) bits word)) := by
  funext word
  apply Subtype.ext
  simp only [actualPublicOffsetDraw,actualPublicOffsetEquiv,Equiv.trans_apply,finCongr_apply,anchorIndexEquiv,Equiv.coe_fn_mk,Fin.val_cast,
    actualPublicBaselineProgram_eq]

 theorem actualPublicOffsetEquiv_uniform (constant n : ℕ) (mark : Fin (Parameters.modulus n))
    (sample : bodySample (constant : ℝ) n × Bool) :
    (by
      letI : NeZero (actualAnchorWidthProgram n) := ⟨(actualAnchorWidthProgram_positive n).ne'⟩
      exact (FiniteDist.uniform (Fin (actualAnchorWidthProgram n))).map (actualPublicOffsetEquiv constant n mark sample))=
      publicOffsetLaw (constant : ℝ) n mark sample := by
  letI : NeZero (actualAnchorWidthProgram n) := ⟨(actualAnchorWidthProgram_positive n).ne'⟩
  ext point
  rw [FiniteDist.map_equiv_weight]
  simp only [FiniteDist.uniform_weight,Fintype.card_fin,actualAnchorWidthProgram_eq,publicOffsetLaw,
    intervalAnchorLaw,if_pos point.property]

 theorem actualPublicOffsetDraw_l1 (constant n : ℕ) (mark : Fin (Parameters.modulus n))
    (sample : bodySample (constant : ℝ) n × Bool) (bits : ℕ) :
    (∑ offset,|((FiniteDist.uniform (Fin (bits+actualAnchorWidthProgram n+1) → Fin 2)).map
      (actualPublicOffsetDraw constant n mark sample bits)).weight offset-(publicOffsetLaw (constant : ℝ) n mark sample).weight offset|)≤1/(2 : ℝ)^bits := by
  letI : NeZero (actualAnchorWidthProgram n) := ⟨(actualAnchorWidthProgram_positive n).ne'⟩
  have hd := draw_l1 (actualAnchorWidthProgram n) (actualAnchorWidthProgram_positive n)
    (fun _ => (actualAnchorWidthProgram n : ℚ)⁻¹) bits (FiniteDist.uniform (Fin (actualAnchorWidthProgram n))) 0
    (by simp only [Rat.cast_inv,Rat.cast_natCast,FiniteDist.uniform_weight,Fintype.card_fin,sub_self,abs_zero,Finset.sum_const_zero,le_refl])
    (by norm_num)
  simp only [mul_zero,add_zero] at hd
  have hm := FiniteDist.l1_map_le
    ((FiniteDist.uniform (Fin (bits+actualAnchorWidthProgram n+1) → Fin 2)).map
      (draw (actualAnchorWidthProgram n) (actualAnchorWidthProgram_positive n) (fun _ => (actualAnchorWidthProgram n : ℚ)⁻¹) bits))
    (FiniteDist.uniform (Fin (actualAnchorWidthProgram n))) (actualPublicOffsetEquiv constant n mark sample)
  rw [actualPublicOffsetEquiv_uniform,FiniteDist.map_map,←actualPublicOffsetDraw_eq] at hm
  exact hm.trans hd

end
end AFT.V7Calibration
