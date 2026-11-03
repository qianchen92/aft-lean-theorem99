import AFT.ActualBodyBlurProgram

/-! # Computing the actual safe-body mean from the rational source table -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics Filter
open scoped BigOperators

def actualBodyShiftProgram (constant n : ℕ) (point : ActualBodyProgramSample constant n) : ℤ :=
  point.1.val+(match point.2.1 with | none => 0 | some z => z.val)+
    (match point.2.2 with | none => 0 | some z => z.val)

def intervalProbabilityProgram (start : ℤ) (width : ℕ) (point : ℤ) : ℚ :=
  if point∈anchorInterval start width then (width : ℚ)⁻¹ else 0

def actualSafeMarginProgram (n : ℕ) : ℕ := 20*(max 2 n)^2

def actualSafeSizeProgram (n : ℕ) : ℕ :=
  ((ParameterProgram.modulus n).value-2*actualSafeMarginProgram n)

/-- The complete mean is a sum over a polynomial-size, explicitly computed
integer alphabet. Its only nonrational inputs are erased equality proofs. -/
def actualBodyMeanProgram (constant n : ℕ) (color : ℤ) : ℚ :=
  ∑ sample : ActualBodyProgramSample constant n,actualBodyBlurProgram constant n sample*
    intervalProbabilityProgram (actualSafeMarginProgram n) (actualSafeSizeProgram n)
      (color-actualBodyShiftProgram constant n sample)

noncomputable section
open scoped Topology
set_option backward.isDefEq.respectTransparency false

theorem actualBodyShiftProgram_eq (constant n : ℕ) (point : ActualBodyProgramSample constant n) :
    actualBodyShiftProgram constant n point=bodyShift (constant : ℝ) n (actualBodyProgramEquiv constant n point) := by
  rcases point with ⟨root,leg,queue⟩
  cases leg <;> cases queue <;>
    simp only [actualBodyShiftProgram,actualBodyProgramEquiv_apply,bodyShift,extraShift,
      Option.map_none,Option.map_some,optionalShift,actualLegWindowEquiv,Equiv.coe_fn_mk]
  all_goals ring

theorem intervalProbabilityProgram_cast (start : ℤ) (width : ℕ) (point : ℤ) :
    (intervalProbabilityProgram start width point : ℝ)=intervalAnchorLaw start width point := by
  unfold intervalProbabilityProgram intervalAnchorLaw
  split_ifs <;> simp only [Rat.cast_inv,Rat.cast_natCast,Rat.cast_zero]

theorem intervalProbabilityProgram_abs_le_one (start : ℤ) (width : ℕ) (point : ℤ) :
    |(intervalProbabilityProgram start width point : ℝ)|≤1 := by
  rw [intervalProbabilityProgram_cast,abs_of_nonneg (intervalAnchorLaw_nonneg _ _ _)]
  apply (intervalAnchorLaw_bound _ _ _).trans
  by_cases hw : width=0
  · subst width; norm_num
  have hh : (1 : ℝ)≤width := by exact_mod_cast (show 1≤width by omega)
  exact inv_le_one_of_one_le₀ hh

theorem actualSafeMarginProgram_eq (n : ℕ) : actualSafeMarginProgram n=Parameters.safeMargin n := rfl

theorem actualSafeSizeProgram_eq (n : ℕ) : actualSafeSizeProgram n=Parameters.safeSize n := by
  unfold actualSafeSizeProgram Parameters.safeSize
  rw [ParameterProgram.modulus_value,actualSafeMarginProgram_eq]

private theorem rational_expectation_error {Source : Type*} [Fintype Source]
    (approximate : Source → ℚ) (reference : Source → ℝ) (kernel : Source → ℚ)
    (bound : ℝ) (hbound : ∀ point,|(kernel point : ℝ)|≤bound) :
    |((∑ point,approximate point*kernel point : ℚ) : ℝ)-
      (∑ point,reference point*(kernel point : ℝ))|≤
      bound*(∑ point,|(approximate point : ℝ)-reference point|) := by
  simp only [Rat.cast_sum,Rat.cast_mul,← Finset.sum_sub_distrib,← sub_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro point _
  rw [abs_mul,mul_comm bound]
  exact mul_le_mul_of_nonneg_left (hbound point) (abs_nonneg _)

/-- The exact target is the blurred safe-uniform law in the V7 mean
calibration formula. The estimate is simultaneous for every output color. -/
theorem actual_body_mean_program_eventually (constant : ℕ) :
    ∀ᶠ n : ℕ in atTop,∀ color : ℤ,
      |(actualBodyMeanProgram constant n color : ℝ)-
        TrimmedSlice.blurredSafeLaw (Parameters.modulus n) (Parameters.safeMargin n)
          (bodyShift (constant : ℝ) n) (bodyBlur (constant : ℝ) n).weight color|≤
        actualBodyBlurProgramError n := by
  filter_upwards [actual_body_blur_program_eventually constant] with n hh color
  have he := rational_expectation_error (actualBodyBlurProgram constant n)
    (fun sample => (bodyBlur (constant : ℝ) n).weight (actualBodyProgramEquiv constant n sample))
    (fun sample => intervalProbabilityProgram (actualSafeMarginProgram n) (actualSafeSizeProgram n)
      (color-actualBodyShiftProgram constant n sample)) 1 (fun sample => intervalProbabilityProgram_abs_le_one _ _ _)
  rw [one_mul] at he
  have hwidth : (Parameters.safeSize n : ℕ)=
      ((Parameters.modulus n : ℤ)-2*(Parameters.safeMargin n : ℤ)).toNat := by
    unfold Parameters.safeSize
    omega
  have hsum : (∑ sample : ActualBodyProgramSample constant n,
      (bodyBlur (constant : ℝ) n).weight (actualBodyProgramEquiv constant n sample)*
        (intervalProbabilityProgram (actualSafeMarginProgram n) (actualSafeSizeProgram n)
          (color-actualBodyShiftProgram constant n sample) : ℝ))=
      TrimmedSlice.blurredSafeLaw (Parameters.modulus n) (Parameters.safeMargin n)
        (bodyShift (constant : ℝ) n) (bodyBlur (constant : ℝ) n).weight color := by
    simp only [intervalProbabilityProgram_cast,actualSafeMarginProgram_eq,actualSafeSizeProgram_eq,
      actualBodyShiftProgram_eq,hwidth]
    unfold TrimmedSlice.blurredSafeLaw
    convert (actualBodyProgramEquiv constant n).sum_comp (fun sample =>
      (bodyBlur (constant : ℝ) n).weight sample*
        intervalAnchorLaw (Parameters.safeMargin n)
          ((Parameters.modulus n : ℤ)-2*(Parameters.safeMargin n : ℤ)).toNat
          (color-bodyShift (constant : ℝ) n sample)) using 1
  rw [hsum] at he
  exact he.trans hh

end
end AFT.V7Calibration
