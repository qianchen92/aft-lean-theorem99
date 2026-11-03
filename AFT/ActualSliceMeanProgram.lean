import AFT.ActualPairSourceProgram
import AFT.ActualBodyMeanProgram

/-! # Rational computation of the actual shared-source endpoint means -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics Filter
open scoped BigOperators

def sliceProbabilityProgram (modulus boundary shift color : ℤ) : ℚ :=
  if color∈TrimmedSlice.slice modulus boundary shift then
    ((TrimmedSlice.slice modulus boundary shift).card : ℚ)⁻¹ else 0

def averagedSliceProgram (modulus boundary start source : ℤ) (width : ℕ) (color : ℤ) : ℚ :=
  ∑ shift∈anchorInterval start width,
    intervalProbabilityProgram start width shift*sliceProbabilityProgram modulus boundary (shift-source) color

def actualBoundaryHalfProgram (constant n : ℕ) : ℤ :=
  (actualSafeMarginProgram n : ℤ)-
    ((3*n^2-1)+(actualLegCutoffProgram constant n-1)+(n^2-1) : ℕ)

def actualAnchorWidthProgram (n : ℕ) : ℕ := (max 2 n)^32

def actualPairStartProgram (constant n : ℕ) (positive : Bool)
    (sample : ActualPairProgramSample constant n) : ℤ :=
  (if positive then (actualAnchorWidthProgram n : ℤ) else -2*(actualAnchorWidthProgram n : ℤ)+1)+
    actualBodyShiftProgram constant n sample.1

def actualMixedSliceProgram (constant n : ℕ) (positive shifted : Bool) (color : ℤ) : ℚ :=
  ∑ sample : ActualPairProgramSample constant n,actualPairSourceProgram constant n sample*
    averagedSliceProgram (ParameterProgram.modulus n).value (actualBoundaryHalfProgram constant n)
      (actualPairStartProgram constant n positive sample)
      (if shifted then sample.2.val else 0) (actualAnchorWidthProgram n) color

def actualFairSliceProgram (constant n : ℕ) (shifted : Bool) (color : ℤ) : ℚ :=
  (actualMixedSliceProgram constant n true shifted color+
    actualMixedSliceProgram constant n false shifted color)/2

noncomputable section
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
local instance sliceProgramFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

theorem sliceProbabilityProgram_cast (modulus boundary shift color : ℤ) :
    (sliceProbabilityProgram modulus boundary shift color : ℝ)=TrimmedSlice.law modulus boundary shift color := by
  unfold sliceProbabilityProgram TrimmedSlice.law
  split_ifs <;> simp only [Rat.cast_inv,Rat.cast_natCast,Rat.cast_zero]

theorem sliceProbabilityProgram_abs_le_one (modulus boundary shift color : ℤ) :
    |(sliceProbabilityProgram modulus boundary shift color : ℝ)|≤1 := by
  unfold sliceProbabilityProgram
  split_ifs with hh
  · simp only [Rat.cast_inv,Rat.cast_natCast]
    rw [abs_of_nonneg (by positivity)]
    apply inv_le_one_of_one_le₀
    exact_mod_cast (Finset.one_le_card.mpr ⟨color,hh⟩)
  · norm_num

theorem averagedSliceProgram_cast (modulus boundary start source : ℤ) (width : ℕ) (color : ℤ) :
    (averagedSliceProgram modulus boundary start source width color : ℝ)=
      TrimmedSlice.averagedLaw modulus boundary start source width color := by
  simp only [averagedSliceProgram,Rat.cast_sum,Rat.cast_mul,intervalProbabilityProgram_cast,
    sliceProbabilityProgram_cast,TrimmedSlice.averagedLaw,TrimmedSlice.intervalMixture]

theorem averagedSliceProgram_abs_le_one (modulus boundary start source : ℤ) (width : ℕ) (color : ℤ) :
    |(averagedSliceProgram modulus boundary start source width color : ℝ)|≤1 := by
  by_cases hw : width=0
  · subst width
    simp [averagedSliceProgram,anchorInterval]
  simp only [averagedSliceProgram,Rat.cast_sum,Rat.cast_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ shift∈anchorInterval start width,intervalAnchorLaw start width shift := by
      apply Finset.sum_le_sum
      intro shift _
      rw [abs_mul,intervalProbabilityProgram_cast,abs_of_nonneg (intervalAnchorLaw_nonneg _ _ _)]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (sliceProbabilityProgram_abs_le_one modulus boundary (shift-source) color)
        (intervalAnchorLaw_nonneg start shift width)
    _ = 1 := intervalAnchorLaw_mass start width hw

theorem actualBoundaryHalfProgram_eq (constant n : ℕ) :
    actualBoundaryHalfProgram constant n=boundaryHalf (constant : ℝ) n := by
  simp only [actualBoundaryHalfProgram,actualSafeMarginProgram_eq,actualLegCutoffProgram_eq,
    boundaryHalf,maxBodyShift,v7RootCutoff,queueCutoff]

theorem actualAnchorWidthProgram_eq (n : ℕ) : actualAnchorWidthProgram n=Parameters.anchorWidth n := rfl

theorem actualPairStartProgram_eq (constant n : ℕ) (positive : Bool)
    (sample : ActualPairProgramSample constant n) :
    actualPairStartProgram constant n positive sample=
      (if positive then startsPlus (constant : ℝ) n else startsMinus (constant : ℝ) n)
        (actualPairProgramEquiv constant n sample) := by
  cases positive <;> simp only [actualPairStartProgram,Bool.false_eq_true,if_false,if_true,
    actualAnchorWidthProgram_eq,actualBodyShiftProgram_eq,actualPairProgramEquiv_apply,
    startsPlus,startsMinus]
  ring

theorem actualPairSourceProgram_shift (constant n : ℕ) (sample : ActualPairProgramSample constant n) :
    sample.2.val=pairSourceShift (constant : ℝ) n (actualPairProgramEquiv constant n sample) := rfl

theorem finite_rational_expectation_error {Source : Type*} [Fintype Source]
    (approximate : Source → ℚ) (reference : Source → ℝ) (kernel : Source → ℚ)
    (hbound : ∀ point,|(kernel point : ℝ)|≤1) :
    |((∑ point,approximate point*kernel point : ℚ) : ℝ)-
      (∑ point,reference point*(kernel point : ℝ))|≤
      ∑ point,|(approximate point : ℝ)-reference point| := by
  simp only [Rat.cast_sum,Rat.cast_mul,← Finset.sum_sub_distrib,← sub_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro point _
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (hbound point)

/-- Each sign and each shifted/unshifted slice is computed using the same
complete pair-source table. The bound is uniform in the output color. -/
theorem actual_mixed_slice_program_eventually (constant : ℕ) :
    ∀ᶠ n : ℕ in atTop,∀ (positive shifted : Bool) (color : ℤ),
      |(actualMixedSliceProgram constant n positive shifted color : ℝ)-
        TrimmedSlice.mixedLaw (Parameters.modulus n) (boundaryHalf (constant : ℝ) n)
          (if positive then startsPlus (constant : ℝ) n else startsMinus (constant : ℝ) n)
          (if shifted then pairSourceShift (constant : ℝ) n else fun _ => 0)
          (pairSourceLaw (constant : ℝ) n).weight (Parameters.anchorWidth n) color|≤
        actualPairSourceProgramError n := by
  filter_upwards [actual_pair_source_program_eventually constant] with n hh positive shifted color
  let kernel := fun sample : ActualPairProgramSample constant n =>
    averagedSliceProgram (ParameterProgram.modulus n).value (actualBoundaryHalfProgram constant n)
      (actualPairStartProgram constant n positive sample)
      (if shifted then sample.2.val else 0) (actualAnchorWidthProgram n) color
  let actualKernel := fun sample : pairSample (constant : ℝ) n =>
    TrimmedSlice.averagedLaw (Parameters.modulus n) (boundaryHalf (constant : ℝ) n)
      ((if positive then startsPlus (constant : ℝ) n else startsMinus (constant : ℝ) n) sample)
      ((if shifted then pairSourceShift (constant : ℝ) n else fun _ => 0) sample)
      (Parameters.anchorWidth n) color
  have hkernel (sample : ActualPairProgramSample constant n) :
      (kernel sample : ℝ)=actualKernel (actualPairProgramEquiv constant n sample) := by
    dsimp only [kernel,actualKernel]
    simp only [averagedSliceProgram_cast,ParameterProgram.modulus_value,actualBoundaryHalfProgram_eq,
      actualPairStartProgram_eq,actualAnchorWidthProgram_eq,actualPairSourceProgram_shift]
    cases shifted <;> rfl
  have he := finite_rational_expectation_error (actualPairSourceProgram constant n)
    (fun sample => (pairSourceLaw (constant : ℝ) n).weight (actualPairProgramEquiv constant n sample))
    kernel (fun sample => averagedSliceProgram_abs_le_one _ _ _ _ _ _)
  have hsum : (∑ sample : ActualPairProgramSample constant n,
      (pairSourceLaw (constant : ℝ) n).weight (actualPairProgramEquiv constant n sample)*(kernel sample : ℝ))=
      TrimmedSlice.mixedLaw (Parameters.modulus n) (boundaryHalf (constant : ℝ) n)
        (if positive then startsPlus (constant : ℝ) n else startsMinus (constant : ℝ) n)
        (if shifted then pairSourceShift (constant : ℝ) n else fun _ => 0)
        (pairSourceLaw (constant : ℝ) n).weight (Parameters.anchorWidth n) color := by
    simp only [hkernel]
    change (∑ sample : ActualPairProgramSample constant n,
      (pairSourceLaw (constant : ℝ) n).weight (actualPairProgramEquiv constant n sample)*
        actualKernel (actualPairProgramEquiv constant n sample))=
      ∑ sample : pairSample (constant : ℝ) n,(pairSourceLaw (constant : ℝ) n).weight sample*actualKernel sample
    convert (actualPairProgramEquiv constant n).sum_comp (fun sample =>
      (pairSourceLaw (constant : ℝ) n).weight sample*actualKernel sample) using 1
  rw [hsum] at he
  exact he.trans hh

theorem actual_fair_slice_program_eventually (constant : ℕ) :
    ∀ᶠ n : ℕ in atTop,∀ (shifted : Bool) (color : ℤ),
      |(actualFairSliceProgram constant n shifted color : ℝ)-
        TrimmedSlice.fairMixedLaw (Parameters.modulus n) (boundaryHalf (constant : ℝ) n)
          (startsPlus (constant : ℝ) n) (startsMinus (constant : ℝ) n)
          (if shifted then pairSourceShift (constant : ℝ) n else fun _ => 0)
          (pairSourceLaw (constant : ℝ) n).weight (Parameters.anchorWidth n) color|≤
        actualPairSourceProgramError n := by
  filter_upwards [actual_mixed_slice_program_eventually constant] with n hh shifted color
  have hp := hh true shifted color
  have hm := hh false shifted color
  simp only [if_true,Bool.false_eq_true,if_false] at hp hm
  simp only [actualFairSliceProgram,Rat.cast_div,Rat.cast_add,Rat.cast_ofNat,
    TrimmedSlice.fairMixedLaw]
  rw [show ∀ a b c d : ℝ,(a+b)/2-(c+d)/2=((a-c)+(b-d))/2 by intros;ring]
  rw [abs_div,abs_of_pos (by norm_num : (0 : ℝ)<2)]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ)<2)).mpr
  exact (abs_add_le _ _).trans ((add_le_add hp hm).trans_eq (by ring))

theorem mixed_slice_abs_le_one {Source : Type*} [Fintype Source]
    (law : FiniteDist Source) (modulus boundary : ℤ) (starts sources : Source → ℤ)
    (width : ℕ) (color : ℤ) :
    |TrimmedSlice.mixedLaw modulus boundary starts sources law.weight width color|≤1 := by
  unfold TrimmedSlice.mixedLaw
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ point,law.weight point := by
      apply Finset.sum_le_sum
      intro point _
      rw [abs_mul,abs_of_nonneg (law.nonneg point)]
      have hh := averagedSliceProgram_abs_le_one modulus boundary (starts point) (sources point) width color
      rw [averagedSliceProgram_cast] at hh
      exact mul_le_of_le_one_right (law.nonneg point) hh
    _ = 1 := law.sum_one

theorem fair_slice_abs_le_one {Source : Type*} [Fintype Source]
    (law : FiniteDist Source) (modulus boundary : ℤ) (startsPlus startsMinus sources : Source → ℤ)
    (width : ℕ) (color : ℤ) :
    |TrimmedSlice.fairMixedLaw modulus boundary startsPlus startsMinus sources law.weight width color|≤1 := by
  unfold TrimmedSlice.fairMixedLaw
  rw [abs_div,abs_of_pos (by norm_num : (0 : ℝ)<2)]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ)<2)).mpr
  have hp := mixed_slice_abs_le_one law modulus boundary startsPlus sources width color
  have hm := mixed_slice_abs_le_one law modulus boundary startsMinus sources width color
  nlinarith [abs_add_le (TrimmedSlice.mixedLaw modulus boundary startsPlus sources law.weight width color)
    (TrimmedSlice.mixedLaw modulus boundary startsMinus sources law.weight width color)]

end
end AFT.V7Calibration
