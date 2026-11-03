import AFT.ActualSliceMeanProgram
import AFT.ConditionalPairOutput

/-! # Executable actual trimmed endpoint pairs, conditional on the shared source -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics Filter
open scoped BigOperators

/-- The exact integer pair sum fixes the only possible anchor offset. -/
def averagedPairProgram (modulus : ℕ) (boundary start source : ℤ) (width : ℕ)
    (first second : ℕ) : ℚ :=
  let shift : ℤ := (first : ℤ)+second-((modulus : ℤ)-1)
  intervalProbabilityProgram start width (shift+source)*sliceProbabilityProgram modulus boundary shift first

def conditionalBaselineProgram (modulus width mark : ℕ) (coin : Bool) : ℤ :=
  if 2*mark < modulus-1 then -2*(width : ℤ)+1
  else if modulus-1 < 2*mark then width
  else if coin then -2*(width : ℤ)+1 else width

def conditionalPairCoinProgram (constant n mark : ℕ) (source : ℤ) (first second : ℕ)
    (sample : ActualBodyProgramSample constant n) (coin : Bool) : ℚ :=
  averagedPairProgram (ParameterProgram.modulus n).value (actualBoundaryHalfProgram constant n)
    (conditionalBaselineProgram (ParameterProgram.modulus n).value (actualAnchorWidthProgram n) mark coin+
      actualBodyShiftProgram constant n sample)
    source (actualAnchorWidthProgram n) first second

def conditionalPairAtSourceProgram (constant n mark : ℕ) (source : ℤ) (first second : ℕ) : ℚ :=
  ∑ sample : ActualBodyProgramSample constant n,actualBodyBlurProgram constant n sample*
    ((conditionalPairCoinProgram constant n mark source first second sample true+
      conditionalPairCoinProgram constant n mark source first second sample false)/2)

noncomputable section
open scoped Classical Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
local instance conditionalPairProgramFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

theorem averagedPairProgram_cast (modulus : ℕ) (boundary start source : ℤ) (width : ℕ)
    (first second : Fin modulus) :
    (averagedPairProgram modulus boundary start source width first.val second.val : ℝ)=
      TrimmedSlice.averagedPair modulus boundary start source width first second := by
  simp only [averagedPairProgram,Rat.cast_mul,intervalProbabilityProgram_cast,sliceProbabilityProgram_cast,
    TrimmedSlice.averagedPair_formula]

theorem averagedPairProgram_abs_le_one (modulus : ℕ) (boundary start source : ℤ) (width first second : ℕ) :
    |(averagedPairProgram modulus boundary start source width first second : ℝ)| ≤ 1 := by
  simp only [averagedPairProgram,Rat.cast_mul,abs_mul]
  exact (mul_le_mul (intervalProbabilityProgram_abs_le_one _ _ _) (sliceProbabilityProgram_abs_le_one _ _ _ _)
    (abs_nonneg _) (by norm_num)).trans_eq (mul_one _)

theorem conditionalBaselineProgram_eq (modulus width : ℕ) (mark : Fin modulus) (coin : Bool) :
    conditionalBaselineProgram modulus width mark.val coin=conditionalBaselineStart modulus width mark coin := by
  rw [conditionalBaselineStart_formula]
  unfold conditionalBaselineProgram
  split_ifs <;> ring

theorem conditionalPairCoinProgram_cast (constant n : ℕ) (mark first second : Fin (Parameters.modulus n))
    (source : ℤ) (sample : ActualBodyProgramSample constant n) (coin : Bool) :
    (conditionalPairCoinProgram constant n mark.val source first.val second.val sample coin : ℝ)=
      TrimmedSlice.averagedPair (Parameters.modulus n) (boundaryHalf (constant : ℝ) n)
        (conditionalPairStart (constant : ℝ) n mark (actualBodyProgramEquiv constant n sample,coin)) source
        (Parameters.anchorWidth n) first second := by
  unfold conditionalPairCoinProgram
  rw [ParameterProgram.modulus_value,actualBoundaryHalfProgram_eq,actualAnchorWidthProgram_eq,
    conditionalBaselineProgram_eq,actualBodyShiftProgram_eq,averagedPairProgram_cast]
  rfl

/-- This approximation is simultaneous in the primary mark, both endpoints,
and the retained source, so downstream tensors retain their actual shared
source rather than inserting independently averaged copies. -/
theorem conditional_pair_at_source_program_eventually (constant : ℕ) :
    ∀ᶠ n : ℕ in atTop,∀ (mark first second : Fin (Parameters.modulus n)) (source : ℤ),
      |(conditionalPairAtSourceProgram constant n mark.val source first.val second.val : ℝ)-
        conditionalPairAtSource (constant : ℝ) n mark source first second| ≤ actualBodyBlurProgramError n := by
  filter_upwards [actual_body_blur_program_eventually constant] with n hsource mark first second source
  let kernel := fun sample : ActualBodyProgramSample constant n =>
    (conditionalPairCoinProgram constant n mark.val source first.val second.val sample true+
      conditionalPairCoinProgram constant n mark.val source first.val second.val sample false)/2
  have hkernel (sample : ActualBodyProgramSample constant n) : |(kernel sample : ℝ)| ≤ 1 := by
    simp only [kernel,Rat.cast_div,Rat.cast_add,Rat.cast_ofNat,abs_div,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply (div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num : (0 : ℝ) ≤ 2)).trans
    have htrue : |(conditionalPairCoinProgram constant n mark.val source first.val second.val sample true : ℝ)| ≤ 1 :=
      averagedPairProgram_abs_le_one _ _ _ _ _ _ _
    have hfalse : |(conditionalPairCoinProgram constant n mark.val source first.val second.val sample false : ℝ)| ≤ 1 :=
      averagedPairProgram_abs_le_one _ _ _ _ _ _ _
    linarith
  have he := finite_rational_expectation_error (actualBodyBlurProgram constant n)
    (fun sample => (bodyBlur (constant : ℝ) n).weight (actualBodyProgramEquiv constant n sample)) kernel hkernel
  have hsum : (∑ sample : ActualBodyProgramSample constant n,
      (bodyBlur (constant : ℝ) n).weight (actualBodyProgramEquiv constant n sample)*(kernel sample : ℝ))=
      conditionalPairAtSource (constant : ℝ) n mark source first second := by
    simp only [kernel,Rat.cast_div,Rat.cast_add,Rat.cast_ofNat,conditionalPairCoinProgram_cast]
    apply ((actualBodyProgramEquiv constant n).sum_comp (fun sample =>
      (bodyBlur (constant : ℝ) n).weight sample*
        ((TrimmedSlice.averagedPair (Parameters.modulus n) (boundaryHalf (constant : ℝ) n)
          (conditionalPairStart (constant : ℝ) n mark (sample,true)) source (Parameters.anchorWidth n) first second+
          TrimmedSlice.averagedPair (Parameters.modulus n) (boundaryHalf (constant : ℝ) n)
          (conditionalPairStart (constant : ℝ) n mark (sample,false)) source (Parameters.anchorWidth n) first second)/2))).trans
    unfold conditionalPairAtSource TrimmedSlice.mixedPair errorLaw
    simp only [Fintype.sum_prod_type,FiniteDist.prod_weight,FiniteDist.uniform_weight,Fintype.card_bool,
      Nat.cast_ofNat,Fintype.sum_bool]
    apply Finset.sum_congr rfl
    intro sample _
    ring
  rw [hsum] at he
  exact he.trans hsource

end
end AFT.V7Calibration
