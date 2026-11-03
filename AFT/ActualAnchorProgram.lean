import AFT.ActualPrimaryProgram
import AFT.ActualResponseFormula

/-! # Rational entries of the physical body and root-only anchor matrices -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics Filter
open scoped BigOperators

def publicAnchorStartProgram (modulus width color : ℕ) (coin : Bool) : ℤ :=
  if 2*color < modulus-1 then (modulus : ℤ)-color-2*width
  else if modulus-1 < 2*color then (modulus : ℤ)-1-color+width
  else if coin then (modulus : ℤ)-color-2*width else (modulus : ℤ)-1-color+width

def publicAnchorKernelProgram (modulus width color : ℕ) (output : ℤ) : ℚ :=
  (intervalProbabilityProgram (publicAnchorStartProgram modulus width color true) width output+
    intervalProbabilityProgram (publicAnchorStartProgram modulus width color false) width output)/2

/-- The Boolean selects the root-only compensator. In the other branch it
retains exactly the actual body blur, including both optional shifts. -/
def actualAnchorProgram (constant n : ℕ) (rootOnly : Bool) (color : ℕ) (output : ℤ) : ℚ :=
  ∑ sample : ActualPairProgramSample constant n,actualPairSourceProgram constant n sample*
    publicAnchorKernelProgram (ParameterProgram.modulus n).value (actualAnchorWidthProgram n) color
      (output-(if rootOnly then sample.1.1.val else actualBodyShiftProgram constant n sample.1))

noncomputable section
open scoped Topology
set_option backward.isDefEq.respectTransparency false
local instance anchorProgramFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

theorem publicAnchorStartProgram_eq (modulus width : ℕ) (color : Fin modulus) (coin : Bool) :
    publicAnchorStartProgram modulus width color.val coin=publicAnchorStart modulus width color coin := rfl

theorem publicAnchorKernelProgram_cast (modulus width : ℕ) (color : Fin modulus) (output : ℤ) :
    (publicAnchorKernelProgram modulus width color.val output : ℝ)=publicAnchorKernel modulus width color output := by
  simp only [publicAnchorKernelProgram,Rat.cast_add,Rat.cast_div,Rat.cast_ofNat,
    publicAnchorStartProgram_eq,intervalProbabilityProgram_cast,publicAnchorKernel]

theorem publicAnchorKernelProgram_abs_le_one (modulus width color : ℕ) (output : ℤ) :
    |(publicAnchorKernelProgram modulus width color output : ℝ)|≤1 := by
  simp only [publicAnchorKernelProgram,Rat.cast_add,Rat.cast_div,Rat.cast_ofNat,abs_div,
    abs_of_pos (by norm_num : (0 : ℝ)<2)]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ)<2)).mpr
  apply (abs_add_le _ _).trans
  have hfirst := intervalProbabilityProgram_abs_le_one (publicAnchorStartProgram modulus width color true) width output
  have hsecond := intervalProbabilityProgram_abs_le_one (publicAnchorStartProgram modulus width color false) width output
  linarith

def actualAnchorMatrix (constant : ℝ) (n : ℕ) (rootOnly : Bool)
    (color : Fin (Parameters.modulus n)) (output : ℤ) : ℝ :=
  blurredAnchorKernel (Parameters.modulus n) (Parameters.anchorWidth n)
    (if rootOnly then compensatorRootShift constant n else fun sample => bodyShift constant n sample.1)
    (pairSourceLaw constant n) color output

theorem actual_anchor_program_eventually (constant : ℕ) :
    ∀ᶠ n : ℕ in atTop,∀ (rootOnly : Bool) (color : Fin (Parameters.modulus n)) (output : ℤ),
      |(actualAnchorProgram constant n rootOnly color.val output : ℝ)-
        actualAnchorMatrix (constant : ℝ) n rootOnly color output|≤actualPairSourceProgramError n := by
  filter_upwards [actual_pair_source_program_eventually constant] with n hh rootOnly color output
  let kernel := fun sample : ActualPairProgramSample constant n =>
    publicAnchorKernelProgram (ParameterProgram.modulus n).value (actualAnchorWidthProgram n) color.val
      (output-(if rootOnly then sample.1.1.val else actualBodyShiftProgram constant n sample.1))
  let actualKernel := fun sample : pairSample (constant : ℝ) n =>
    publicAnchorKernel (Parameters.modulus n) (Parameters.anchorWidth n) color
      (output-((if rootOnly then compensatorRootShift (constant : ℝ) n else
        fun sample => bodyShift (constant : ℝ) n sample.1) sample))
  have hk (sample : ActualPairProgramSample constant n) :
      (kernel sample : ℝ)=actualKernel (actualPairProgramEquiv constant n sample) := by
    dsimp only [kernel,actualKernel]
    rw [ParameterProgram.modulus_value,actualAnchorWidthProgram_eq,publicAnchorKernelProgram_cast]
    cases rootOnly
    · simp only [Bool.false_eq_true,if_false,actualPairProgramEquiv_apply,actualBodyShiftProgram_eq]
    · rfl
  have he := finite_rational_expectation_error (actualPairSourceProgram constant n)
    (fun sample => (pairSourceLaw (constant : ℝ) n).weight (actualPairProgramEquiv constant n sample))
    kernel (fun sample => publicAnchorKernelProgram_abs_le_one _ _ _ _)
  have heq : (∑ sample : ActualPairProgramSample constant n,
      (pairSourceLaw (constant : ℝ) n).weight (actualPairProgramEquiv constant n sample)*(kernel sample : ℝ))=
      actualAnchorMatrix (constant : ℝ) n rootOnly color output := by
    simp only [hk]
    change (∑ sample : ActualPairProgramSample constant n,
      (pairSourceLaw (constant : ℝ) n).weight (actualPairProgramEquiv constant n sample)*
        actualKernel (actualPairProgramEquiv constant n sample))=
      ∑ sample : pairSample (constant : ℝ) n,(pairSourceLaw (constant : ℝ) n).weight sample*actualKernel sample
    convert (actualPairProgramEquiv constant n).sum_comp (fun sample =>
      (pairSourceLaw (constant : ℝ) n).weight sample*actualKernel sample) using 1
  rw [heq] at he
  exact he.trans hh

end
end AFT.V7Calibration
