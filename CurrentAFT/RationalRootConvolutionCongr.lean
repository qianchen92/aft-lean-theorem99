import CurrentAFT.BinaryRootConvolutionResources

/-! # The finite palette support of the actual root convolution -/
namespace CurrentAFT.RationalBackgroundProfiles
open AFT RationalNumerics
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus

theorem inverseShift_lt (security output : ℕ) (shift : ℤ) : inverseShift security shift output<colors security := by
  have hq : 0<colors security := by
    rw [colors, PublicParameterProgram.modulus_value]
    exact (Parameters.modulus_spec security).2.pos
  have hqz : (0:ℤ)<colors security := by exact_mod_cast hq
  have h0 := Int.emod_nonneg ((output:ℤ)-shift) (ne_of_gt hqz)
  have h1 := Int.emod_lt_of_pos ((output:ℤ)-shift) hqz
  unfold inverseShift
  omega

theorem convolution_congr (security bits output : ℕ) (first second : ℕ→ℚ)
    (h : ∀ color : Fin (colors security), first color.val=second color.val) :
    convolution security bits first output=convolution security bits second output := by
  unfold convolution RationalProposalProgram.seedEvaluate
  apply Finset.sum_congr rfl
  intro seed _
  exact congrArg (fun entry : ℚ => RationalProposalProgram.seedWeight security bits seed*entry)
    (h ⟨inverseShift security (seed.1.1.val-seed.1.2.val) output,
      inverseShift_lt security output (seed.1.1.val-seed.1.2.val)⟩)

end CurrentAFT.RationalBackgroundProfiles

namespace CurrentAFT.BinaryRootConvolution
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits

theorem current_of_entries (security bits : ℕ)
    (table : Vector RationalBits (BinaryFirstInverseProgram.colors security)) (output : List Bool)
    (profile : ℕ→ℚ) (h : ∀ color, (table.get color).decode=profile color.val) :
    (current security bits table output).data.decode=RationalBackgroundProfiles.convolution security bits profile (value output) := by
  rw [current_value]
  apply RationalBackgroundProfiles.convolution_congr
  intro color
  simp only [BinaryRootConvolutionKernel.profile, dif_pos color.isLt]
  exact h color

end CurrentAFT.BinaryRootConvolution
