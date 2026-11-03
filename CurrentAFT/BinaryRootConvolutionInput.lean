import CurrentAFT.BinaryRootConvolutionResources
import CurrentAFT.RationalRootConvolutionCongr

/-! # Materialized local profiles for the true binary root convolution -/
namespace CurrentAFT.BinaryRootConvolutionInput
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryRootConvolution.current

abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def current (security bits : ℕ) (profile : Fin (colors security) → RationalResult) (output : List Bool) : RationalResult :=
  let modulus := PublicParameterProgram.modulus security
  let input := buildArray modulus.count profile
  let result := BinaryRootConvolution.current security bits input.data output
  ⟨result.data,modulus.work+input.work+result.work+4⟩

theorem current_value (security bits : ℕ) (profile : Fin (colors security) → RationalResult)
    (value : ℕ → ℚ) (output : List Bool)
    (hprofile : ∀ color, (profile color).data.decode=value color.val) :
    (current security bits profile output).data.decode=
      RationalBackgroundProfiles.convolution security bits value (BinaryArithmetic.value output) := by
  change (BinaryRootConvolution.current _ _ _ _).data.decode=_
  apply BinaryRootConvolution.current_of_entries
  intro color
  rw [buildArray_get,hprofile]

noncomputable section
noncomputable def heightPolynomial (precision inputBits profileBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryRootConvolution.heightPolynomial precision inputBits profileBits
noncomputable def workPolynomial (precision inputBits profileBits profileWork : Polynomial ℕ) : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+BinaryFirstInverseProgram.colorsPolynomial*(profileWork+2)+2+
    BinaryRootConvolution.workPolynomial precision inputBits profileBits+4

theorem current_bounds (security : ℕ) (precision inputBits profileBits profileWork : Polynomial ℕ)
    (profile : Fin (colors security) → RationalResult) (output : List Bool)
    (ho : output.length ≤ inputBits.eval security)
    (hh : ∀ color, HeightBound (profile color).data.decode (profileBits.eval security))
    (hw : ∀ color, (profile color).work ≤ profileWork.eval security) :
    HeightBound (current security (precision.eval security) profile output).data.decode
      ((heightPolynomial precision inputBits profileBits).eval security) ∧
    (current security (precision.eval security) profile output).work ≤
      (workPolynomial precision inputBits profileBits profileWork).eval security := by
  let input := buildArray (colors security) profile
  have hinput (color : Fin (colors security)) : HeightBound (input.data.get color).decode (profileBits.eval security) := by
    rw [buildArray_get]; exact hh color
  have hi := BinaryRootConvolution.current_bounds security precision inputBits profileBits input.data output ho hinput
  have wi := (buildArray_work (colors security) (profileWork.eval security) profile hw).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ (BinaryFirstInverseProgram.colors_bound security)) 2)
  change input.work ≤ BinaryFirstInverseProgram.colorsPolynomial.eval security*(profileWork.eval security+2)+2 at wi
  have wq := PublicParameterProgram.modulus_work security
  constructor
  · exact hi.1
  · change (PublicParameterProgram.modulus security).work+input.work+
      (BinaryRootConvolution.current security (precision.eval security) input.data output).work+4 ≤ _
    simp only [workPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
    rw [PublicParameterProgram.workPolynomial_eval]
    omega

end
end CurrentAFT.BinaryRootConvolutionInput
