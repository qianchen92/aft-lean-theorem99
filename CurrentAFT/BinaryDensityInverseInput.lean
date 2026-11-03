import CurrentAFT.BinaryDensityInverseProgram

/-! # Executed materialization of arbitrary current density-inverse inputs -/
namespace CurrentAFT.BinaryDensityInverseInput
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryDensityInverseProgram.current

abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

theorem current_of_entries (security bits : ℕ) (input : Vector RationalBits (colors security))
    (profile : ℕ→ℚ) (output : Fin (colors security))
    (hprofile : ∀ color, (input.get color).decode=profile color.val) :
    (BinaryDensityInverseProgram.current security bits input output).data.decode=
      RationalDensityInverseProgram.current security bits profile output.val := by
  rw [BinaryDensityInverseProgram.current_value]
  simp only [RationalDensityInverseProgram.current,RationalFirstResponseProgram.inverse,
    RationalFirstResponseProgram.functional,BinaryFirstInverseProgram.inputAt_value,hprofile]

def current (security bits : ℕ) (profile : Fin (colors security)→RationalResult) (output : Fin (colors security)) : RationalResult :=
  let modulus := PublicParameterProgram.modulus security
  let input := buildArray modulus.count profile
  let result := BinaryDensityInverseProgram.current security bits input.data output
  ⟨result.data,modulus.work+input.work+result.work+4⟩

theorem current_value (security bits : ℕ) (profile : Fin (colors security)→RationalResult)
    (value : ℕ→ℚ) (output : Fin (colors security))
    (hprofile : ∀ color, (profile color).data.decode=value color.val) :
    (current security bits profile output).data.decode=RationalDensityInverseProgram.current security bits value output.val := by
  change (BinaryDensityInverseProgram.current _ _ _ _).data.decode=_
  apply current_of_entries
  intro color
  rw [buildArray_get,hprofile]

noncomputable section
noncomputable def heightPolynomial (precision profileBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryDensityInverseProgram.currentHeightPolynomial precision profileBits
noncomputable def workPolynomial (precision profileBits profileWork : Polynomial ℕ) : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+BinaryFirstInverseProgram.colorsPolynomial*(profileWork+2)+2+
    BinaryDensityInverseProgram.currentWorkPolynomial precision profileBits+4

theorem current_bounds (security : ℕ) (precision profileBits profileWork : Polynomial ℕ)
    (profile : Fin (colors security)→RationalResult) (output : Fin (colors security))
    (hh : ∀ color, HeightBound (profile color).data.decode (profileBits.eval security))
    (hw : ∀ color, (profile color).work≤profileWork.eval security) :
    HeightBound (current security (precision.eval security) profile output).data.decode
      ((heightPolynomial precision profileBits).eval security) ∧
      (current security (precision.eval security) profile output).work≤(workPolynomial precision profileBits profileWork).eval security := by
  let input := buildArray (colors security) profile
  have hinput (color : Fin (colors security)) : HeightBound (input.data.get color).decode (profileBits.eval security) := by
    rw [buildArray_get]
    exact hh color
  have hi := BinaryDensityInverseProgram.current_bounds security precision profileBits input.data output hinput
  have wi := (buildArray_work (colors security) (profileWork.eval security) profile hw).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ (BinaryFirstInverseProgram.colors_bound security)) 2)
  change input.work≤BinaryFirstInverseProgram.colorsPolynomial.eval security*(profileWork.eval security+2)+2 at wi
  have wq := PublicParameterProgram.modulus_work security
  constructor
  · exact hi.1
  · change (PublicParameterProgram.modulus security).work+input.work+
      (BinaryDensityInverseProgram.current security (precision.eval security) input.data output).work+4≤_
    simp only [workPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,PublicParameterProgram.workPolynomial_eval]
    omega

end
end CurrentAFT.BinaryDensityInverseInput
