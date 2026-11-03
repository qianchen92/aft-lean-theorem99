import CurrentAFT.BinaryMassLiftColumn
import CurrentAFT.BinaryDensityInverseProgram

/-! Actual binary columns of the density inverse, including the complete
stored delta input and its primary-reference conjugation. -/
namespace CurrentAFT.BinaryDensityInverseColumn
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits BinaryMassLiftColumn
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryDensityInverseProgram.current PublicParameterProgram.modulus

def current (security bits : ℕ) (source output : Fin (BinaryFirstInverseProgram.colors security)) : RationalResult :=
  let input := delta source
  let result := BinaryDensityInverseProgram.current security bits input.data output
  ⟨result.data, input.work+result.work+3⟩

theorem current_value (security bits : ℕ) (source output : Fin (BinaryFirstInverseProgram.colors security)) :
    (current security bits source output).data.decode =
      RationalDensityInverseProgram.current security bits (fun color => if color=source.val then 1 else 0) output.val := by
  change (BinaryDensityInverseProgram.current _ _ _ _).data.decode = _
  rw [BinaryDensityInverseProgram.current_value, delta_inputAt]

noncomputable section
noncomputable def heightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryDensityInverseProgram.currentHeightPolynomial precision 1
noncomputable def workPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  let Q := BinaryFirstInverseProgram.colorsPolynomial
  Q*(12*Q+9)+2+BinaryDensityInverseProgram.currentWorkPolynomial precision 1+3

theorem current_bounds (security : ℕ) (precision : Polynomial ℕ)
    (source output : Fin (BinaryFirstInverseProgram.colors security)) :
    HeightBound (current security (precision.eval security) source output).data.decode
      ((heightPolynomial precision).eval security) ∧
      (current security (precision.eval security) source output).work ≤ (workPolynomial precision).eval security := by
  have hd (color : Fin (BinaryFirstInverseProgram.colors security)) :
      HeightBound ((delta source).data.get color).decode ((1:Polynomial ℕ).eval security) := by
    rw [delta, buildArray_get]
    simpa only [Polynomial.eval_one] using point_height source color
  have hi := BinaryDensityInverseProgram.current_bounds security precision 1 (delta source).data output hd
  have wd := buildArray_work (BinaryFirstInverseProgram.colors security)
    (12*BinaryFirstInverseProgram.colors security+7) (point source) (point_work source)
  constructor
  · exact hi.1
  · change _+_+3 ≤ _
    have hq := BinaryFirstInverseProgram.colors_bound security
    have wdelta : (delta source).work ≤ BinaryFirstInverseProgram.colorsPolynomial.eval security*
        (12*BinaryFirstInverseProgram.colorsPolynomial.eval security+9)+2 := by
      apply wd.trans
      gcongr
    simp only [workPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat]
    omega

end
end CurrentAFT.BinaryDensityInverseColumn
