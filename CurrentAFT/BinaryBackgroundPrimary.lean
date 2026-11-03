import CurrentAFT.BinaryBackgroundDeviation
import CurrentAFT.BinaryMassLiftInput

/-! # Full binary production of the original free primary-certificate density -/
namespace CurrentAFT.BinaryBackgroundPrimary
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryBackgroundDeviation.current BinaryMassLiftInput.current

def point (security bits : ℕ) (color : Fin (BinaryFirstInverseProgram.colors security)) : RationalResult :=
  let code := canonicalCounter color.val
  let result := BinaryBackgroundDeviation.current security bits code.digits
  ⟨result.data, code.work+result.work+2⟩

theorem point_value (security bits : ℕ) (color : Fin (BinaryFirstInverseProgram.colors security)) :
    (point security bits color).data.decode = RationalBackgroundProfiles.bodyDeviation security bits color.val := by
  simp only [point, BinaryBackgroundDeviation.current_value, canonicalCounter_value]

def current (security bits : ℕ) (output : Fin (BinaryFirstInverseProgram.colors security)) : RationalResult :=
  BinaryMassLiftInput.current security bits (point security bits) output

theorem current_value (security bits : ℕ) (output : Fin (BinaryFirstInverseProgram.colors security)) :
    (current security bits output).data.decode = RationalBackgroundDensities.primary security bits output.val :=
  BinaryMassLiftInput.current_value security bits (point security bits)
    (RationalBackgroundProfiles.bodyDeviation security bits) output (point_value security bits)

noncomputable section
noncomputable def pointHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryBackgroundDeviation.heightPolynomial precision BinaryFirstInverseProgram.colorsPolynomial
noncomputable def pointWorkPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  50*(BinaryFirstInverseProgram.colorsPolynomial+1)^2+
    BinaryBackgroundDeviation.workPolynomial precision BinaryFirstInverseProgram.colorsPolynomial+2
noncomputable def heightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryMassLiftInput.heightPolynomial precision (pointHeightPolynomial precision)
noncomputable def workPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryMassLiftInput.workPolynomial precision (pointHeightPolynomial precision) (pointWorkPolynomial precision)

theorem point_bounds (security : ℕ) (precision : Polynomial ℕ) (color : Fin (BinaryFirstInverseProgram.colors security)) :
    HeightBound (point security (precision.eval security) color).data.decode ((pointHeightPolynomial precision).eval security) ∧
      (point security (precision.eval security) color).work ≤ (pointWorkPolynomial precision).eval security := by
  have hc : color.val ≤ BinaryFirstInverseProgram.colorsPolynomial.eval security :=
    color.isLt.le.trans (BinaryFirstInverseProgram.colors_bound security)
  have hl : (canonicalCounter color.val).digits.length ≤ BinaryFirstInverseProgram.colorsPolynomial.eval security := by
    rw [canonicalCounter_length]
    exact (Nat.size_le.mpr (Nat.lt_two_pow_self (n := color.val))).trans hc
  have h := BinaryBackgroundDeviation.current_bounds security precision BinaryFirstInverseProgram.colorsPolynomial
    (canonicalCounter color.val).digits hl
  constructor
  · exact h.1
  · have w := (canonicalCounter_work color.val).trans
      (Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (Nat.add_le_add_right hc 1) 2))
    change _+_+2 ≤ _
    simp only [pointWorkPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_ofNat, Polynomial.eval_one]
    omega

theorem current_bounds (security : ℕ) (precision : Polynomial ℕ) (output : Fin (BinaryFirstInverseProgram.colors security)) :
    HeightBound (current security (precision.eval security) output).data.decode ((heightPolynomial precision).eval security) ∧
      (current security (precision.eval security) output).work ≤ (workPolynomial precision).eval security :=
  BinaryMassLiftInput.current_bounds security precision (pointHeightPolynomial precision) (pointWorkPolynomial precision)
    (point security (precision.eval security)) output (fun color => (point_bounds security precision color).1)
    (fun color => (point_bounds security precision color).2)

end
end CurrentAFT.BinaryBackgroundPrimary
