import CurrentAFT.BinaryFirstInverseResources
import CurrentAFT.RationalBackgroundDensities

/-! # The actual body-minus-uniform profile produced on binary data -/
namespace CurrentAFT.BinaryBackgroundDeviation
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryBodyProgram.current

def current (security bits : ℕ) (output : List Bool) : RationalResult :=
  let modulus := PublicParameterProgram.modulus security
  let encoded := ofCounter modulus.count
  let reference := BinaryBodyProgram.current security bits false output
  let reciprocal := RationalBits.inverse encoded.data
  let negative := RationalBits.negate reciprocal.data
  let result := RationalBits.add reference.data negative.data
  ⟨result.data, modulus.work+encoded.work+reference.work+reciprocal.work+negative.work+result.work+6⟩

theorem current_value (security bits : ℕ) (output : List Bool) :
    (current security bits output).data.decode = RationalBackgroundProfiles.bodyDeviation security bits (value output) := by
  simp only [current, RationalBits.add_value, RationalBits.negate_value, inverse_value, ofCounter_value,
    BinaryBodyProgram.current_value, RationalBackgroundProfiles.bodyDeviation, RationalBackgroundProfiles.colors,
    one_div, sub_eq_add_neg]

noncomputable section
noncomputable def operandHeightPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFirstInverseProgram.colorsPolynomial+BinaryBodyProgram.currentHeightPolynomial precision inputBits
noncomputable def heightPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  2*operandHeightPolynomial precision inputBits+1
noncomputable def workPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+60*(BinaryFirstInverseProgram.colorsPolynomial+1)^2+
    BinaryBodyProgram.currentWorkPolynomial precision inputBits+
    3*primitiveWorkPolynomial (operandHeightPolynomial precision inputBits)+6

theorem current_bounds (security : ℕ) (precision inputBits : Polynomial ℕ) (output : List Bool)
    (ho : output.length ≤ inputBits.eval security) :
    HeightBound (current security (precision.eval security) output).data.decode ((heightPolynomial precision inputBits).eval security) ∧
      (current security (precision.eval security) output).work ≤ (workPolynomial precision inputBits).eval security := by
  let q := PublicParameterProgram.modulus security
  let encoded := ofCounter q.count
  let reference := BinaryBodyProgram.current security (precision.eval security) false output
  let reciprocal := RationalBits.inverse encoded.data
  let negative := RationalBits.negate reciprocal.data
  let H := (operandHeightPolynomial precision inputBits).eval security
  have hq : q.count ≤ BinaryFirstInverseProgram.colorsPolynomial.eval security := BinaryFirstInverseProgram.colors_bound security
  have hqH : q.count ≤ H := by
    simp only [H, operandHeightPolynomial, Polynomial.eval_add]
    omega
  have hrH : (BinaryBodyProgram.currentHeightPolynomial precision inputBits).eval security ≤ H := by
    simp only [H, operandHeightPolynomial, Polynomial.eval_add]
    omega
  have hencoded : HeightBound encoded.data.decode H := by
    rw [ofCounter_value]
    exact (HeightBound.nat_coarse q.count).mono hqH
  have hreference : HeightBound reference.data.decode H :=
    (BinaryBodyProgram.current_height security false output precision inputBits ho).mono hrH
  have hreciprocal : HeightBound reciprocal.data.decode H := by rw [inverse_value]; exact hencoded.inv
  have hnegative : HeightBound negative.data.decode H := by rw [RationalBits.negate_value]; exact hreciprocal.neg
  have wq := PublicParameterProgram.modulus_work security
  have we : encoded.work ≤ 60*(BinaryFirstInverseProgram.colorsPolynomial.eval security+1)^2 :=
    (ofCounter_work q.count).trans (Nat.mul_le_mul_left 60 (Nat.pow_le_pow_left (Nat.add_le_add_right hq 1) 2))
  have wr := BinaryBodyProgram.current_polynomial_work security false output precision inputBits ho
  change reference.work ≤ _ at wr
  have wi := RationalBits.inverse_work encoded.data H
  have wn := RationalBits.negate_work reciprocal.data H
  have wa := RationalBits.add_work reference.data negative.data H hreference hnegative
  change q.work ≤ PublicParameterProgram.workBound security at wq
  change reciprocal.work ≤ primitiveWorkBound H at wi
  change negative.work ≤ primitiveWorkBound H at wn
  constructor
  · change HeightBound (RationalBits.add reference.data negative.data).data.decode _
    rw [RationalBits.add_value]
    simpa only [heightPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one]
      using (hreference.add hnegative).mono (show H+H+1≤2*H+1 by omega)
  · change q.work+encoded.work+reference.work+reciprocal.work+negative.work+
      (RationalBits.add reference.data negative.data).work+6 ≤ _
    simp only [workPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_ofNat, Polynomial.eval_one, primitiveWorkPolynomial_eval]
    rw [PublicParameterProgram.workPolynomial_eval]
    change _ ≤ PublicParameterProgram.workBound security+60*(BinaryFirstInverseProgram.colorsPolynomial.eval security+1)^2+
      (BinaryBodyProgram.currentWorkPolynomial precision inputBits).eval security+3*primitiveWorkBound H+6
    omega

end
end CurrentAFT.BinaryBackgroundDeviation
