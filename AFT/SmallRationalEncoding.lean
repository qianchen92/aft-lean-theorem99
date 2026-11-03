import AFT.BinaryGaussianInputs
import AFT.ParametricLiteralBounds

/-! # Runtime encoding of polynomially bounded rational literals

The input rational is an already constructed numerator/denominator record.
Both integers are encoded by the actual counter algorithms, and the binary
quotient is normalized by the actual rational implementation. This module
charges encoding, not the earlier construction of the rational record.
-/
namespace AFT.BinaryArithmetic.RationalBits
open AFT.RationalNumerics Polynomial

def encodeSmallRational (input : ℚ) : RationalResult :=
  let numerator := ofUnaryInteger input.num
  let denominator := ofCounter input.den
  let result := quotient numerator.data denominator.data
  ⟨result.data,numerator.work+denominator.work+result.work+3⟩

theorem encodeSmallRational_value (input : ℚ) :
    (encodeSmallRational input).data.decode=input := by
  simp only [encodeSmallRational,quotient_value,ofUnaryInteger_value,ofCounter_value,
    Rat.num_div_den]

def smallRationalEncodingWork (bound : ℕ) : ℕ :=
  120*(bound+1)^2+2*primitiveWorkBound bound+10

theorem encodeSmallRational_work (input : ℚ) (bound : ℕ)
    (hinput : RationalLiteralBound input bound) :
    (encodeSmallRational input).work≤smallRationalEncodingWork bound := by
  have hn := (ofUnaryInteger_work input.num).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left 60
      (Nat.pow_le_pow_left (Nat.add_le_add_right hinput.1 1) 2)) 5)
  have hd := (ofCounter_work input.den).trans
    (Nat.mul_le_mul_left 60 (Nat.pow_le_pow_left (Nat.add_le_add_right hinput.2 1) 2))
  have hnh : HeightBound (ofUnaryInteger input.num).data.decode bound := by
    rw [ofUnaryInteger_value]
    exact HeightBound.of_int (hinput.1.trans (Nat.lt_two_pow_self (n:=bound)).le)
  have hdh : HeightBound (ofCounter input.den).data.decode bound := by
    rw [ofCounter_value]
    exact (HeightBound.nat_coarse input.den).mono hinput.2
  have hq := quotient_work (ofUnaryInteger input.num).data (ofCounter input.den).data bound hnh hdh
  simp only [encodeSmallRational,smallRationalEncodingWork]
  omega

theorem encodeSmallRational_height (input : ℚ) (bound : ℕ)
    (hinput : RationalLiteralBound input bound) :
    HeightBound (encodeSmallRational input).data.decode bound := by
  rw [encodeSmallRational_value]
  exact ⟨hinput.1.trans (Nat.lt_two_pow_self (n:=bound)).le,
    hinput.2.trans (Nat.lt_two_pow_self (n:=bound)).le⟩

theorem encodeSmallRational_lengths (input : ℚ) (bound : ℕ)
    (hinput : RationalLiteralBound input bound) :
    (encodeSmallRational input).data.numerator.length≤bound+1 ∧
      (encodeSmallRational input).data.denominator.length≤bound+1 :=
  lengths_of_height _ _ (encodeSmallRational_height input bound hinput)

noncomputable def smallRationalEncodingPolynomial (bound : Polynomial ℕ) : Polynomial ℕ :=
  120*(bound+1)^2+20000000*(bound+2)^3+10

theorem smallRationalEncodingPolynomial_eval (bound : Polynomial ℕ) (n : ℕ) :
    (smallRationalEncodingPolynomial bound).eval n=smallRationalEncodingWork (bound.eval n) := by
  simp [smallRationalEncodingPolynomial,smallRationalEncodingWork,primitiveWorkBound]
  ring

theorem encodeSmallRational_polynomial_work (input : ℚ) (bound : Polynomial ℕ) (n : ℕ)
    (hinput : RationalLiteralBound input (bound.eval n)) :
    (encodeSmallRational input).work≤(smallRationalEncodingPolynomial bound).eval n := by
  rw [smallRationalEncodingPolynomial_eval]
  exact encodeSmallRational_work input _ hinput

end AFT.BinaryArithmetic.RationalBits
