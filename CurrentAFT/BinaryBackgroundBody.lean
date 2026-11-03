import CurrentAFT.BinarySafeProfile
import CurrentAFT.RationalBackgroundDensities

/-! # Original free-body certificate density from generated safe and center tables -/
namespace CurrentAFT.BinaryBackgroundBody
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinarySafeProfile.current BinaryReferenceTables.current

def current (security bits : ℕ) (output : Fin (BinaryFirstInverseProgram.colors security)) : RationalResult :=
  let code := canonicalCounter output.val
  let safe := BinarySafeProfile.current security code.digits
  let reference := BinaryReferenceTables.current security bits
  let center := readVector zero reference.center output
  let density := RationalBits.quotient safe.data center.value
  let negative := RationalBits.negate density.data
  let result := RationalBits.add one negative.data
  ⟨result.data, code.work+safe.work+reference.work+center.work+density.work+negative.work+result.work+7⟩

theorem current_value (security bits : ℕ) (output : Fin (BinaryFirstInverseProgram.colors security)) :
    (current security bits output).data.decode = RationalBackgroundDensities.body security bits output.val := by
  simp only [current, RationalBits.add_value, RationalBits.negate_value, quotient_value, one_value,
    BinarySafeProfile.current_value, canonicalCounter_value, readVector_value, BinaryReferenceTables.center_value,
    RationalBackgroundDensities.body, sub_eq_add_neg]

noncomputable section
noncomputable def operandHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinarySafeProfile.heightPolynomial BinaryFirstInverseProgram.colorsPolynomial+
    BinaryReferenceTables.heightPolynomial precision+1
noncomputable def heightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ := operandHeightPolynomial precision+1
noncomputable def workPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  50*(BinaryFirstInverseProgram.colorsPolynomial+1)^2+
    BinarySafeProfile.workPolynomial BinaryFirstInverseProgram.colorsPolynomial+
    BinaryReferenceTables.currentWorkPolynomial precision+3*BinaryFirstInverseProgram.colorsPolynomial+
    4*primitiveWorkPolynomial (operandHeightPolynomial precision)+12

theorem current_bounds (security : ℕ) (precision : Polynomial ℕ) (output : Fin (BinaryFirstInverseProgram.colors security)) :
    HeightBound (current security (precision.eval security) output).data.decode ((heightPolynomial precision).eval security) ∧
      (current security (precision.eval security) output).work ≤ (workPolynomial precision).eval security := by
  let code := canonicalCounter output.val
  let safe := BinarySafeProfile.current security code.digits
  let reference := BinaryReferenceTables.current security (precision.eval security)
  let center := readVector zero reference.center output
  let density := RationalBits.quotient safe.data center.value
  let negative := RationalBits.negate density.data
  let H := (operandHeightPolynomial precision).eval security
  have hq := BinaryFirstInverseProgram.colors_bound security
  have ho := output.isLt.le.trans hq
  have hl : code.digits.length ≤ BinaryFirstInverseProgram.colorsPolynomial.eval security := by
    rw [canonicalCounter_length]
    exact (Nat.size_le.mpr (Nat.lt_two_pow_self (n := output.val))).trans ho
  have hs := BinarySafeProfile.current_bounds security code.digits BinaryFirstInverseProgram.colorsPolynomial hl
  have hr := BinaryReferenceTables.current_bounds security precision
  have hH : H = (BinarySafeProfile.heightPolynomial BinaryFirstInverseProgram.colorsPolynomial).eval security+
      (BinaryReferenceTables.heightPolynomial precision).eval security+1 := by
    simp only [H, operandHeightPolynomial, Polynomial.eval_add, Polynomial.eval_one]
  have hsafe : HeightBound safe.data.decode H := hs.1.mono (by rw [hH]; omega)
  have hcenter : HeightBound center.value.decode H := by
    rw [readVector_value]
    exact (hr.2.1 output).mono (by rw [hH]; omega)
  have hdensity : HeightBound density.data.decode H := by
    rw [quotient_value, readVector_value]
    exact (hs.1.div (hr.2.1 output)).mono (by rw [hH]; omega)
  have hnegative : HeightBound negative.data.decode H := by rw [RationalBits.negate_value]; exact hdensity.neg
  have wc : code.work ≤ 50*(BinaryFirstInverseProgram.colorsPolynomial.eval security+1)^2 :=
    (canonicalCounter_work output.val).trans (Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (Nat.add_le_add_right ho 1) 2))
  have wr : reference.work ≤ (BinaryReferenceTables.currentWorkPolynomial precision).eval security := hr.2.2.2.2
  have wsafe : safe.work ≤ (BinarySafeProfile.workPolynomial BinaryFirstInverseProgram.colorsPolynomial).eval security := hs.2
  have wcenter := readVector_work zero reference.center output
  change center.work ≤ 3*BinaryFirstInverseProgram.colors security+3 at wcenter
  have wd : density.work ≤ 2*primitiveWorkBound H+2 := quotient_work _ _ H hsafe hcenter
  have wn : negative.work ≤ primitiveWorkBound H := RationalBits.negate_work density.data H
  have wa := RationalBits.add_work one negative.data H (by rw [one_value]; exact HeightBound.one.mono (by omega)) hnegative
  constructor
  · change HeightBound (RationalBits.add one negative.data).data.decode _
    rw [RationalBits.add_value, one_value]
    simpa only [heightPolynomial, Polynomial.eval_add, Polynomial.eval_one, zero_add, H] using HeightBound.one.add hnegative
  · change code.work+safe.work+reference.work+center.work+density.work+negative.work+
      (RationalBits.add one negative.data).work+7 ≤ _
    simp only [workPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_ofNat, Polynomial.eval_one, primitiveWorkPolynomial_eval]
    change _ ≤ 50*(BinaryFirstInverseProgram.colorsPolynomial.eval security+1)^2+
      (BinarySafeProfile.workPolynomial BinaryFirstInverseProgram.colorsPolynomial).eval security+
      (BinaryReferenceTables.currentWorkPolynomial precision).eval security+3*BinaryFirstInverseProgram.colorsPolynomial.eval security+
      4*primitiveWorkBound H+12
    omega

end
end CurrentAFT.BinaryBackgroundBody
