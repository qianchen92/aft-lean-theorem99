import CurrentAFT.BinaryFirstInverseResources
import CurrentAFT.RationalBackgroundProfiles

/-! # Actual public margin and safe-law atom on binary operands -/
namespace CurrentAFT.BinarySafeProfile
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus addCounter multiplyCounter powerCounter

def margin (security : ℕ) : UnaryCounterResult :=
  let base := addCounter security 2
  let square := powerCounter base.count 2
  let result := multiplyCounter 3 square.count
  ⟨result.count, base.work+square.work+result.work+3⟩

theorem margin_value (security : ℕ) : (margin security).count = 3*(security+2)^2 := by
  simp only [margin, multiplyCounter_value, powerCounter_value, addCounter_value]

def marginWork (security : ℕ) := 2*security+1+powerCounterWork (security+2) 2+3*(2*(security+2)^2+3)+1+3

theorem margin_work (security : ℕ) : (margin security).work ≤ marginWork security := by
  have hs := powerCounter_work (addCounter security 2).count 2
  simp only [addCounter_value] at hs
  simp only [margin, addCounter_work, multiplyCounter_work, powerCounter_value, addCounter_value, marginWork]
  omega

def current (security : ℕ) (output : List Bool) : RationalResult :=
  let modulus := PublicParameterProgram.modulus security
  let safeMargin := margin security
  let modulusCode := canonicalCounter modulus.count
  let marginCode := canonicalCounter safeMargin.count
  let result := binarySliceProbability false false false false modulusCode.digits marginCode.digits [] output
  ⟨result.data, modulus.work+safeMargin.work+modulusCode.work+marginCode.work+result.work+5⟩

theorem current_value (security : ℕ) (output : List Bool) :
    (current security output).data.decode = RationalBackgroundProfiles.safe security (value output) := by
  simp only [current, binarySliceProbability_value, signedValue, Bool.false_eq_true, if_false,
    canonicalCounter_value, value, margin_value, RationalBackgroundProfiles.safe,
    RationalBackgroundProfiles.colors, RationalBackgroundProfiles.margin, RationalProposalProgram.safeEntry]
  norm_num

noncomputable section
noncomputable def marginWorkPolynomial : Polynomial ℕ :=
  2*Polynomial.X+1+3*(6*(Polynomial.X+3)^4+4)+3*(2*(Polynomial.X+2)^2+3)+1+3
noncomputable def parameterPolynomial (inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFirstInverseProgram.colorsPolynomial+3*(Polynomial.X+2)^2+inputBits
noncomputable def heightPolynomial (inputBits : Polynomial ℕ) : Polynomial ℕ := parameterPolynomial inputBits+3
noncomputable def sliceWorkPolynomial (bits : Polynomial ℕ) : Polynomial ℕ :=
  120*(bits+2)+11+200*(bits+5)+primitiveWorkPolynomial (bits+3)
noncomputable def workPolynomial (inputBits : Polynomial ℕ) : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+marginWorkPolynomial+100*(parameterPolynomial inputBits+1)^2+
    sliceWorkPolynomial (parameterPolynomial inputBits)+5

theorem sliceWorkPolynomial_eval (bits : Polynomial ℕ) (security : ℕ) :
    (sliceWorkPolynomial bits).eval security = binarySliceProbabilityWork (bits.eval security) := by
  simp only [sliceWorkPolynomial, binarySliceProbabilityWork, binaryEndpointProbabilityWork,
    binaryIntervalProbabilityWork, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    primitiveWorkPolynomial_eval]
  ring

theorem marginWorkPolynomial_eval (security : ℕ) : marginWorkPolynomial.eval security = marginWork security := by
  simp only [marginWorkPolynomial, marginWork, powerCounterWork, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_one]
  ring

theorem current_bounds (security : ℕ) (output : List Bool) (inputBits : Polynomial ℕ)
    (ho : output.length ≤ inputBits.eval security) :
    HeightBound (current security output).data.decode ((heightPolynomial inputBits).eval security) ∧
      (current security output).work ≤ (workPolynomial inputBits).eval security := by
  let q := PublicParameterProgram.modulus security
  let m := margin security
  let qc := canonicalCounter q.count
  let mc := canonicalCounter m.count
  let B := (parameterPolynomial inputBits).eval security
  have hB : B = BinaryFirstInverseProgram.colorsPolynomial.eval security+3*(security+2)^2+inputBits.eval security := by
    simp only [B, parameterPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_ofNat]
  have hq : q.count ≤ B := (BinaryFirstInverseProgram.colors_bound security).trans (by rw [hB]; omega)
  have hm : m.count ≤ B := by rw [margin_value, hB]; omega
  have hqc : qc.digits.length ≤ B := by
    rw [canonicalCounter_length]
    exact (Nat.size_le.mpr (Nat.lt_two_pow_self (n := q.count))).trans hq
  have hmc : mc.digits.length ≤ B := by
    rw [canonicalCounter_length]
    exact (Nat.size_le.mpr (Nat.lt_two_pow_self (n := m.count))).trans hm
  have hout : output.length ≤ B := ho.trans (by rw [hB]; omega)
  have hp := binarySliceProbability_height false false false false qc.digits mc.digits [] output B hqc hmc (by simp)
  have wp := binarySliceProbability_work false false false false qc.digits mc.digits [] output B hqc hmc (by simp) hout
  have wq := PublicParameterProgram.modulus_work security
  have wm := margin_work security
  change q.work ≤ _ at wq
  change m.work ≤ _ at wm
  have wqc : qc.work ≤ 50*(B+1)^2 := (canonicalCounter_work q.count).trans
    (Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (Nat.add_le_add_right hq 1) 2))
  have wmc : mc.work ≤ 50*(B+1)^2 := (canonicalCounter_work m.count).trans
    (Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (Nat.add_le_add_right hm 1) 2))
  constructor
  · simpa only [heightPolynomial, Polynomial.eval_add, Polynomial.eval_ofNat] using hp
  · change q.work+m.work+qc.work+mc.work+
      (binarySliceProbability false false false false qc.digits mc.digits [] output).work+5 ≤ _
    simp only [workPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
      Polynomial.eval_one, PublicParameterProgram.workPolynomial_eval, marginWorkPolynomial_eval, sliceWorkPolynomial_eval]
    change _ ≤ PublicParameterProgram.workBound security+marginWork security+100*(B+1)^2+binarySliceProbabilityWork B+5
    omega

end
end CurrentAFT.BinarySafeProfile
