import CurrentAFT.BinaryUnsafeProfile

/-! # Executed current safe-interval membership test -/
namespace CurrentAFT.BinarySafeMembership
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinarySafeProfile.margin

def current (security : ℕ) (output : List Bool) : CountedValue Bool :=
  let modulus := PublicParameterProgram.modulus security
  let margin := BinarySafeProfile.margin security
  let qc := canonicalCounter modulus.count
  let mc := canonicalCounter margin.count
  let result := BinaryUnsafeProfile.membership qc.digits mc.digits output
  ⟨result.value,modulus.work+margin.work+qc.work+mc.work+result.work+5⟩

theorem current_value (security : ℕ) (output : List Bool) :
    (current security output).value=true ↔ RationalBackgroundProfiles.Safe security (value output) := by
  change (BinaryUnsafeProfile.membership _ _ _).value=true ↔ _
  rw [BinaryUnsafeProfile.membership_value]
  simp only [canonicalCounter_value,BinarySafeProfile.margin_value,RationalBackgroundProfiles.Safe,
    RationalBackgroundProfiles.margin,RationalBackgroundProfiles.colors]

noncomputable section
noncomputable def parameterPolynomial (inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFirstInverseProgram.colorsPolynomial+3*(Polynomial.X+2)^2+inputBits
noncomputable def workPolynomial (inputBits : Polynomial ℕ) : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+BinarySafeProfile.marginWorkPolynomial+
    100*(parameterPolynomial inputBits+1)^2+100*parameterPolynomial inputBits+100+5

theorem current_work (security : ℕ) (output : List Bool) (inputBits : Polynomial ℕ)
    (ho : output.length ≤ inputBits.eval security) :
    (current security output).work ≤ (workPolynomial inputBits).eval security := by
  let q := PublicParameterProgram.modulus security
  let m := BinarySafeProfile.margin security
  let qc := canonicalCounter q.count
  let mc := canonicalCounter m.count
  let B := (parameterPolynomial inputBits).eval security
  have hB : B=BinaryFirstInverseProgram.colorsPolynomial.eval security+3*(security+2)^2+inputBits.eval security := by
    simp only [B,parameterPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_ofNat]
  have hq : q.count ≤ B := (BinaryFirstInverseProgram.colors_bound security).trans (by rw [hB]; omega)
  have hm : m.count ≤ B := by rw [BinarySafeProfile.margin_value,hB]; omega
  have hqc : qc.digits.length ≤ B := by
    rw [canonicalCounter_length]; exact (Nat.size_le.mpr (Nat.lt_two_pow_self (n := q.count))).trans hq
  have hmc : mc.digits.length ≤ B := by
    rw [canonicalCounter_length]; exact (Nat.size_le.mpr (Nat.lt_two_pow_self (n := m.count))).trans hm
  have wr := BinaryUnsafeProfile.membership_work qc.digits mc.digits output B hqc hmc (ho.trans (by rw [hB]; omega))
  have wq := PublicParameterProgram.modulus_work security
  have wm := BinarySafeProfile.margin_work security
  have wqc := (canonicalCounter_work q.count).trans (Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (Nat.add_le_add_right hq 1) 2))
  have wmc := (canonicalCounter_work m.count).trans (Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (Nat.add_le_add_right hm 1) 2))
  change q.work ≤ _ at wq
  change m.work ≤ _ at wm
  change qc.work ≤ _ at wqc
  change mc.work ≤ _ at wmc
  change q.work+m.work+qc.work+mc.work+(BinaryUnsafeProfile.membership qc.digits mc.digits output).work+5 ≤ _
  simp only [workPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_ofNat,
    Polynomial.eval_one,PublicParameterProgram.workPolynomial_eval,BinarySafeProfile.marginWorkPolynomial_eval]
  change _ ≤ PublicParameterProgram.workBound security+BinarySafeProfile.marginWork security+100*(B+1)^2+100*B+100+5
  omega

end
end CurrentAFT.BinarySafeMembership
