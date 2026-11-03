import CurrentAFT.BinaryUnsafeArray
import CurrentAFT.RationalMarkedSeedProgram

/-! # The original fixed-scalar marked anchor with an actual binary index average -/
namespace CurrentAFT.BinaryMarkedFixedAnchor
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryDiffuseCurrent.metadata BinaryMarkedKernel.average PublicParameterProgram.modulus

def current (security : ℕ) (scalar : IntegerBits) (primary : Fin (BinaryFirstInverseProgram.colors security))
    (output : List Bool) : RationalResult :=
  let parameters := BinaryDiffuseCurrent.metadata security
  let code := canonicalCounter primary.val
  let result := BinaryMarkedKernel.average parameters.colors parameters.width primary.val 0 0
    scalar.negative scalar.digits code.digits output
  ⟨result.data,parameters.work+code.work+result.work+3⟩

theorem current_value (security : ℕ) (scalar : IntegerBits) (primary : Fin (BinaryFirstInverseProgram.colors security))
    (output : List Bool) :
    (current security scalar primary output).data.decode=RationalMarkedSeedProgram.fixedAnchor security primary.val scalar.decode (value output) := by
  rcases BinaryDiffuseCurrent.metadata_value security with ⟨hq,hw,_⟩
  unfold current
  rw [BinaryMarkedKernel.average_value,hq,hw]
  simp only [canonicalCounter_value,RationalMarkedSeedProgram.fixedAnchor,RationalMarkedSeedProgram.colors,
    PublicParameterProgram.modulus_value,RationalProposalProgram.anchorKernel,neg_neg,sub_self,IntegerBits.decode]

noncomputable section
noncomputable def widthPolynomial : Polynomial ℕ := (Polynomial.X+2)^48
noncomputable def parameterPolynomial (scalarBits outputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFirstInverseProgram.colorsPolynomial+widthPolynomial+scalarBits+outputBits
noncomputable def heightPolynomial : Polynomial ℕ := BinaryMarkedCurrent.averageHeightPolynomial widthPolynomial
noncomputable def workPolynomial (scalarBits outputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryDiffuseCurrent.metadataWorkPolynomial+50*(BinaryFirstInverseProgram.colorsPolynomial+1)^2+
    BinaryMarkedCurrent.averageWorkPolynomial widthPolynomial (parameterPolynomial scalarBits outputBits)+3

theorem current_bounds (security : ℕ) (scalar : IntegerBits) (primary : Fin (BinaryFirstInverseProgram.colors security))
    (output : List Bool) (scalarBits outputBits : Polynomial ℕ)
    (hs : scalar.digits.length ≤ scalarBits.eval security) (ho : output.length ≤ outputBits.eval security) :
    HeightBound (current security scalar primary output).data.decode (heightPolynomial.eval security) ∧
      (current security scalar primary output).work≤(workPolynomial scalarBits outputBits).eval security := by
  let parameters := BinaryDiffuseCurrent.metadata security
  let code := canonicalCounter primary.val
  let B := (parameterPolynomial scalarBits outputBits).eval security
  rcases BinaryDiffuseCurrent.metadata_value security with ⟨hq,hw,_⟩
  have hqB : parameters.colors≤BinaryFirstInverseProgram.colorsPolynomial.eval security := by
    rw [hq]
    exact (PublicParameterProgram.modulus_value security) ▸ BinaryFirstInverseProgram.colors_bound security
  have hp := primary.isLt.le.trans (BinaryFirstInverseProgram.colors_bound security)
  have hB : B=BinaryFirstInverseProgram.colorsPolynomial.eval security+(security+2)^48+
      scalarBits.eval security+outputBits.eval security := by
    simp only [B,parameterPolynomial,widthPolynomial,Polynomial.eval_add,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_ofNat]
  have hc : parameters.colors≤B := hqB.trans (by rw [hB]; omega)
  have hwidth : parameters.width≤B := by rw [hw,hB]; omega
  have hprimary : primary.val≤B := hp.trans (by rw [hB]; omega)
  have hcode : code.digits.length≤B := by
    rw [canonicalCounter_length]
    exact (Nat.size_le.mpr (Nat.lt_two_pow_self (n := primary.val))).trans hprimary
  have h := BinaryMarkedKernel.average_bounds parameters.colors parameters.width primary.val 0 0 scalar.negative
    scalar.digits code.digits output B hc hwidth hprimary (Nat.zero_le _) (Nat.zero_le _)
    (hs.trans (by rw [hB]; omega)) hcode (ho.trans (by rw [hB]; omega))
  have wp := BinaryDiffuseCurrent.metadata_work security
  change parameters.work≤_ at wp
  have wc : code.work≤50*(BinaryFirstInverseProgram.colorsPolynomial.eval security+1)^2 :=
    (canonicalCounter_work primary.val).trans
      (Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (Nat.add_le_add_right hp 1) 2))
  have hh : BinaryMarkedKernel.averageHeight parameters.width=heightPolynomial.eval security := by
    rw [hw]
    simp only [heightPolynomial,BinaryMarkedCurrent.averageHeightPolynomial,BinaryMarkedKernel.averageHeight,
      widthPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_ofNat]
  have wa := h.2.trans_eq (congrArg (fun width => BinaryMarkedKernel.averageWork width B) hw)
  change (BinaryMarkedKernel.average parameters.colors parameters.width primary.val 0 0 scalar.negative
    scalar.digits code.digits output).work≤BinaryMarkedKernel.averageWork ((security+2)^48) B at wa
  constructor
  · change HeightBound (BinaryMarkedKernel.average parameters.colors parameters.width primary.val 0 0
      scalar.negative scalar.digits code.digits output).data.decode _
    exact h.1.mono hh.le
  · change parameters.work+code.work+
      (BinaryMarkedKernel.average parameters.colors parameters.width primary.val 0 0 scalar.negative scalar.digits code.digits output).work+3≤_
    simp only [workPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_ofNat,
      Polynomial.eval_one,BinaryDiffuseCurrent.metadataWorkPolynomial_eval,BinaryMarkedCurrent.averageWorkPolynomial_eval,
      widthPolynomial,Polynomial.eval_X]
    change _≤BinaryDiffuseCurrent.metadataWork security+50*(BinaryFirstInverseProgram.colorsPolynomial.eval security+1)^2+
      BinaryMarkedKernel.averageWork ((security+2)^48) B+3
    omega

end
end CurrentAFT.BinaryMarkedFixedAnchor
