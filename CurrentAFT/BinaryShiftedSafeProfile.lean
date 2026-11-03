import CurrentAFT.BinaryUnsafeProfile

/-! # The full shifted safe law, with generated current metadata -/
namespace CurrentAFT.BinaryShiftedSafeProfile
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryBodyKernel.translated

def current (security : ℕ) (shift : IntegerBits) (output : List Bool) : RationalResult :=
  let modulus := PublicParameterProgram.modulus security
  let margin := BinarySafeProfile.margin security
  let result := BinaryBodyKernel.translated modulus.count margin.count shift.negative shift.digits output
  ⟨result.data,modulus.work+margin.work+result.work+3⟩

theorem current_value (security : ℕ) (shift : IntegerBits) (output : List Bool) :
    (current security shift output).data.decode=RationalBackgroundProfiles.shifted security shift.decode (value output) := by
  have hq : 0<(PublicParameterProgram.modulus security).count := by
    rw [PublicParameterProgram.modulus_value]
    exact (Parameters.modulus_spec security).2.pos
  change (BinaryBodyKernel.translated _ _ _ _ _).data.decode=_
  rw [BinaryBodyKernel.translated_value _ _ _ _ _ hq,BinarySafeProfile.margin_value]
  rfl

noncomputable section
noncomputable def heightPolynomial (shiftBits outputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryUnsafeProfile.heightPolynomial shiftBits outputBits
noncomputable def workPolynomial (shiftBits outputBits : Polynomial ℕ) : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+BinarySafeProfile.marginWorkPolynomial+
    BinaryBodyKernel.translatedWorkPolynomial (BinaryUnsafeProfile.parameterPolynomial shiftBits outputBits)+3

theorem current_bounds (security : ℕ) (shift : IntegerBits) (output : List Bool) (shiftBits outputBits : Polynomial ℕ)
    (hs : shift.digits.length ≤ shiftBits.eval security) (ho : output.length ≤ outputBits.eval security) :
    HeightBound (current security shift output).data.decode ((heightPolynomial shiftBits outputBits).eval security) ∧
      (current security shift output).work≤(workPolynomial shiftBits outputBits).eval security := by
  let q := PublicParameterProgram.modulus security
  let m := BinarySafeProfile.margin security
  let B := (BinaryUnsafeProfile.parameterPolynomial shiftBits outputBits).eval security
  have hB : B=BinaryFirstInverseProgram.colorsPolynomial.eval security+3*(security+2)^2+
      shiftBits.eval security+outputBits.eval security := by
    simp only [B,BinaryUnsafeProfile.parameterPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
      Polynomial.eval_X,Polynomial.eval_ofNat]
  have hq : q.count≤B := (BinaryFirstInverseProgram.colors_bound security).trans (by rw [hB]; omega)
  have hm : m.count≤B := by rw [BinarySafeProfile.margin_value,hB]; omega
  have h := BinaryBodyKernel.translated_bounds q.count m.count shift.negative shift.digits output B hq hm
    (hs.trans (by rw [hB]; omega)) (ho.trans (by rw [hB]; omega))
  constructor
  · simpa only [heightPolynomial,BinaryUnsafeProfile.heightPolynomial,Polynomial.eval_mul,Polynomial.eval_add,
      Polynomial.eval_ofNat] using h.1
  · have wq := PublicParameterProgram.modulus_work security
    have wm := BinarySafeProfile.margin_work security
    change q.work≤_ at wq
    change m.work≤_ at wm
    change q.work+m.work+(BinaryBodyKernel.translated q.count m.count shift.negative shift.digits output).work+3≤_
    simp only [workPolynomial,Polynomial.eval_add,Polynomial.eval_ofNat,PublicParameterProgram.workPolynomial_eval,
      BinarySafeProfile.marginWorkPolynomial_eval,BinaryBodyKernel.translatedWorkPolynomial_eval]
    dsimp only [B] at h
    omega

end
end CurrentAFT.BinaryShiftedSafeProfile
