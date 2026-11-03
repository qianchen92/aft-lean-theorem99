import CurrentAFT.BinaryDensityInverseTensor
import CurrentAFT.BinaryRootMeanResources
import CurrentAFT.BinaryShiftedSafeProfile
import CurrentAFT.RationalRootMassProgram
import AFT.BinaryIntegerData

/-! The compensator equality and attachment use their actual retained roots
and the same scalar as the pair. No hidden root is replaced by a marginal. -/
namespace CurrentAFT.BinaryRootControlRest
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryRootProfile.key BinaryShiftedSafeProfile.current
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def current (security : ℕ) (compensator attachment scalar : IntegerBits)
    (center : Fin (colors security)) (word : Vector (Fin (colors security)) 4) : RationalResult :=
  let first := readVector (BinaryDensityInverseTensor.first security) word 0
  let last := readVector (BinaryDensityInverseTensor.first security) word 3
  let firstCode := canonicalCounter first.value.val
  let lastCode := canonicalCounter last.value.val
  let centerCode := canonicalCounter center.val
  let negative := IntegerBits.negate compensator
  let key := BinaryRootProfile.key security negative.value centerCode.digits
  let matched := signedEqual false false key.digits firstCode.digits
  let shift := IntegerBits.add attachment scalar
  let body := BinaryShiftedSafeProfile.current security shift.value lastCode.digits
  ⟨if matched.value then body.data else zero,
    first.work+last.work+firstCode.work+lastCode.work+centerCode.work+negative.work+key.work+matched.work+shift.work+body.work+10⟩

theorem current_value (security : ℕ) (compensator attachment scalar : IntegerBits)
    (center : Fin (colors security)) (word : Vector (Fin (colors security)) 4) :
    (current security compensator attachment scalar center word).data.decode =
      RationalRootMassProgram.controlRest security compensator.decode attachment.decode scalar.decode center.val
        (fun index => (word.get index).val) := by
  have hq : (PublicParameterProgram.modulus security).count ≠ 0 := by
    rw [PublicParameterProgram.modulus_value]
    exact (Parameters.modulus_spec security).2.ne_zero
  have hk := BinaryRootProfile.key_value security (IntegerBits.negate compensator).value (canonicalCounter center.val).digits
  simp only [RationalBackgroundProfiles.inverseShift, RationalBackgroundProfiles.colors,
    IntegerBits.negate_value, canonicalCounter_value, sub_neg_eq_add] at hk
  have hcast : (value (BinaryRootProfile.key security (IntegerBits.negate compensator).value
      (canonicalCounter center.val).digits).digits:ℤ) =
      ((center.val:ℤ)+compensator.decode)%(PublicParameterProgram.modulus security).count := by
    rw [hk, Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hq))]
  have hm := signedEqual_value false false
    (BinaryRootProfile.key security (IntegerBits.negate compensator).value (canonicalCounter center.val).digits).digits
    (canonicalCounter (word.get 0).val).digits
  simp only [signedValue, Bool.false_eq_true, if_false, canonicalCounter_value, hcast] at hm
  simp only [current, readVector_value]
  simp only [hm]
  split_ifs <;> simp only [BinaryShiftedSafeProfile.current_value, IntegerBits.add_value, canonicalCounter_value,
    RationalRootMassProgram.controlRest, RationalBackgroundProfiles.shifted, RationalBackgroundProfiles.colors, RationalBackgroundProfiles.margin, ite_true, ite_false, mul_one, mul_zero, zero_value, *]

noncomputable section
noncomputable def heightPolynomial (inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryShiftedSafeProfile.heightPolynomial (inputBits+1) BinaryFirstInverseProgram.colorsPolynomial
noncomputable def workPolynomial (inputBits : Polynomial ℕ) : Polynomial ℕ :=
  let Q := BinaryFirstInverseProgram.colorsPolynomial
  let K := BinaryRootProfile.keyBitsPolynomial inputBits Q
  150*(Q+1)^2+20*inputBits+100+BinaryRootProfile.keyWorkPolynomial inputBits Q+
    48*(K+Q)+BinaryShiftedSafeProfile.workPolynomial (inputBits+1) Q

theorem current_bounds (security : ℕ) (inputBits : Polynomial ℕ) (compensator attachment scalar : IntegerBits)
    (center : Fin (colors security)) (word : Vector (Fin (colors security)) 4)
    (hc : compensator.digits.length ≤ inputBits.eval security)
    (ha : attachment.digits.length ≤ inputBits.eval security) (hs : scalar.digits.length ≤ inputBits.eval security) :
    HeightBound (current security compensator attachment scalar center word).data.decode ((heightPolynomial inputBits).eval security) ∧
      (current security compensator attachment scalar center word).work ≤ (workPolynomial inputBits).eval security := by
  let first := readVector (BinaryDensityInverseTensor.first security) word 0
  let last := readVector (BinaryDensityInverseTensor.first security) word 3
  let firstCode := canonicalCounter first.value.val
  let lastCode := canonicalCounter last.value.val
  let centerCode := canonicalCounter center.val
  let negative := IntegerBits.negate compensator
  let key := BinaryRootProfile.key security negative.value centerCode.digits
  let matched := signedEqual false false key.digits firstCode.digits
  let shift := IntegerBits.add attachment scalar
  let body := BinaryShiftedSafeProfile.current security shift.value lastCode.digits
  let Q := BinaryFirstInverseProgram.colorsPolynomial.eval security
  have hq := BinaryFirstInverseProgram.colors_bound security
  have hn (color : Fin (colors security)) : color.val ≤ Q := color.isLt.le.trans hq
  have hl (color : Fin (colors security)) : (canonicalCounter color.val).digits.length ≤ Q := by
    rw [canonicalCounter_length]
    exact (Nat.size_le.mpr (Nat.lt_two_pow_self (n:=color.val))).trans (hn color)
  have hw (color : Fin (colors security)) : (canonicalCounter color.val).work ≤ 50*(Q+1)^2 :=
    (canonicalCounter_work color.val).trans (Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (Nat.add_le_add_right (hn color) 1) 2))
  have hshift : shift.value.digits.length ≤ (inputBits+1).eval security := by
    have h := IntegerBits.add_length attachment scalar
    simp only [Polynomial.eval_add, Polynomial.eval_one]
    exact h.trans (by omega)
  have hb := BinaryShiftedSafeProfile.current_bounds security shift.value lastCode.digits
    (inputBits+1) BinaryFirstInverseProgram.colorsPolynomial hshift (hl _)
  have hk := BinaryRootProfile.key_bounds security inputBits BinaryFirstInverseProgram.colorsPolynomial
    negative.value centerCode.digits hc (hl center)
  change key.digits.length ≤ (BinaryRootProfile.keyBitsPolynomial inputBits BinaryFirstInverseProgram.colorsPolynomial).eval security ∧
    key.work ≤ (BinaryRootProfile.keyWorkPolynomial inputBits BinaryFirstInverseProgram.colorsPolynomial).eval security at hk
  change HeightBound body.data.decode _ ∧ body.work ≤ _ at hb
  constructor
  · change HeightBound (if matched.value then body.data else zero).decode _
    split_ifs
    · exact hb.1
    · exact HeightBound.zero.mono (Nat.zero_le _)
  · have wf := readVector_work (BinaryDensityInverseTensor.first security) word 0
    have wl := readVector_work (BinaryDensityInverseTensor.first security) word 3
    have wfc := hw first.value
    have wlc := hw last.value
    have wcc := hw center
    have ws := IntegerBits.add_work attachment scalar
    have wm := signedEqual_work false false key.digits firstCode.digits
    have hf := hl first.value
    change first.work+last.work+firstCode.work+lastCode.work+centerCode.work+negative.work+
      key.work+matched.work+shift.work+body.work+10 ≤ _
    have wn : negative.work=2 := rfl
    change first.work ≤ 15 at wf
    change last.work ≤ 15 at wl
    change firstCode.work ≤ 50*(Q+1)^2 at wfc
    change lastCode.work ≤ 50*(Q+1)^2 at wlc
    change centerCode.work ≤ 50*(Q+1)^2 at wcc
    change shift.work ≤ _ at ws
    change matched.work ≤ _ at wm
    change firstCode.digits.length ≤ Q at hf
    simp only [workPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_ofNat, Polynomial.eval_one]
    change _ ≤ 150*(Q+1)^2+20*inputBits.eval security+100+
      (BinaryRootProfile.keyWorkPolynomial inputBits BinaryFirstInverseProgram.colorsPolynomial).eval security+
      48*((BinaryRootProfile.keyBitsPolynomial inputBits BinaryFirstInverseProgram.colorsPolynomial).eval security+Q)+
      (BinaryShiftedSafeProfile.workPolynomial (inputBits+1) BinaryFirstInverseProgram.colorsPolynomial).eval security
    omega

end
end CurrentAFT.BinaryRootControlRest
