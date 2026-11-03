import CurrentAFT.BinaryRootMeanResources

/-! # Charged palette normalization and lookup of a generated profile -/
namespace CurrentAFT.BinaryProfileLookup
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryRootProfile.key BinaryPaletteLookup.current

abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def zeroRoot : IntegerBits := ⟨false,[]⟩

def current (security : ℕ) (profile : Fin (colors security) → RationalResult) (output : ℕ) : RationalResult :=
  let code := canonicalCounter output
  let modulus := PublicParameterProgram.modulus security
  let table := buildArray modulus.count profile
  let key := BinaryRootProfile.key security zeroRoot code.digits
  let result := BinaryPaletteLookup.current table.data key.digits
  ⟨result.data,code.work+modulus.work+table.work+key.work+result.work+5⟩

theorem key_value (security output : ℕ) :
    value (BinaryRootProfile.key security zeroRoot (canonicalCounter output).digits).digits = output%colors security := by
  rw [BinaryRootProfile.key_value,canonicalCounter_value]
  simp only [RationalBackgroundProfiles.inverseShift,zeroRoot,IntegerBits.decode,signedValue,
    Bool.false_eq_true,if_false,value,Int.ofNat_zero,sub_zero]
  rfl

theorem current_value (security : ℕ) (profile : Fin (colors security) → RationalResult) (ideal : ℕ → ℚ)
    (hprofile : ∀ color, (profile color).data.decode=ideal color.val) (output : ℕ) :
    (current security profile output).data.decode=ideal (output%colors security) := by
  have hq : 0<colors security := by
    rw [colors,BinaryFirstInverseProgram.colors,PublicParameterProgram.modulus_value]
    exact (Parameters.modulus_spec security).2.pos
  change (BinaryPaletteLookup.current _ _).data.decode = _
  rw [BinaryPaletteLookup.current_value _ _ ⟨output%colors security,Nat.mod_lt _ hq⟩ (key_value security output),
    buildArray_get,hprofile]

noncomputable section
def heightPolynomial (profileBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFirstInverseProgram.colorsPolynomial*(profileBits+1)
def lookupWorkPolynomial (profileBits : Polynomial ℕ) : Polynomial ℕ :=
  let Q := BinaryFirstInverseProgram.colorsPolynomial
  let K := BinaryRootProfile.keyBitsPolynomial 0 Q
  Q*(50*(Q+1)^2+48*(Q+K)+42+3*Q+3+primitiveWorkPolynomial ((Q+1)*(profileBits+1))+2)+2
def workPolynomial (profileBits profileWork : Polynomial ℕ) : Polynomial ℕ :=
  50*(BinaryFirstInverseProgram.colorsPolynomial+1)^2+PublicParameterProgram.workPolynomial+
    BinaryFirstInverseProgram.colorsPolynomial*(profileWork+2)+2+
    BinaryRootProfile.keyWorkPolynomial 0 BinaryFirstInverseProgram.colorsPolynomial+
    lookupWorkPolynomial profileBits+5

theorem current_bounds (security : ℕ) (profileBits profileWork : Polynomial ℕ)
    (profile : Fin (colors security) → RationalResult) (output : ℕ) (ho : output<colors security)
    (hh : ∀ color, HeightBound (profile color).data.decode (profileBits.eval security))
    (hw : ∀ color, (profile color).work ≤ profileWork.eval security) :
    HeightBound (current security profile output).data.decode ((heightPolynomial profileBits).eval security) ∧
      (current security profile output).work ≤ (workPolynomial profileBits profileWork).eval security := by
  let code := canonicalCounter output
  let modulus := PublicParameterProgram.modulus security
  let table := buildArray modulus.count profile
  let key := BinaryRootProfile.key security zeroRoot code.digits
  let result := BinaryPaletteLookup.current table.data key.digits
  have hq := BinaryFirstInverseProgram.colors_bound security
  have hi := ho.le.trans hq
  have hl : code.digits.length ≤ BinaryFirstInverseProgram.colorsPolynomial.eval security := by
    rw [canonicalCounter_length]; exact (Nat.size_le.mpr (Nat.lt_two_pow_self (n:=output))).trans hi
  have hk := BinaryRootProfile.key_bounds security 0 BinaryFirstInverseProgram.colorsPolynomial zeroRoot code.digits
    (by simp [zeroRoot]) hl
  have ht (color : Fin (colors security)) : HeightBound (table.data.get color).decode (profileBits.eval security) := by
    rw [buildArray_get]; exact hh color
  have hr := BinaryPaletteLookup.current_bounds table.data key.digits
    ((BinaryRootProfile.keyBitsPolynomial 0 BinaryFirstInverseProgram.colorsPolynomial).eval security)
    (profileBits.eval security) hk.1 ht
  have wc := (canonicalCounter_work output).trans
    (Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (Nat.add_le_add_right hi 1) 2))
  change code.work ≤ 50*(BinaryFirstInverseProgram.colorsPolynomial.eval security+1)^2 at wc
  have wk : key.work ≤ (BinaryRootProfile.keyWorkPolynomial 0 BinaryFirstInverseProgram.colorsPolynomial).eval security := hk.2
  have wm : modulus.work ≤ PublicParameterProgram.workBound security := PublicParameterProgram.modulus_work security
  have wt := (buildArray_work (colors security) (profileWork.eval security) profile hw).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ hq) 2)
  have wr : result.work ≤ (lookupWorkPolynomial profileBits).eval security := by
    apply hr.2.trans
    simp only [lookupWorkPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
      Polynomial.eval_ofNat,Polynomial.eval_one,primitiveWorkPolynomial_eval]
    unfold BinaryPaletteLookup.work BinaryPaletteLookup.termWork primitiveWorkBound
    gcongr
  constructor
  · apply hr.1.mono
    simp only [heightPolynomial,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_one]
    exact Nat.mul_le_mul_right _ hq
  · change code.work+modulus.work+table.work+key.work+result.work+5 ≤ _
    simp only [workPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_ofNat,Polynomial.eval_one]
    rw [PublicParameterProgram.workPolynomial_eval]
    change table.work ≤ BinaryFirstInverseProgram.colorsPolynomial.eval security*(profileWork.eval security+2)+2 at wt
    omega

end
end CurrentAFT.BinaryProfileLookup
