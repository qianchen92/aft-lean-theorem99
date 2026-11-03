import CurrentAFT.BinaryFairDiffuse
import CurrentAFT.BinarySafeMembership

/-! # True fair diffuse pair and its safe-core mask on stored binary colors -/
namespace CurrentAFT.BinaryDiffusePairLeaf
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryFairDiffuse.current BinarySafeProfile.current BinarySafeMembership.current

abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def pair (security bits : ℕ) (scalar : IntegerBits) (first second : Fin (colors security)) : RationalResult :=
  let fc := canonicalCounter first.val
  let sc := canonicalCounter second.val
  let result := BinaryFairDiffuse.current security bits scalar fc.digits sc.digits
  ⟨result.data,fc.work+sc.work+result.work+3⟩

theorem pair_value (security bits : ℕ) (scalar : IntegerBits) (first second : Fin (colors security)) :
    (pair security bits scalar first second).data.decode=RationalDiffuseResidualProgram.pair security bits scalar.decode first.val second.val := by
  simp only [pair,BinaryFairDiffuse.current_value,canonicalCounter_value]

def safePair (security bits : ℕ) (scalar : IntegerBits) (first second : Fin (colors security)) : RationalResult :=
  let fc := canonicalCounter first.val
  let sc := canonicalCounter second.val
  let fs := BinarySafeMembership.current security fc.digits
  let ss := BinarySafeMembership.current security sc.digits
  let result := pair security bits scalar first second
  ⟨if fs.value && ss.value then result.data else zero,fc.work+sc.work+fs.work+ss.work+result.work+5⟩

theorem safePair_value (security bits : ℕ) (scalar : IntegerBits) (first second : Fin (colors security)) :
    (safePair security bits scalar first second).data.decode=
      if RationalBackgroundProfiles.Safe security first.val ∧ RationalBackgroundProfiles.Safe security second.val then
        RationalDiffuseResidualProgram.pair security bits scalar.decode first.val second.val else 0 := by
  have hf := BinarySafeMembership.current_value security (canonicalCounter first.val).digits
  have hs := BinarySafeMembership.current_value security (canonicalCounter second.val).digits
  simp only [canonicalCounter_value] at hf hs
  unfold safePair
  dsimp only
  split <;> rename_i h
  · have hp : (BinarySafeMembership.current security (canonicalCounter first.val).digits).value=true ∧
        (BinarySafeMembership.current security (canonicalCounter second.val).digits).value=true := by simpa only [Bool.and_eq_true] using h
    rw [if_pos ⟨hf.mp hp.1,hs.mp hp.2⟩,pair_value]
  · rw [if_neg (by intro hp; exact h (by simp only [hf.mpr hp.1,hs.mpr hp.2,Bool.and_self])),zero_value]

def safeReference (security : ℕ) (output : Fin (colors security)) : RationalResult :=
  let code := canonicalCounter output.val
  let result := BinarySafeProfile.current security code.digits
  ⟨result.data,code.work+result.work+2⟩

theorem safeReference_value (security : ℕ) (output : Fin (colors security)) :
    (safeReference security output).data.decode=RationalBackgroundProfiles.safe security output.val := by
  simp only [safeReference,BinarySafeProfile.current_value,canonicalCounter_value]

def uniformReference (security : ℕ) (_output : Fin (colors security)) : RationalResult :=
  let modulus := PublicParameterProgram.modulus security
  let count := ofCounter modulus.count
  let result := RationalBits.inverse count.data
  ⟨result.data,modulus.work+count.work+result.work+3⟩

theorem uniformReference_value (security : ℕ) (output : Fin (colors security)) :
    (uniformReference security output).data.decode=1/(colors security:ℚ) := by
  simp only [uniformReference,inverse_value,ofCounter_value,one_div]

noncomputable section
noncomputable def codeWorkPolynomial : Polynomial ℕ := 50*(BinaryFirstInverseProgram.colorsPolynomial+1)^2
noncomputable def inputPolynomial (scalarBits : Polynomial ℕ) : Polynomial ℕ := BinaryFirstInverseProgram.colorsPolynomial+scalarBits
noncomputable def pairHeightPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFairDiffuse.heightPolynomial precision (inputPolynomial scalarBits)
noncomputable def pairWorkPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  2*codeWorkPolynomial+BinaryFairDiffuse.workPolynomial precision (inputPolynomial scalarBits)+3
noncomputable def safePairWorkPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  2*codeWorkPolynomial+2*BinarySafeMembership.workPolynomial BinaryFirstInverseProgram.colorsPolynomial+
    pairWorkPolynomial precision scalarBits+5
noncomputable def safeHeightPolynomial : Polynomial ℕ := BinarySafeProfile.heightPolynomial BinaryFirstInverseProgram.colorsPolynomial
noncomputable def safeWorkPolynomial : Polynomial ℕ :=
  codeWorkPolynomial+BinarySafeProfile.workPolynomial BinaryFirstInverseProgram.colorsPolynomial+2
noncomputable def uniformWorkPolynomial : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+60*(BinaryFirstInverseProgram.colorsPolynomial+1)^2+
    primitiveWorkPolynomial BinaryFirstInverseProgram.colorsPolynomial+3

theorem code_bounds (security : ℕ) (output : Fin (colors security)) :
    (canonicalCounter output.val).digits.length ≤ BinaryFirstInverseProgram.colorsPolynomial.eval security ∧
      (canonicalCounter output.val).work ≤ codeWorkPolynomial.eval security := by
  have ho : output.val ≤ BinaryFirstInverseProgram.colorsPolynomial.eval security :=
    output.isLt.le.trans (BinaryFirstInverseProgram.colors_bound security)
  constructor
  · rw [canonicalCounter_length]
    exact (Nat.size_le.mpr (Nat.lt_two_pow_self (n := output.val))).trans ho
  · simp only [codeWorkPolynomial,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_ofNat,Polynomial.eval_one]
    exact (canonicalCounter_work output.val).trans (by gcongr)

theorem pair_bounds (security : ℕ) (precision scalarBits : Polynomial ℕ) (scalar : IntegerBits)
    (hs : scalar.digits.length ≤ scalarBits.eval security) (first second : Fin (colors security)) :
    HeightBound (pair security (precision.eval security) scalar first second).data.decode
      ((pairHeightPolynomial precision scalarBits).eval security) ∧
    (pair security (precision.eval security) scalar first second).work ≤ (pairWorkPolynomial precision scalarBits).eval security := by
  have hf := code_bounds security first
  have ht := code_bounds security second
  have he : (inputPolynomial scalarBits).eval security=BinaryFirstInverseProgram.colorsPolynomial.eval security+scalarBits.eval security := by
    simp only [inputPolynomial,Polynomial.eval_add]
  have hb := BinaryFairDiffuse.current_bounds security precision (inputPolynomial scalarBits) scalar
    (canonicalCounter first.val).digits (canonicalCounter second.val).digits
    (hs.trans (by rw [he]; omega)) (hf.1.trans (by rw [he]; omega)) (ht.1.trans (by rw [he]; omega))
  refine ⟨hb.1,?_⟩
  change (canonicalCounter first.val).work+(canonicalCounter second.val).work+_+3 ≤ _
  simp only [pairWorkPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
  omega

theorem safePair_bounds (security : ℕ) (precision scalarBits : Polynomial ℕ) (scalar : IntegerBits)
    (hs : scalar.digits.length ≤ scalarBits.eval security) (first second : Fin (colors security)) :
    HeightBound (safePair security (precision.eval security) scalar first second).data.decode
      ((pairHeightPolynomial precision scalarBits).eval security) ∧
    (safePair security (precision.eval security) scalar first second).work ≤ (safePairWorkPolynomial precision scalarBits).eval security := by
  have hp := pair_bounds security precision scalarBits scalar hs first second
  have hf := code_bounds security first
  have ht := code_bounds security second
  have wf := BinarySafeMembership.current_work security (canonicalCounter first.val).digits _ hf.1
  have wt := BinarySafeMembership.current_work security (canonicalCounter second.val).digits _ ht.1
  constructor
  · unfold safePair
    dsimp only
    split
    · exact hp.1
    · rw [zero_value]; exact HeightBound.zero.mono (Nat.zero_le _)
  · change (canonicalCounter first.val).work+(canonicalCounter second.val).work+_+_+_+5 ≤ _
    simp only [safePairWorkPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
    omega

theorem safeReference_bounds (security : ℕ) (output : Fin (colors security)) :
    HeightBound (safeReference security output).data.decode (safeHeightPolynomial.eval security) ∧
      (safeReference security output).work ≤ safeWorkPolynomial.eval security := by
  have hc := code_bounds security output
  have hs := BinarySafeProfile.current_bounds security (canonicalCounter output.val).digits _ hc.1
  refine ⟨hs.1,?_⟩
  change (canonicalCounter output.val).work+_+2 ≤ _
  simp only [safeWorkPolynomial,Polynomial.eval_add,Polynomial.eval_ofNat]
  omega

theorem uniformReference_bounds (security : ℕ) (output : Fin (colors security)) :
    HeightBound (uniformReference security output).data.decode (BinaryFirstInverseProgram.colorsPolynomial.eval security) ∧
      (uniformReference security output).work ≤ uniformWorkPolynomial.eval security := by
  let q := PublicParameterProgram.modulus security
  let count := ofCounter q.count
  have hq : q.count ≤ BinaryFirstInverseProgram.colorsPolynomial.eval security := BinaryFirstInverseProgram.colors_bound security
  have hh : HeightBound count.data.decode (BinaryFirstInverseProgram.colorsPolynomial.eval security) := by
    rw [ofCounter_value]; exact (HeightBound.nat_coarse q.count).mono hq
  have wq := PublicParameterProgram.modulus_work security
  have wc := (ofCounter_work q.count).trans (by gcongr : 60*(q.count+1)^2 ≤ 60*(BinaryFirstInverseProgram.colorsPolynomial.eval security+1)^2)
  have wi := inverse_work count.data (BinaryFirstInverseProgram.colorsPolynomial.eval security)
  constructor
  · change HeightBound (RationalBits.inverse count.data).data.decode _
    rw [inverse_value]; exact hh.inv
  · change q.work+count.work+(RationalBits.inverse count.data).work+3 ≤ _
    change q.work ≤ _ at wq
    change count.work ≤ _ at wc
    simp only [uniformWorkPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
      Polynomial.eval_ofNat,Polynomial.eval_one,PublicParameterProgram.workPolynomial_eval,primitiveWorkPolynomial_eval]
    omega

end
end CurrentAFT.BinaryDiffusePairLeaf
