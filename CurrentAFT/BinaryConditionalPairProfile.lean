import CurrentAFT.BinaryPairProgram
import CurrentAFT.BinaryDiffusePairLeaf
import CurrentAFT.RationalConditionalPairProgram

/-! # Both actual pair marginals, with a common retained scalar -/
namespace CurrentAFT.BinaryConditionalPairProfile
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryPairProgram.current
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def pair (security bits : ℕ) (scalar : IntegerBits) (primary first second : Fin (colors security)) : RationalResult :=
  let fc := canonicalCounter first.val
  let sc := canonicalCounter second.val
  let result := BinaryPairProgram.current security bits primary.val scalar.negative scalar.digits fc.digits sc.digits
  ⟨result.data,fc.work+sc.work+result.work+3⟩

theorem pair_value (security bits : ℕ) (scalar : IntegerBits) (primary first second : Fin (colors security)) :
    (pair security bits scalar primary first second).data.decode=LocalPairProgram.current security bits primary.val scalar.decode first.val second.val := by
  simp only [pair,BinaryPairProgram.current_value,canonicalCounter_value,IntegerBits.decode]

def current (security bits : ℕ) (scalar : IntegerBits) (primary output : Fin (colors security)) : RationalResult :=
  let first := sumFin (colors security) (fun other => pair security bits scalar primary output other)
  let second := sumFin (colors security) (fun other => pair security bits scalar primary other output)
  let result := RationalBits.add first.data second.data
  ⟨result.data,first.work+second.work+result.work+3⟩

theorem current_value (security bits : ℕ) (scalar : IntegerBits) (primary output : Fin (colors security)) :
    (current security bits scalar primary output).data.decode=
      RationalConditionalPairProgram.pairProfile security bits primary.val scalar.decode output.val := by
  simp only [current,RationalBits.add_value,sumFin_value,pair_value,RationalConditionalPairProgram.pairProfile]

noncomputable section
noncomputable def inputPolynomial (scalarBits : Polynomial ℕ) : Polynomial ℕ := BinaryFirstInverseProgram.colorsPolynomial+scalarBits
noncomputable def pairHeightPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryPairProgram.currentHeightPolynomial precision (inputPolynomial scalarBits)
noncomputable def pairWorkPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  2*BinaryDiffusePairLeaf.codeWorkPolynomial+BinaryPairProgram.currentWorkPolynomial precision (inputPolynomial scalarBits)+3
noncomputable def marginalHeightPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFirstInverseProgram.colorsPolynomial*(pairHeightPolynomial precision scalarBits+1)
noncomputable def marginalWorkPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFirstInverseProgram.colorsPolynomial*(pairWorkPolynomial precision scalarBits+
    primitiveWorkPolynomial ((BinaryFirstInverseProgram.colorsPolynomial+1)*(pairHeightPolynomial precision scalarBits+1))+2)+2
noncomputable def heightPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ := 2*marginalHeightPolynomial precision scalarBits+1
noncomputable def workPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  2*marginalWorkPolynomial precision scalarBits+primitiveWorkPolynomial (marginalHeightPolynomial precision scalarBits)+3

theorem pair_bounds (security : ℕ) (precision scalarBits : Polynomial ℕ) (scalar : IntegerBits)
    (hs : scalar.digits.length ≤ scalarBits.eval security) (primary first second : Fin (colors security)) :
    HeightBound (pair security (precision.eval security) scalar primary first second).data.decode
      ((pairHeightPolynomial precision scalarBits).eval security) ∧
    (pair security (precision.eval security) scalar primary first second).work ≤ (pairWorkPolynomial precision scalarBits).eval security := by
  let actualPrimary : FirstHistogram.Palette security := ⟨primary.val,by
    rw [← PublicParameterProgram.modulus_value security]; exact primary.isLt⟩
  have hf := BinaryDiffusePairLeaf.code_bounds security first
  have ht := BinaryDiffusePairLeaf.code_bounds security second
  have he : (inputPolynomial scalarBits).eval security=BinaryFirstInverseProgram.colorsPolynomial.eval security+scalarBits.eval security := by
    simp only [inputPolynomial,Polynomial.eval_add]
  have h := BinaryPairProgram.current_bounds security actualPrimary scalar.negative scalar.digits
    (canonicalCounter first.val).digits (canonicalCounter second.val).digits precision (inputPolynomial scalarBits)
    (hs.trans (by rw [he]; omega)) (hf.1.trans (by rw [he]; omega)) (ht.1.trans (by rw [he]; omega))
  dsimp only [actualPrimary] at h
  refine ⟨h.1,?_⟩
  change (canonicalCounter first.val).work+(canonicalCounter second.val).work+_+3 ≤ _
  simp only [pairWorkPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
  omega

theorem current_bounds (security : ℕ) (precision scalarBits : Polynomial ℕ) (scalar : IntegerBits)
    (hs : scalar.digits.length ≤ scalarBits.eval security) (primary output : Fin (colors security)) :
    HeightBound (current security (precision.eval security) scalar primary output).data.decode
      ((heightPolynomial precision scalarBits).eval security) ∧
    (current security (precision.eval security) scalar primary output).work ≤ (workPolynomial precision scalarBits).eval security := by
  let first := sumFin (colors security) (fun other => pair security (precision.eval security) scalar primary output other)
  let second := sumFin (colors security) (fun other => pair security (precision.eval security) scalar primary other output)
  have hf := sumFin_height (colors security) ((pairHeightPolynomial precision scalarBits).eval security)
    (fun other => pair security (precision.eval security) scalar primary output other)
    (fun other => (pair_bounds security precision scalarBits scalar hs primary output other).1)
  have ht := sumFin_height (colors security) ((pairHeightPolynomial precision scalarBits).eval security)
    (fun other => pair security (precision.eval security) scalar primary other output)
    (fun other => (pair_bounds security precision scalarBits scalar hs primary other output).1)
  have hq := BinaryFirstInverseProgram.colors_bound security
  have hh : colors security*((pairHeightPolynomial precision scalarBits).eval security+1) ≤
      (marginalHeightPolynomial precision scalarBits).eval security := by
    simp only [marginalHeightPolynomial,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_one]
    exact Nat.mul_le_mul_right _ hq
  have hf' : HeightBound first.data.decode ((marginalHeightPolynomial precision scalarBits).eval security) := hf.mono hh
  have ht' : HeightBound second.data.decode ((marginalHeightPolynomial precision scalarBits).eval security) := ht.mono hh
  have wf := sumFin_work (colors security) ((pairHeightPolynomial precision scalarBits).eval security)
    ((pairWorkPolynomial precision scalarBits).eval security)
    (fun other => pair security (precision.eval security) scalar primary output other)
    (fun other => (pair_bounds security precision scalarBits scalar hs primary output other).1)
    (fun other => (pair_bounds security precision scalarBits scalar hs primary output other).2)
  have wt := sumFin_work (colors security) ((pairHeightPolynomial precision scalarBits).eval security)
    ((pairWorkPolynomial precision scalarBits).eval security)
    (fun other => pair security (precision.eval security) scalar primary other output)
    (fun other => (pair_bounds security precision scalarBits scalar hs primary other output).1)
    (fun other => (pair_bounds security precision scalarBits scalar hs primary other output).2)
  have hb : colors security*((pairWorkPolynomial precision scalarBits).eval security+
      primitiveWorkBound ((colors security+1)*((pairHeightPolynomial precision scalarBits).eval security+1))+2)+2 ≤
      (marginalWorkPolynomial precision scalarBits).eval security := by
    simp only [marginalWorkPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
      Polynomial.eval_one,primitiveWorkPolynomial_eval]
    unfold primitiveWorkBound
    gcongr
  have wf' : first.work ≤ (marginalWorkPolynomial precision scalarBits).eval security := wf.trans hb
  have wt' : second.work ≤ (marginalWorkPolynomial precision scalarBits).eval security := wt.trans hb
  have wa := RationalBits.add_work first.data second.data ((marginalHeightPolynomial precision scalarBits).eval security) hf' ht'
  constructor
  · change HeightBound (RationalBits.add first.data second.data).data.decode _
    rw [RationalBits.add_value]
    convert hf'.add ht' using 1
    simp only [heightPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_one]
    omega
  · change first.work+second.work+(RationalBits.add first.data second.data).work+3 ≤ _
    simp only [workPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,primitiveWorkPolynomial_eval]
    omega

end
end CurrentAFT.BinaryConditionalPairProfile
