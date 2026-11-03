import CurrentAFT.BinaryPairProgram
import CurrentAFT.BinaryDensityInverseTensor

/-! The local pair reads its two endpoints from the stored joint four-word. -/
namespace CurrentAFT.BinaryFourPointPair
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def current (security bits : ℕ) (primary : Fin (colors security)) (scalar : IntegerBits)
    (word : Vector (Fin (colors security)) 4) : RationalResult :=
  let first := readVector (BinaryDensityInverseTensor.first security) word 1
  let second := readVector (BinaryDensityInverseTensor.first security) word 2
  let firstCode := canonicalCounter first.value.val
  let secondCode := canonicalCounter second.value.val
  let pair := BinaryPairProgram.current security bits primary.val scalar.negative scalar.digits firstCode.digits secondCode.digits
  ⟨pair.data,first.work+second.work+firstCode.work+secondCode.work+pair.work+5⟩

theorem current_value (security bits : ℕ) (primary : Fin (colors security)) (scalar : IntegerBits)
    (word : Vector (Fin (colors security)) 4) :
    (current security bits primary scalar word).data.decode = LocalPairProgram.current security bits primary.val scalar.decode
      (word.get 1).val (word.get 2).val := by
  simp only [current, BinaryPairProgram.current_value, readVector_value, canonicalCounter_value, IntegerBits.decode]

noncomputable section
noncomputable def inputPolynomial (inputBits : Polynomial ℕ) : Polynomial ℕ := inputBits+BinaryFirstInverseProgram.colorsPolynomial
noncomputable def heightPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryPairProgram.currentHeightPolynomial precision (inputPolynomial inputBits)
noncomputable def workPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  100*(BinaryFirstInverseProgram.colorsPolynomial+1)^2+35+
    BinaryPairProgram.currentWorkPolynomial precision (inputPolynomial inputBits)

theorem current_bounds (security : ℕ) (precision inputBits : Polynomial ℕ) (primary : Fin (colors security))
    (scalar : IntegerBits) (word : Vector (Fin (colors security)) 4) (hs : scalar.digits.length ≤ inputBits.eval security) :
    HeightBound (current security (precision.eval security) primary scalar word).data.decode ((heightPolynomial precision inputBits).eval security) ∧
      (current security (precision.eval security) primary scalar word).work ≤ (workPolynomial precision inputBits).eval security := by
  have hq := BinaryFirstInverseProgram.colors_bound security
  have hc (color : Fin (colors security)) : color.val ≤ BinaryFirstInverseProgram.colorsPolynomial.eval security := color.isLt.le.trans hq
  have hl (color : Fin (colors security)) : (canonicalCounter color.val).digits.length ≤ (inputPolynomial inputBits).eval security := by
    rw [canonicalCounter_length]
    apply ((Nat.size_le.mpr (Nat.lt_two_pow_self (n:=color.val))).trans (hc color)).trans
    simp only [inputPolynomial, Polynomial.eval_add]; omega
  have hh := BinaryPairProgram.current_bounds security
    ⟨primary.val, by rw [← PublicParameterProgram.modulus_value]; exact primary.isLt⟩ scalar.negative scalar.digits
    (canonicalCounter (readVector (BinaryDensityInverseTensor.first security) word 1).value.val).digits
    (canonicalCounter (readVector (BinaryDensityInverseTensor.first security) word 2).value.val).digits
    precision (inputPolynomial inputBits) (hs.trans (by simp only [inputPolynomial, Polynomial.eval_add]; omega)) (hl _) (hl _)
  dsimp only at hh
  constructor
  · exact hh.1
  · have hfirst := readVector_work (BinaryDensityInverseTensor.first security) word 1
    have hsecond := readVector_work (BinaryDensityInverseTensor.first security) word 2
    have hcode (color : Fin (colors security)) : (canonicalCounter color.val).work ≤ 50*(BinaryFirstInverseProgram.colorsPolynomial.eval security+1)^2 :=
      (canonicalCounter_work color.val).trans (Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (Nat.add_le_add_right (hc color) 1) 2))
    have hf := hcode (readVector (BinaryDensityInverseTensor.first security) word 1).value
    have ht := hcode (readVector (BinaryDensityInverseTensor.first security) word 2).value
    change _+_+_+_+_+5 ≤ _
    simp only [workPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat, Polynomial.eval_one]
    omega

end
end CurrentAFT.BinaryFourPointPair
