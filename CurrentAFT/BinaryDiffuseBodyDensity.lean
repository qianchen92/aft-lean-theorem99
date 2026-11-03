import CurrentAFT.BinaryDiffuseCanonical
import CurrentAFT.BinaryReferenceTables

/-! # The actual diffuse body-pair density on binary reference atoms -/
namespace CurrentAFT.BinaryDiffuseBodyDensity
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryReferenceTables.current BinaryDiffuseCanonical.seed
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def current (security bits : ℕ) (scalar : IntegerBits) (first second : Fin (colors security)) : RationalResult :=
  let seed := BinaryDiffuseCanonical.seed security bits scalar first second
  let refs := BinaryReferenceTables.current security bits
  let f := readVector zero refs.center first
  let s := readVector zero refs.center second
  let denominator := RationalBits.multiply f.value s.value
  let inverse := RationalBits.inverse denominator.data
  let result := RationalBits.multiply seed.data inverse.data
  ⟨result.data,seed.work+refs.work+f.work+s.work+denominator.work+inverse.work+result.work+7⟩

theorem current_value (security bits : ℕ) (scalar : IntegerBits) (first second : Fin (colors security)) :
    (current security bits scalar first second).data.decode=
      RationalDiffuseResidualProgram.bodyDensity security bits scalar.decode first.val second.val := by
  simp only [current,RationalBits.multiply_value,inverse_value,readVector_value,BinaryReferenceTables.center_value,
    BinaryDiffuseCanonical.seed_value,RationalDiffuseResidualProgram.bodyDensity,div_eq_mul_inv]

noncomputable section
noncomputable def operandPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryDiffuseCanonical.seedHeightPolynomial precision scalarBits+2*BinaryReferenceTables.heightPolynomial precision
noncomputable def heightPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ := operandPolynomial precision scalarBits
noncomputable def workPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryDiffuseCanonical.seedWorkPolynomial precision scalarBits+BinaryReferenceTables.currentWorkPolynomial precision+
    6*BinaryFirstInverseProgram.colorsPolynomial+6+3*primitiveWorkPolynomial (operandPolynomial precision scalarBits)+7

theorem current_bounds (security : ℕ) (precision scalarBits : Polynomial ℕ) (scalar : IntegerBits)
    (hs : scalar.digits.length ≤ scalarBits.eval security) (first second : Fin (colors security)) :
    HeightBound (current security (precision.eval security) scalar first second).data.decode
      ((heightPolynomial precision scalarBits).eval security) ∧
    (current security (precision.eval security) scalar first second).work ≤ (workPolynomial precision scalarBits).eval security := by
  let seed := BinaryDiffuseCanonical.seed security (precision.eval security) scalar first second
  let refs := BinaryReferenceTables.current security (precision.eval security)
  let f := readVector zero refs.center first
  let s := readVector zero refs.center second
  let denominator := RationalBits.multiply f.value s.value
  let inverse := RationalBits.inverse denominator.data
  let H := (operandPolynomial precision scalarBits).eval security
  have hH : H=(BinaryDiffuseCanonical.seedHeightPolynomial precision scalarBits).eval security+
      2*(BinaryReferenceTables.heightPolynomial precision).eval security := by
    simp only [H,operandPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
  have hp := BinaryDiffuseCanonical.seed_bounds security precision scalarBits scalar hs first second
  have hr := BinaryReferenceTables.current_bounds security precision
  have hf : HeightBound f.value.decode ((BinaryReferenceTables.heightPolynomial precision).eval security) := by
    rw [readVector_value]; exact hr.2.1 first
  have hs : HeightBound s.value.decode ((BinaryReferenceTables.heightPolynomial precision).eval security) := by
    rw [readVector_value]; exact hr.2.1 second
  have hd : HeightBound denominator.data.decode (2*(BinaryReferenceTables.heightPolynomial precision).eval security) := by
    rw [RationalBits.multiply_value]; convert hf.mul hs using 1; omega
  have hi : HeightBound inverse.data.decode (2*(BinaryReferenceTables.heightPolynomial precision).eval security) := by
    rw [inverse_value]; exact hd.inv
  have wd := RationalBits.multiply_work f.value s.value H (hf.mono (by rw [hH]; omega)) (hs.mono (by rw [hH]; omega))
  have wi : inverse.work ≤ primitiveWorkBound H := inverse_work denominator.data H
  have wm := RationalBits.multiply_work seed.data inverse.data H (hp.1.mono (by rw [hH]; omega)) (hi.mono (by rw [hH]; omega))
  have wf := readVector_work zero refs.center first
  have ws := readVector_work zero refs.center second
  have wq := BinaryFirstInverseProgram.colors_bound security
  have wr : refs.work ≤ (BinaryReferenceTables.currentWorkPolynomial precision).eval security := hr.2.2.2.2
  have wp : seed.work ≤ (BinaryDiffuseCanonical.seedWorkPolynomial precision scalarBits).eval security := hp.2
  constructor
  · change HeightBound (RationalBits.multiply seed.data inverse.data).data.decode _
    rw [RationalBits.multiply_value]
    exact (hp.1.mul hi).mono (by rw [heightPolynomial,← hH])
  · change seed.work+refs.work+f.work+s.work+denominator.work+inverse.work+(RationalBits.multiply seed.data inverse.data).work+7 ≤ _
    change f.work ≤ _ at wf
    change s.work ≤ _ at ws
    simp only [workPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,primitiveWorkPolynomial_eval]
    change _ ≤ (BinaryDiffuseCanonical.seedWorkPolynomial precision scalarBits).eval security+
      (BinaryReferenceTables.currentWorkPolynomial precision).eval security+6*BinaryFirstInverseProgram.colorsPolynomial.eval security+6+
      3*primitiveWorkBound H+7
    change (PublicParameterProgram.modulus security).count ≤ _ at wq
    dsimp only [seed,refs,denominator,inverse,f,s] at wd wi wm wf ws wr wp ⊢
    omega

end
end CurrentAFT.BinaryDiffuseBodyDensity
