import CurrentAFT.BinaryDiffuseCanonical
import CurrentAFT.BinaryRootConvolutionInput

/-! # Actual double-root smoothing of the joint safe diffuse seed -/
namespace CurrentAFT.BinaryDiffuseResidual
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryRootConvolutionInput.current BinaryDiffuseCanonical.seed BinaryDiffuseCanonical.uniform
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def inner (security bits : ℕ) (scalar : IntegerBits) (first second : Fin (colors security)) : RationalResult :=
  let code := canonicalCounter second.val
  let result := BinaryRootConvolutionInput.current security bits (BinaryDiffuseCanonical.seed security bits scalar first) code.digits
  ⟨result.data,code.work+result.work+2⟩

theorem inner_value (security bits : ℕ) (scalar : IntegerBits) (first second : Fin (colors security)) :
    (inner security bits scalar first second).data.decode=
      RationalBackgroundProfiles.convolution security bits (RationalDiffuseResidualProgram.seed security bits scalar.decode first.val) second.val := by
  change (BinaryRootConvolutionInput.current _ _ _ _).data.decode=_
  rw [BinaryRootConvolutionInput.current_value _ _ _ _ _ (BinaryDiffuseCanonical.seed_value security bits scalar first),canonicalCounter_value]

def smoothed (security bits : ℕ) (scalar : IntegerBits) (first second : Fin (colors security)) : RationalResult :=
  let code := canonicalCounter first.val
  let result := BinaryRootConvolutionInput.current security bits (fun left => inner security bits scalar left second) code.digits
  ⟨result.data,code.work+result.work+2⟩

theorem smoothed_value (security bits : ℕ) (scalar : IntegerBits) (first second : Fin (colors security)) :
    (smoothed security bits scalar first second).data.decode=
      RationalDiffuseResidualProgram.smoothedSeed security bits scalar.decode first.val second.val := by
  change (BinaryRootConvolutionInput.current _ _ _ _).data.decode=_
  rw [BinaryRootConvolutionInput.current_value _ _ _
    (fun left => RationalBackgroundProfiles.convolution security bits (RationalDiffuseResidualProgram.seed security bits scalar.decode left) second.val)
    _ (fun left => inner_value security bits scalar left second),canonicalCounter_value]
  rfl

def current (security bits : ℕ) (scalar : IntegerBits) (first second : Fin (colors security)) : RationalResult :=
  let uniform := BinaryDiffuseCanonical.uniform security bits scalar first second
  let smooth := smoothed security bits scalar first second
  let negative := RationalBits.negate smooth.data
  let result := RationalBits.add uniform.data negative.data
  ⟨result.data,uniform.work+smooth.work+negative.work+result.work+4⟩

theorem current_value (security bits : ℕ) (scalar : IntegerBits) (first second : Fin (colors security)) :
    (current security bits scalar first second).data.decode=RationalDiffuseResidualProgram.residual security bits scalar.decode first.val second.val := by
  simp only [current,RationalBits.add_value,RationalBits.negate_value,BinaryDiffuseCanonical.uniform_value,smoothed_value,
    RationalDiffuseResidualProgram.residual,sub_eq_add_neg]

noncomputable section
noncomputable def innerHeightPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryRootConvolutionInput.heightPolynomial precision BinaryFirstInverseProgram.colorsPolynomial
    (BinaryDiffuseCanonical.seedHeightPolynomial precision scalarBits)
noncomputable def innerWorkPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryDiffusePairLeaf.codeWorkPolynomial+
    BinaryRootConvolutionInput.workPolynomial precision BinaryFirstInverseProgram.colorsPolynomial
      (BinaryDiffuseCanonical.seedHeightPolynomial precision scalarBits) (BinaryDiffuseCanonical.seedWorkPolynomial precision scalarBits)+2
noncomputable def smoothedHeightPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryRootConvolutionInput.heightPolynomial precision BinaryFirstInverseProgram.colorsPolynomial (innerHeightPolynomial precision scalarBits)
noncomputable def smoothedWorkPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryDiffusePairLeaf.codeWorkPolynomial+
    BinaryRootConvolutionInput.workPolynomial precision BinaryFirstInverseProgram.colorsPolynomial
      (innerHeightPolynomial precision scalarBits) (innerWorkPolynomial precision scalarBits)+2
noncomputable def operandPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryDiffuseCanonical.uniformHeightPolynomial precision scalarBits+smoothedHeightPolynomial precision scalarBits
noncomputable def heightPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ := operandPolynomial precision scalarBits+1
noncomputable def workPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryDiffuseCanonical.uniformWorkPolynomial precision scalarBits+smoothedWorkPolynomial precision scalarBits+
    2*primitiveWorkPolynomial (operandPolynomial precision scalarBits)+4

theorem inner_bounds (security : ℕ) (precision scalarBits : Polynomial ℕ) (scalar : IntegerBits)
    (hs : scalar.digits.length ≤ scalarBits.eval security) (first second : Fin (colors security)) :
    HeightBound (inner security (precision.eval security) scalar first second).data.decode
      ((innerHeightPolynomial precision scalarBits).eval security) ∧
    (inner security (precision.eval security) scalar first second).work ≤ (innerWorkPolynomial precision scalarBits).eval security := by
  have hc := BinaryDiffusePairLeaf.code_bounds security second
  have h := BinaryRootConvolutionInput.current_bounds security precision BinaryFirstInverseProgram.colorsPolynomial
    (BinaryDiffuseCanonical.seedHeightPolynomial precision scalarBits) (BinaryDiffuseCanonical.seedWorkPolynomial precision scalarBits)
    (BinaryDiffuseCanonical.seed security (precision.eval security) scalar first) (canonicalCounter second.val).digits hc.1
    (fun color => (BinaryDiffuseCanonical.seed_bounds security precision scalarBits scalar hs first color).1)
    (fun color => (BinaryDiffuseCanonical.seed_bounds security precision scalarBits scalar hs first color).2)
  refine ⟨h.1,?_⟩
  change (canonicalCounter second.val).work+_+2 ≤ _
  simp only [innerWorkPolynomial,Polynomial.eval_add,Polynomial.eval_ofNat]
  omega

theorem smoothed_bounds (security : ℕ) (precision scalarBits : Polynomial ℕ) (scalar : IntegerBits)
    (hs : scalar.digits.length ≤ scalarBits.eval security) (first second : Fin (colors security)) :
    HeightBound (smoothed security (precision.eval security) scalar first second).data.decode
      ((smoothedHeightPolynomial precision scalarBits).eval security) ∧
    (smoothed security (precision.eval security) scalar first second).work ≤ (smoothedWorkPolynomial precision scalarBits).eval security := by
  have hc := BinaryDiffusePairLeaf.code_bounds security first
  have h := BinaryRootConvolutionInput.current_bounds security precision BinaryFirstInverseProgram.colorsPolynomial
    (innerHeightPolynomial precision scalarBits) (innerWorkPolynomial precision scalarBits)
    (fun left => inner security (precision.eval security) scalar left second) (canonicalCounter first.val).digits hc.1
    (fun left => (inner_bounds security precision scalarBits scalar hs left second).1)
    (fun left => (inner_bounds security precision scalarBits scalar hs left second).2)
  refine ⟨h.1,?_⟩
  change (canonicalCounter first.val).work+_+2 ≤ _
  simp only [smoothedWorkPolynomial,Polynomial.eval_add,Polynomial.eval_ofNat]
  omega

theorem current_bounds (security : ℕ) (precision scalarBits : Polynomial ℕ) (scalar : IntegerBits)
    (hs : scalar.digits.length ≤ scalarBits.eval security) (first second : Fin (colors security)) :
    HeightBound (current security (precision.eval security) scalar first second).data.decode
      ((heightPolynomial precision scalarBits).eval security) ∧
    (current security (precision.eval security) scalar first second).work ≤ (workPolynomial precision scalarBits).eval security := by
  let uniform := BinaryDiffuseCanonical.uniform security (precision.eval security) scalar first second
  let smooth := smoothed security (precision.eval security) scalar first second
  let negative := RationalBits.negate smooth.data
  let B := (operandPolynomial precision scalarBits).eval security
  have hB : B=(BinaryDiffuseCanonical.uniformHeightPolynomial precision scalarBits).eval security+
      (smoothedHeightPolynomial precision scalarBits).eval security := by simp only [B,operandPolynomial,Polynomial.eval_add]
  have hu := BinaryDiffuseCanonical.uniform_bounds security precision scalarBits scalar hs first second
  have hs := smoothed_bounds security precision scalarBits scalar hs first second
  change HeightBound uniform.data.decode _ ∧ uniform.work ≤ _ at hu
  change HeightBound smooth.data.decode _ ∧ smooth.work ≤ _ at hs
  have hn : HeightBound negative.data.decode ((smoothedHeightPolynomial precision scalarBits).eval security) := by
    rw [RationalBits.negate_value]; exact hs.1.neg
  have wn : negative.work ≤ primitiveWorkBound B := RationalBits.negate_work smooth.data B
  have wa := RationalBits.add_work uniform.data negative.data B (hu.1.mono (by rw [hB]; omega)) (hn.mono (by rw [hB]; omega))
  constructor
  · change HeightBound (RationalBits.add uniform.data negative.data).data.decode _
    rw [RationalBits.add_value]
    simpa only [heightPolynomial,operandPolynomial,Polynomial.eval_add,Polynomial.eval_one] using hu.1.add hn
  · change uniform.work+smooth.work+negative.work+(RationalBits.add uniform.data negative.data).work+4 ≤ _
    simp only [workPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,primitiveWorkPolynomial_eval]
    change _ ≤ (BinaryDiffuseCanonical.uniformWorkPolynomial precision scalarBits).eval security+
      (smoothedWorkPolynomial precision scalarBits).eval security+2*primitiveWorkBound B+4
    omega

end
end CurrentAFT.BinaryDiffuseResidual
