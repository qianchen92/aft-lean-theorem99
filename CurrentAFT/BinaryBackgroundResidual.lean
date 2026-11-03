import CurrentAFT.BinaryUnsafeArray
import CurrentAFT.RationalRootConvolutionCongr
import CurrentAFT.BinaryMassLiftInput
import CurrentAFT.RationalBackgroundDensities

/-! # Actual unsafe-root residual and its original primary mass lift -/
namespace CurrentAFT.BinaryBackgroundResidual
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryUnsafeArray.current BinaryRootConvolution.current BinaryBodyProgram.current
  BinaryMassLiftInput.current PublicParameterProgram.modulus

def profile (security bits : ℕ) (shift : IntegerBits) (output : List Bool) : RationalResult :=
  let cache := BinaryUnsafeArray.current security shift
  let convolution := BinaryRootConvolution.current security bits cache.profile output
  let body := BinaryBodyProgram.current security bits false output
  let product := RationalBits.multiply cache.total body.data
  let negative := RationalBits.negate product.data
  let result := RationalBits.add convolution.data negative.data
  ⟨result.data, cache.work+convolution.work+body.work+product.work+negative.work+result.work+6⟩

theorem profile_value (security bits : ℕ) (shift : IntegerBits) (output : List Bool) :
    (profile security bits shift output).data.decode=RationalBackgroundProfiles.residual security bits shift.decode (value output) := by
  unfold profile
  rw [RationalBits.add_value, RationalBits.negate_value, RationalBits.multiply_value,
    BinaryRootConvolution.current_of_entries security bits _ output
      (RationalBackgroundProfiles.unsafeProfile security shift.decode) (BinaryUnsafeArray.profile_value security shift),
    BinaryUnsafeArray.total_value, BinaryBodyProgram.current_value]
  simp only [RationalBackgroundProfiles.residual, sub_eq_add_neg]

def point (security bits : ℕ) (shift : IntegerBits)
    (output : Fin (BinaryFirstInverseProgram.colors security)) : RationalResult :=
  let code := canonicalCounter output.val
  let result := profile security bits shift code.digits
  ⟨result.data, code.work+result.work+2⟩

theorem point_value (security bits : ℕ) (shift : IntegerBits)
    (output : Fin (BinaryFirstInverseProgram.colors security)) :
    (point security bits shift output).data.decode=RationalBackgroundProfiles.residual security bits shift.decode output.val := by
  simp only [point, profile_value, canonicalCounter_value]

def current (security bits : ℕ) (shift : IntegerBits)
    (output : Fin (BinaryFirstInverseProgram.colors security)) : RationalResult :=
  BinaryMassLiftInput.current security bits (point security bits shift) output

theorem current_value (security bits : ℕ) (shift : IntegerBits)
    (output : Fin (BinaryFirstInverseProgram.colors security)) :
    (current security bits shift output).data.decode=RationalBackgroundDensities.residual security bits shift.decode output.val :=
  BinaryMassLiftInput.current_value security bits (point security bits shift)
    (RationalBackgroundProfiles.residual security bits shift.decode) output (point_value security bits shift)

noncomputable section
noncomputable def operandHeightPolynomial (precision shiftBits outputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryUnsafeArray.heightPolynomial shiftBits+
    BinaryRootConvolution.heightPolynomial precision outputBits (BinaryUnsafeArray.heightPolynomial shiftBits)+
    BinaryBodyProgram.currentHeightPolynomial precision outputBits
noncomputable def profileHeightPolynomial (precision shiftBits outputBits : Polynomial ℕ) : Polynomial ℕ :=
  3*operandHeightPolynomial precision shiftBits outputBits+1
noncomputable def profileWorkPolynomial (precision shiftBits outputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryUnsafeArray.workPolynomial shiftBits+
    BinaryRootConvolution.workPolynomial precision outputBits (BinaryUnsafeArray.heightPolynomial shiftBits)+
    BinaryBodyProgram.currentWorkPolynomial precision outputBits+
    3*primitiveWorkPolynomial (2*operandHeightPolynomial precision shiftBits outputBits)+6
noncomputable def pointHeightPolynomial (precision shiftBits : Polynomial ℕ) : Polynomial ℕ :=
  profileHeightPolynomial precision shiftBits BinaryFirstInverseProgram.colorsPolynomial
noncomputable def pointWorkPolynomial (precision shiftBits : Polynomial ℕ) : Polynomial ℕ :=
  50*(BinaryFirstInverseProgram.colorsPolynomial+1)^2+
    profileWorkPolynomial precision shiftBits BinaryFirstInverseProgram.colorsPolynomial+2
noncomputable def heightPolynomial (precision shiftBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryMassLiftInput.heightPolynomial precision (pointHeightPolynomial precision shiftBits)
noncomputable def workPolynomial (precision shiftBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryMassLiftInput.workPolynomial precision (pointHeightPolynomial precision shiftBits) (pointWorkPolynomial precision shiftBits)

theorem profile_bounds (security : ℕ) (precision shiftBits outputBits : Polynomial ℕ) (shift : IntegerBits) (output : List Bool)
    (hs : shift.digits.length ≤ shiftBits.eval security) (ho : output.length ≤ outputBits.eval security) :
    HeightBound (profile security (precision.eval security) shift output).data.decode
      ((profileHeightPolynomial precision shiftBits outputBits).eval security) ∧
      (profile security (precision.eval security) shift output).work≤(profileWorkPolynomial precision shiftBits outputBits).eval security := by
  let cache := BinaryUnsafeArray.current security shift
  let convolution := BinaryRootConvolution.current security (precision.eval security) cache.profile output
  let body := BinaryBodyProgram.current security (precision.eval security) false output
  let product := RationalBits.multiply cache.total body.data
  let negative := RationalBits.negate product.data
  let H := (operandHeightPolynomial precision shiftBits outputBits).eval security
  have hc := BinaryUnsafeArray.current_bounds security shift shiftBits hs
  have hv := BinaryRootConvolution.current_bounds security precision outputBits (BinaryUnsafeArray.heightPolynomial shiftBits)
    cache.profile output ho hc.1
  have hb := BinaryBodyProgram.current_height security false output precision outputBits ho
  have hH : H=(BinaryUnsafeArray.heightPolynomial shiftBits).eval security+
      (BinaryRootConvolution.heightPolynomial precision outputBits (BinaryUnsafeArray.heightPolynomial shiftBits)).eval security+
      (BinaryBodyProgram.currentHeightPolynomial precision outputBits).eval security := by
    simp only [H, operandHeightPolynomial, Polynomial.eval_add]
  have hcache : HeightBound cache.total.decode H := hc.2.1.mono (by rw [hH]; omega)
  have hconv : HeightBound convolution.data.decode H := hv.1.mono (by rw [hH]; omega)
  have hbody : HeightBound body.data.decode H := hb.mono (by rw [hH]; omega)
  have hprod : HeightBound product.data.decode (2*H) := by
    rw [RationalBits.multiply_value]
    exact (hcache.mul hbody).mono (by omega)
  have hnegative : HeightBound negative.data.decode (2*H) := by rw [RationalBits.negate_value]; exact hprod.neg
  have wc : cache.work≤(BinaryUnsafeArray.workPolynomial shiftBits).eval security := hc.2.2
  have wv : convolution.work≤(BinaryRootConvolution.workPolynomial precision outputBits (BinaryUnsafeArray.heightPolynomial shiftBits)).eval security := hv.2
  have wb := BinaryBodyProgram.current_polynomial_work security false output precision outputBits ho
  change body.work≤_ at wb
  have wp : product.work≤primitiveWorkBound (2*H) := RationalBits.multiply_work _ _ (2*H)
    (hcache.mono (by omega)) (hbody.mono (by omega))
  have wn : negative.work≤primitiveWorkBound (2*H) := RationalBits.negate_work product.data (2*H)
  have wa := RationalBits.add_work convolution.data negative.data (2*H) (hconv.mono (by omega)) hnegative
  constructor
  · change HeightBound (RationalBits.add convolution.data negative.data).data.decode _
    rw [RationalBits.add_value]
    exact (hconv.add hnegative).mono (by
      simp only [profileHeightPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one]
      change H+2*H+1≤3*H+1
      omega)
  · change cache.work+convolution.work+body.work+product.work+negative.work+
      (RationalBits.add convolution.data negative.data).work+6≤_
    simp only [profileWorkPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, primitiveWorkPolynomial_eval]
    change _≤(BinaryUnsafeArray.workPolynomial shiftBits).eval security+
      (BinaryRootConvolution.workPolynomial precision outputBits (BinaryUnsafeArray.heightPolynomial shiftBits)).eval security+
      (BinaryBodyProgram.currentWorkPolynomial precision outputBits).eval security+3*primitiveWorkBound (2*H)+6
    omega

theorem point_bounds (security : ℕ) (precision shiftBits : Polynomial ℕ) (shift : IntegerBits)
    (hs : shift.digits.length ≤ shiftBits.eval security) (output : Fin (BinaryFirstInverseProgram.colors security)) :
    HeightBound (point security (precision.eval security) shift output).data.decode ((pointHeightPolynomial precision shiftBits).eval security) ∧
      (point security (precision.eval security) shift output).work≤(pointWorkPolynomial precision shiftBits).eval security := by
  have ho := output.isLt.le.trans (BinaryFirstInverseProgram.colors_bound security)
  have hl : (canonicalCounter output.val).digits.length≤BinaryFirstInverseProgram.colorsPolynomial.eval security := by
    rw [canonicalCounter_length]
    exact (Nat.size_le.mpr (Nat.lt_two_pow_self (n := output.val))).trans ho
  have h := profile_bounds security precision shiftBits BinaryFirstInverseProgram.colorsPolynomial shift (canonicalCounter output.val).digits hs hl
  constructor
  · exact h.1
  · have wc := (canonicalCounter_work output.val).trans
      (Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (Nat.add_le_add_right ho 1) 2))
    change _+_+2≤_
    simp only [pointWorkPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_ofNat, Polynomial.eval_one]
    omega

theorem current_bounds (security : ℕ) (precision shiftBits : Polynomial ℕ) (shift : IntegerBits)
    (hs : shift.digits.length ≤ shiftBits.eval security) (output : Fin (BinaryFirstInverseProgram.colors security)) :
    HeightBound (current security (precision.eval security) shift output).data.decode ((heightPolynomial precision shiftBits).eval security) ∧
      (current security (precision.eval security) shift output).work≤(workPolynomial precision shiftBits).eval security :=
  BinaryMassLiftInput.current_bounds security precision (pointHeightPolynomial precision shiftBits) (pointWorkPolynomial precision shiftBits)
    (point security (precision.eval security) shift) output (fun color => (point_bounds security precision shiftBits shift hs color).1)
    (fun color => (point_bounds security precision shiftBits shift hs color).2)

end
end CurrentAFT.BinaryBackgroundResidual
