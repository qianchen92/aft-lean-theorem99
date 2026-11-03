import CurrentAFT.BinaryActivationProgram
import CurrentAFT.BinaryMarkedCurrent

/-! # The complete actual pair entry on binary rational data

This executes activation, both physical branches and all rational mixing
operations. Its semantic error is the already proved simultaneous error
for the true current pair law; its work is derived from actual operands.
-/
namespace CurrentAFT.BinaryPairProgram
open AFT GaussianSource RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def current (security bits primary : ℕ) (sourceSign : Bool) (source first second : List Bool) : RationalResult :=
  let rate := BinaryActivationProgram.current security bits
  let diffuse := BinaryDiffuseCurrent.current security bits primary sourceSign source first second
  let marked := BinaryMarkedCurrent.current security bits primary sourceSign source first second
  let negativeRate := RationalBits.negate rate.data
  let remaining := RationalBits.add one negativeRate.data
  let diffuseTerm := RationalBits.multiply remaining.data diffuse.data
  let markedTerm := RationalBits.multiply rate.data marked.data
  let result := RationalBits.add diffuseTerm.data markedTerm.data
  ⟨result.data, rate.work + diffuse.work + marked.work + negativeRate.work + remaining.work +
    diffuseTerm.work + markedTerm.work + result.work + 8⟩

theorem current_value (security bits primary : ℕ) (sourceSign : Bool) (source first second : List Bool) :
    (current security bits primary sourceSign source first second).data.decode =
      LocalPairProgram.current security bits primary (signedValue sourceSign source) (value first) (value second) := by
  simp only [current, RationalBits.add_value, RationalBits.multiply_value, RationalBits.negate_value, one_value,
    BinaryActivationProgram.current_value, BinaryDiffuseCurrent.current_value, BinaryMarkedCurrent.current_value,
    LocalPairProgram.current, sub_eq_add_neg]

noncomputable section
open scoped Classical

theorem current_error (security bits : ℕ) (primary first second : FirstHistogram.Palette security)
    (source : FirstHistogram.Scalar security) (sourceSign : Bool) (sourceCode firstCode secondCode : List Bool)
    (hs : signedValue sourceSign sourceCode = source.val)
    (hf : value firstCode = first.val) (ht : value secondCode = second.val) :
    |((current security bits primary.val sourceSign sourceCode firstCode secondCode).data.decode : ℝ) -
      (LocalReferenceEnergy.pairAt security primary source).weight (first, second)| ≤ 3/(2:ℝ)^bits := by
  rw [current_value, hs, hf, ht]
  exact LocalPairProgram.current_error security bits primary first second source

noncomputable def diffuseHeightPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  let count := 2*(Polynomial.X+2)^2+1
  count*(count*(BinaryDiffuseProgram.termHeightPolynomial (BinaryDiffuseCurrent.parameterPolynomial inputBits)
    (500000000*((Polynomial.X+2)^2+precision+2)^6)+1)+1)
noncomputable def markedHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  let count := 2*(Polynomial.X+2)^2+1
  count*(count*(2*(500000000*((Polynomial.X+2)^2+precision+2)^6)+4*(Polynomial.X+2)^48+3+1)+1)
noncomputable def currentHeightPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  2*BinaryActivationProgram.currentHeightPolynomial precision + diffuseHeightPolynomial precision inputBits +
    markedHeightPolynomial precision + 10

theorem diffuseHeightPolynomial_eval (precision inputBits : Polynomial ℕ) (security : ℕ) :
    (diffuseHeightPolynomial precision inputBits).eval security =
      BinaryDiffuseCurrent.currentHeight security (precision.eval security) (inputBits.eval security) := by
  simp only [diffuseHeightPolynomial, BinaryDiffuseCurrent.currentHeight, BinaryDiffuseProgram.sumHeight,
    BinaryDiffuseProgram.termHeightPolynomial, BinaryDiffuseProgram.termHeight,
    BinaryDiffuseProgram.averageHeightPolynomial, BinaryDiffuseProgram.averageHeight,
    BinaryDiffuseProgram.coinIntegerPolynomial, BinaryDiffuseProgram.coinIntegerBound,
    BinaryDiffuseCurrent.parameterPolynomial_eval, BinaryDiffuseProgram.gaussianHeight, CurrentGaussianBits.budget,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat,
    Polynomial.eval_one]

theorem markedHeightPolynomial_eval (precision : Polynomial ℕ) (security : ℕ) :
    (markedHeightPolynomial precision).eval security = BinaryMarkedCurrent.currentHeight security (precision.eval security) := by
  simp only [markedHeightPolynomial, BinaryMarkedCurrent.currentHeight, BinaryGaussianAverage.sumHeight,
    BinaryGaussianAverage.termHeight, BinaryGaussianAverage.gaussianHeight, CurrentGaussianBits.budget,
    BinaryMarkedKernel.averageHeight, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_one]
  ring

noncomputable def currentWorkPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryActivationProgram.currentWorkPolynomial precision + BinaryDiffuseCurrent.currentWorkPolynomial precision inputBits +
    BinaryMarkedCurrent.currentWorkPolynomial precision inputBits +
    5*primitiveWorkPolynomial (currentHeightPolynomial precision inputBits) + 8

theorem current_bounds (security : ℕ) (primary : FirstHistogram.Palette security) (sourceSign : Bool)
    (source first second : List Bool) (precision inputBits : Polynomial ℕ)
    (hs : source.length ≤ inputBits.eval security) (hf : first.length ≤ inputBits.eval security)
    (ht : second.length ≤ inputBits.eval security) :
    HeightBound (current security (precision.eval security) primary.val sourceSign source first second).data.decode
      ((currentHeightPolynomial precision inputBits).eval security) ∧
    (current security (precision.eval security) primary.val sourceSign source first second).work ≤
      (currentWorkPolynomial precision inputBits).eval security := by
  let rate := BinaryActivationProgram.current security (precision.eval security)
  let diffuse := BinaryDiffuseCurrent.current security (precision.eval security) primary.val sourceSign source first second
  let marked := BinaryMarkedCurrent.current security (precision.eval security) primary.val sourceSign source first second
  let negativeRate := RationalBits.negate rate.data
  let remaining := RationalBits.add one negativeRate.data
  let diffuseTerm := RationalBits.multiply remaining.data diffuse.data
  let markedTerm := RationalBits.multiply rate.data marked.data
  let height := (currentHeightPolynomial precision inputBits).eval security
  have hheight : height = 2*BinaryActivationProgram.currentHeight security (precision.eval security) +
      BinaryDiffuseCurrent.currentHeight security (precision.eval security) (inputBits.eval security) +
      BinaryMarkedCurrent.currentHeight security (precision.eval security) + 10 := by
    simp only [height, currentHeightPolynomial, BinaryActivationProgram.currentHeightPolynomial_eval,
      diffuseHeightPolynomial_eval, markedHeightPolynomial_eval, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat]
  have hr : HeightBound rate.data.decode (BinaryActivationProgram.currentHeight security (precision.eval security)) :=
    (BinaryActivationProgram.current_bounds security _).1
  have hd : HeightBound diffuse.data.decode (BinaryDiffuseCurrent.currentHeight security (precision.eval security) (inputBits.eval security)) :=
    BinaryDiffuseCurrent.current_height security _ primary sourceSign source first second _ hs hf ht
  have hm : HeightBound marked.data.decode (BinaryMarkedCurrent.currentHeight security (precision.eval security)) :=
    BinaryMarkedCurrent.current_height security _ primary.val sourceSign source first second
  have hn : HeightBound negativeRate.data.decode (BinaryActivationProgram.currentHeight security (precision.eval security)) := by
    rw [RationalBits.negate_value]; exact hr.neg
  have hremaining : HeightBound remaining.data.decode (BinaryActivationProgram.currentHeight security (precision.eval security)+1) := by
    rw [RationalBits.add_value, one_value]
    exact (HeightBound.one.add hn).mono (by omega)
  have hleft : HeightBound diffuseTerm.data.decode
      (BinaryActivationProgram.currentHeight security (precision.eval security)+1+
        BinaryDiffuseCurrent.currentHeight security (precision.eval security) (inputBits.eval security)) := by
    rw [RationalBits.multiply_value]; exact hremaining.mul hd
  have hright : HeightBound markedTerm.data.decode
      (BinaryActivationProgram.currentHeight security (precision.eval security)+
        BinaryMarkedCurrent.currentHeight security (precision.eval security)) := by
    rw [RationalBits.multiply_value]; exact hr.mul hm
  have wr : rate.work ≤ (BinaryActivationProgram.currentWorkPolynomial precision).eval security :=
    BinaryActivationProgram.current_polynomial_work precision security
  have wd : diffuse.work ≤ (BinaryDiffuseCurrent.currentWorkPolynomial precision inputBits).eval security :=
    BinaryDiffuseCurrent.current_polynomial_work security primary sourceSign source first second precision inputBits hs hf ht
  have wm : marked.work ≤ (BinaryMarkedCurrent.currentWorkPolynomial precision inputBits).eval security :=
    BinaryMarkedCurrent.current_polynomial_work security primary sourceSign source first second precision inputBits hs hf ht
  have wn : negativeRate.work ≤ primitiveWorkBound height := RationalBits.negate_work _ _
  have wremaining : remaining.work ≤ primitiveWorkBound height :=
    RationalBits.add_work one negativeRate.data height
      (by rw [one_value]; exact HeightBound.one.mono (by omega)) (hn.mono (by omega))
  have wleft : diffuseTerm.work ≤ primitiveWorkBound height :=
    RationalBits.multiply_work _ _ height (hremaining.mono (by omega)) (hd.mono (by omega))
  have wright : markedTerm.work ≤ primitiveWorkBound height :=
    RationalBits.multiply_work _ _ height (hr.mono (by omega)) (hm.mono (by omega))
  have wresult := RationalBits.add_work diffuseTerm.data markedTerm.data height
    (hleft.mono (by omega)) (hright.mono (by omega))
  constructor
  · change HeightBound (RationalBits.add diffuseTerm.data markedTerm.data).data.decode _
    rw [RationalBits.add_value]
    exact (hleft.add hright).mono (by omega)
  · change rate.work + diffuse.work + marked.work + negativeRate.work + remaining.work + diffuseTerm.work +
      markedTerm.work + (RationalBits.add diffuseTerm.data markedTerm.data).work + 8 ≤ _
    simp only [currentWorkPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, primitiveWorkPolynomial_eval]
    change _ ≤ (BinaryActivationProgram.currentWorkPolynomial precision).eval security +
      (BinaryDiffuseCurrent.currentWorkPolynomial precision inputBits).eval security +
      (BinaryMarkedCurrent.currentWorkPolynomial precision inputBits).eval security + 5*primitiveWorkBound height + 8
    omega

end
end CurrentAFT.BinaryPairProgram
