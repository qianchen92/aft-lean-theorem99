import CurrentAFT.BinaryMarkedPairProgram
import CurrentAFT.BinaryMixture
import CurrentAFT.RationalPairQuadraticProgram

/-! # The literal activation mixture of complete actual quadratic data -/
namespace CurrentAFT.BinaryPairQuadraticProgram
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open BinaryFamilyProduct FixedFamilyPrograms
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def current (security bits order : ℕ) (programs : List (Entry order)) (scalar : IntegerBits) : CoefficientProgram order :=
  fun arity inputs centers =>
    let rate := BinaryActivationProgram.current security bits
    let diffuse := BinaryBackgroundLeaves.current .diffuse security bits order scalar arity inputs centers
    let marked := BinaryMarkedPairProgram.current security bits order programs scalar arity inputs centers
    let result := BinaryMixture.current rate.data diffuse.value marked.value
    ⟨result.data,rate.work+diffuse.work+marked.work+result.work+4⟩

noncomputable section
theorem current_value (security bits order : ℕ) (programs : List (Entry order))
    (hcorrect : Correct order programs) (hcomplete : Complete order programs) (scalar : IntegerBits)
    (arity : TruncatedArity order) (inputs : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hi : ∀ index, inputs.get index<BinaryFirstInverseProgram.colors security)
    (hb : ∀ index, centers.get index<BinaryFirstInverseProgram.colors security) :
    (current security bits order programs scalar arity inputs centers).value.decode=
      RationalPairQuadraticProgram.current security bits order scalar.decode arity inputs.get centers.get := by
  simp only [current,BinaryMixture.current_value,BinaryActivationProgram.current_value,
    BinaryBackgroundLeaves.current_value .diffuse security bits order scalar arity inputs centers hi hb,
    BinaryMarkedPairProgram.current_value security bits order programs hcorrect hcomplete scalar arity inputs centers hi hb,
    BinaryBackgroundLeaves.ideal,RationalPairQuadraticProgram.current]

noncomputable def operandPolynomial (order : ℕ) (programs : List (Entry order)) (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryActivationProgram.currentHeightPolynomial precision+BinaryBackgroundLeaves.heightPolynomial .diffuse precision scalarBits+
    BinaryMarkedPairProgram.heightPolynomial order programs precision scalarBits
noncomputable def heightPolynomial (order : ℕ) (programs : List (Entry order)) (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryMixture.heightPolynomial (operandPolynomial order programs precision scalarBits)
noncomputable def workPolynomial (order : ℕ) (programs : List (Entry order)) (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryActivationProgram.currentWorkPolynomial precision+BinaryBackgroundLeaves.workPolynomial .diffuse order precision scalarBits+
    BinaryMarkedPairProgram.workPolynomial order programs precision scalarBits+
    BinaryMixture.workPolynomial (operandPolynomial order programs precision scalarBits)+4

theorem current_bounds (security order : ℕ) (programs : List (Entry order)) (precision scalarBits : Polynomial ℕ)
    (scalar : IntegerBits) (hs : scalar.digits.length ≤ scalarBits.eval security)
    (arity : TruncatedArity order) (inputs : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hi : ∀ index, inputs.get index<BinaryFirstInverseProgram.colors security)
    (hb : ∀ index, centers.get index<BinaryFirstInverseProgram.colors security) :
    HeightBound (current security (precision.eval security) order programs scalar arity inputs centers).value.decode
      ((heightPolynomial order programs precision scalarBits).eval security) ∧
    (current security (precision.eval security) order programs scalar arity inputs centers).work ≤
      (workPolynomial order programs precision scalarBits).eval security := by
  let rate := BinaryActivationProgram.current security (precision.eval security)
  let diffuse := BinaryBackgroundLeaves.current .diffuse security (precision.eval security) order scalar arity inputs centers
  let marked := BinaryMarkedPairProgram.current security (precision.eval security) order programs scalar arity inputs centers
  let H := (operandPolynomial order programs precision scalarBits).eval security
  have hH : H=(BinaryActivationProgram.currentHeightPolynomial precision).eval security+
      (BinaryBackgroundLeaves.heightPolynomial .diffuse precision scalarBits).eval security+
      (BinaryMarkedPairProgram.heightPolynomial order programs precision scalarBits).eval security := by
    simp only [H,operandPolynomial,Polynomial.eval_add]
  have hr := BinaryActivationProgram.current_bounds security (precision.eval security)
  have hd := BinaryBackgroundLeaves.current_bounds .diffuse security order precision scalarBits scalar hs arity inputs centers hi hb
  have hm := BinaryMarkedPairProgram.current_bounds security order programs precision scalarBits scalar hs arity inputs centers hi hb
  have hrate : HeightBound rate.data.decode H := hr.1.mono (by rw [hH,BinaryActivationProgram.currentHeightPolynomial_eval]; omega)
  have h := BinaryMixture.current_bounds rate.data diffuse.value marked.value H hrate
    (hd.1.mono (by rw [hH]; omega)) (hm.1.mono (by rw [hH]; omega))
  constructor
  · rw [heightPolynomial,BinaryMixture.heightPolynomial_eval]
    exact h.1
  · change rate.work+diffuse.work+marked.work+(BinaryMixture.current rate.data diffuse.value marked.value).work+4 ≤ _
    simp only [workPolynomial,Polynomial.eval_add,Polynomial.eval_ofNat,BinaryMixture.workPolynomial_eval]
    have wr := BinaryActivationProgram.current_polynomial_work precision security
    dsimp only [rate,diffuse,marked,H] at h ⊢
    omega

end
end CurrentAFT.BinaryPairQuadraticProgram
