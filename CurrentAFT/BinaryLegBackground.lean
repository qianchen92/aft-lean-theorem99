import CurrentAFT.BinaryLegConditional
import CurrentAFT.BinaryBackgroundLinear

/-! # The complete original leg-background atom as a binary coefficient program -/
namespace CurrentAFT.BinaryLegBackground
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open BinaryFamilyProduct FixedFamilyPrograms
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def average (role : BinaryLegConditional.Role) (security bits order : ℕ) (programs : List (Entry order)) : CoefficientProgram order :=
  BinaryCoefficientScalarAverage.current security bits order (fun scalar => BinaryLegConditional.current role security bits order programs scalar)

def lowerPart (security bits order : ℕ) (programs : List (Entry order)) : CoefficientProgram order :=
  BinaryCoefficientOperations.add order (BinaryBackgroundLinear.current security bits order) (average .quadratic security bits order programs)

def current (security bits order : ℕ) (programs : List (Entry order)) : CoefficientProgram order :=
  BinaryCoefficientOperations.add order (lowerPart security bits order programs) (average .cubic security bits order programs)

noncomputable section
theorem average_value (role : BinaryLegConditional.Role) (security bits order : ℕ) (programs : List (Entry order))
    (hcorrect : Correct order programs) (hcomplete : Complete order programs)
    (arity : TruncatedArity order) (inputs : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hi : ∀ i, inputs.get i<BinaryFirstInverseProgram.colors security) (hb : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    (average role security bits order programs arity inputs centers).value.decode=
      RationalScalarFamilyAverage.current security bits order (BinaryLegConditional.ideal role security bits order) arity inputs.get centers.get :=
  BinaryFamilyValidSemantics.scalarAverage_value security bits order (BinaryFirstInverseProgram.colors security) _ _
    (fun scalar => BinaryLegConditional.current_value role security bits order programs hcorrect hcomplete scalar) arity inputs centers hi hb

theorem current_value (security bits order : ℕ) (programs : List (Entry order))
    (hcorrect : Correct order programs) (hcomplete : Complete order programs)
    (arity : TruncatedArity order) (inputs : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hi : ∀ i, inputs.get i<BinaryFirstInverseProgram.colors security) (hb : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    (current security bits order programs arity inputs centers).value.decode=
      RationalLegBackgroundProgram.current security bits order arity inputs.get centers.get := by
  simp only [current,lowerPart,BinaryCoefficientOperations.add_value,
    BinaryBackgroundLinear.current_value security bits order arity inputs centers hi hb,
    average_value .quadratic security bits order programs hcorrect hcomplete arity inputs centers hi hb,
    average_value .cubic security bits order programs hcorrect hcomplete arity inputs centers hi hb,
    RationalLegBackgroundProgram.current,RationalLegBackgroundProgram.quadratic,RationalLegBackgroundProgram.cubic]
  rfl

noncomputable def scalarBitsPolynomial : Polynomial ℕ := BinaryCoefficientScalarAverage.scalarBitsPolynomial
noncomputable def averageHeightPolynomial (role : BinaryLegConditional.Role) (order : ℕ) (programs : List (Entry order)) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryCoefficientScalarAverage.heightPolynomial precision (BinaryLegConditional.heightPolynomial role order programs precision scalarBitsPolynomial)
noncomputable def averageWorkPolynomial (role : BinaryLegConditional.Role) (order : ℕ) (programs : List (Entry order)) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryCoefficientScalarAverage.workPolynomial precision (BinaryLegConditional.heightPolynomial role order programs precision scalarBitsPolynomial)
    (BinaryLegConditional.workPolynomial role order programs precision scalarBitsPolynomial)
noncomputable def lowerPartHeightPolynomial (order : ℕ) (programs : List (Entry order)) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryCoefficientOperations.addHeight (BinaryBackgroundLinear.heightPolynomial precision) (averageHeightPolynomial .quadratic order programs precision)
noncomputable def lowerPartWorkPolynomial (order : ℕ) (programs : List (Entry order)) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryCoefficientOperations.addWork (BinaryBackgroundLinear.heightPolynomial precision) (averageHeightPolynomial .quadratic order programs precision)
    (BinaryBackgroundLinear.workPolynomial order precision) (averageWorkPolynomial .quadratic order programs precision)
noncomputable def heightPolynomial (order : ℕ) (programs : List (Entry order)) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryCoefficientOperations.addHeight (lowerPartHeightPolynomial order programs precision) (averageHeightPolynomial .cubic order programs precision)
noncomputable def workPolynomial (order : ℕ) (programs : List (Entry order)) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryCoefficientOperations.addWork (lowerPartHeightPolynomial order programs precision) (averageHeightPolynomial .cubic order programs precision)
    (lowerPartWorkPolynomial order programs precision) (averageWorkPolynomial .cubic order programs precision)

theorem average_bounds (role : BinaryLegConditional.Role) (security order : ℕ) (programs : List (Entry order)) (precision : Polynomial ℕ)
    (arity : TruncatedArity order) (inputs : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hi : ∀ i, inputs.get i<BinaryFirstInverseProgram.colors security) (hb : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    HeightBound (average role security (precision.eval security) order programs arity inputs centers).value.decode
      ((averageHeightPolynomial role order programs precision).eval security) ∧
    (average role security (precision.eval security) order programs arity inputs centers).work ≤
      (averageWorkPolynomial role order programs precision).eval security :=
  BinaryCoefficientScalarAverage.current_bounds security order (BinaryFirstInverseProgram.colors security) precision _ _ _
    (fun scalar hs => BinaryLegConditional.current_bounds role security order programs precision scalarBitsPolynomial scalar hs) arity inputs centers hi hb

theorem lowerPart_bounds (security order : ℕ) (programs : List (Entry order)) (precision : Polynomial ℕ)
    (arity : TruncatedArity order) (inputs : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hi : ∀ i, inputs.get i<BinaryFirstInverseProgram.colors security) (hb : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    HeightBound (lowerPart security (precision.eval security) order programs arity inputs centers).value.decode
      ((lowerPartHeightPolynomial order programs precision).eval security) ∧
    (lowerPart security (precision.eval security) order programs arity inputs centers).work ≤
      (lowerPartWorkPolynomial order programs precision).eval security :=
  BinaryCoefficientOperations.add_bounds order (BinaryFirstInverseProgram.colors security) security _ _ _ _ _ _
    (BinaryBackgroundLinear.current_bounds security order precision)
    (average_bounds .quadratic security order programs precision) arity inputs centers hi hb

theorem current_bounds (security order : ℕ) (programs : List (Entry order)) (precision : Polynomial ℕ)
    (arity : TruncatedArity order) (inputs : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hi : ∀ i, inputs.get i<BinaryFirstInverseProgram.colors security) (hb : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    HeightBound (current security (precision.eval security) order programs arity inputs centers).value.decode
      ((heightPolynomial order programs precision).eval security) ∧
    (current security (precision.eval security) order programs arity inputs centers).work ≤
      (workPolynomial order programs precision).eval security :=
  BinaryCoefficientOperations.add_bounds order (BinaryFirstInverseProgram.colors security) security _ _ _ _ _ _
    (lowerPart_bounds security order programs precision)
    (average_bounds .cubic security order programs precision) arity inputs centers hi hb

end
end CurrentAFT.BinaryLegBackground
