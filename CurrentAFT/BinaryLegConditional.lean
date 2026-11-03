import CurrentAFT.BinaryPairQuadraticProgram
import CurrentAFT.BinaryConditionalPairProgram
import CurrentAFT.BinaryCoefficientOperations
import CurrentAFT.RationalLegBackgroundProgram

/-! # Same-scalar quadratic and cubic leg data before the Gaussian average -/
namespace CurrentAFT.BinaryLegConditional
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open BinaryFamilyProduct FixedFamilyPrograms
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

inductive Role where | quadratic | cubic deriving DecidableEq

def left (role : Role) (security bits order : ℕ) (programs : List (Entry order)) (scalar : IntegerBits) : CoefficientProgram order :=
  match role with
  | .quadratic => BinaryConditionalPairProgram.current security bits order scalar
  | .cubic => BinaryPairQuadraticProgram.current security bits order programs scalar

def leftIdeal (role : Role) (security bits order : ℕ) (scalar : ℤ) : RationalFamilyProductProgram.Table ℚ ℕ ℕ order :=
  match role with
  | .quadratic => RationalConditionalPairProgram.current security bits order scalar
  | .cubic => RationalPairQuadraticProgram.current security bits order scalar

def product (role : Role) (security bits order : ℕ) (programs : List (Entry order)) (scalar : IntegerBits) : CoefficientProgram order :=
  BinaryFamilyArithmetic.multiply order programs (left role security bits order programs scalar)
    (BinaryBackgroundLeaves.current .translation security bits order scalar)

def current (role : Role) (security bits order : ℕ) (programs : List (Entry order)) (scalar : IntegerBits) : CoefficientProgram order :=
  match role with
  | .quadratic => BinaryCoefficientOperations.add order (BinaryPairQuadraticProgram.current security bits order programs scalar)
      (product .quadratic security bits order programs scalar)
  | .cubic => product .cubic security bits order programs scalar

def ideal (role : Role) (security bits order : ℕ) (scalar : ℤ) : RationalFamilyProductProgram.Table ℚ ℕ ℕ order :=
  match role with
  | .quadratic => RationalLegBackgroundProgram.conditionalQuadratic security bits order scalar
  | .cubic => RationalLegBackgroundProgram.conditionalCubic security bits order scalar

noncomputable section
theorem left_value (role : Role) (security bits order : ℕ) (programs : List (Entry order))
    (hcorrect : Correct order programs) (hcomplete : Complete order programs) (scalar : IntegerBits)
    (arity : TruncatedArity order) (inputs : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hi : ∀ i, inputs.get i<BinaryFirstInverseProgram.colors security) (hb : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    (left role security bits order programs scalar arity inputs centers).value.decode=
      leftIdeal role security bits order scalar.decode arity inputs.get centers.get := by
  cases role
  · exact BinaryConditionalPairProgram.current_value security bits order scalar arity inputs centers hi hb
  · exact BinaryPairQuadraticProgram.current_value security bits order programs hcorrect hcomplete scalar arity inputs centers hi hb

theorem product_value (role : Role) (security bits order : ℕ) (programs : List (Entry order))
    (hcorrect : Correct order programs) (hcomplete : Complete order programs) (scalar : IntegerBits)
    (arity : TruncatedArity order) (inputs : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hi : ∀ i, inputs.get i<BinaryFirstInverseProgram.colors security) (hb : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    (product role security bits order programs scalar arity inputs centers).value.decode=
      RationalFamilyProductProgram.product order (leftIdeal role security bits order scalar.decode)
        (RationalBackgroundProgram.translation security bits order scalar.decode) arity inputs.get centers.get :=
  BinaryFamilyValidSemantics.multiply_value order (BinaryFirstInverseProgram.colors security) programs hcorrect hcomplete _ _ _ _
    (left_value role security bits order programs hcorrect hcomplete scalar)
    (BinaryBackgroundLeaves.current_value .translation security bits order scalar) arity inputs centers hi hb

theorem current_value (role : Role) (security bits order : ℕ) (programs : List (Entry order))
    (hcorrect : Correct order programs) (hcomplete : Complete order programs) (scalar : IntegerBits)
    (arity : TruncatedArity order) (inputs : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hi : ∀ i, inputs.get i<BinaryFirstInverseProgram.colors security) (hb : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    (current role security bits order programs scalar arity inputs centers).value.decode=ideal role security bits order scalar.decode arity inputs.get centers.get := by
  cases role
  · simp only [current,BinaryCoefficientOperations.add_value,
      BinaryPairQuadraticProgram.current_value security bits order programs hcorrect hcomplete scalar arity inputs centers hi hb,
      product_value .quadratic security bits order programs hcorrect hcomplete scalar arity inputs centers hi hb,
      leftIdeal,ideal,RationalLegBackgroundProgram.conditionalQuadratic]
  · exact product_value .cubic security bits order programs hcorrect hcomplete scalar arity inputs centers hi hb

noncomputable def leftHeightPolynomial (role : Role) (order : ℕ) (programs : List (Entry order)) (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  match role with
  | .quadratic => BinaryConditionalPairProgram.heightPolynomial precision scalarBits
  | .cubic => BinaryPairQuadraticProgram.heightPolynomial order programs precision scalarBits
noncomputable def leftWorkPolynomial (role : Role) (order : ℕ) (programs : List (Entry order)) (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  match role with
  | .quadratic => BinaryConditionalPairProgram.workPolynomial order precision scalarBits
  | .cubic => BinaryPairQuadraticProgram.workPolynomial order programs precision scalarBits
noncomputable def productHeightPolynomial (role : Role) (order : ℕ) (programs : List (Entry order)) (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyArithmetic.heightPolynomial order programs
    (leftHeightPolynomial role order programs precision scalarBits+BinaryBackgroundLeaves.heightPolynomial .translation precision scalarBits)
noncomputable def productWorkPolynomial (role : Role) (order : ℕ) (programs : List (Entry order)) (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyArithmetic.workPolynomial order programs
    (leftHeightPolynomial role order programs precision scalarBits+BinaryBackgroundLeaves.heightPolynomial .translation precision scalarBits)
    (leftWorkPolynomial role order programs precision scalarBits+BinaryBackgroundLeaves.workPolynomial .translation order precision scalarBits)
noncomputable def heightPolynomial (role : Role) (order : ℕ) (programs : List (Entry order)) (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  match role with
  | .quadratic => BinaryCoefficientOperations.addHeight (BinaryPairQuadraticProgram.heightPolynomial order programs precision scalarBits)
      (productHeightPolynomial .quadratic order programs precision scalarBits)
  | .cubic => productHeightPolynomial .cubic order programs precision scalarBits
noncomputable def workPolynomial (role : Role) (order : ℕ) (programs : List (Entry order)) (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  match role with
  | .quadratic => BinaryCoefficientOperations.addWork (BinaryPairQuadraticProgram.heightPolynomial order programs precision scalarBits)
      (productHeightPolynomial .quadratic order programs precision scalarBits) (BinaryPairQuadraticProgram.workPolynomial order programs precision scalarBits)
      (productWorkPolynomial .quadratic order programs precision scalarBits)
  | .cubic => productWorkPolynomial .cubic order programs precision scalarBits

theorem left_bounds (role : Role) (security order : ℕ) (programs : List (Entry order)) (precision scalarBits : Polynomial ℕ)
    (scalar : IntegerBits) (hs : scalar.digits.length ≤ scalarBits.eval security)
    (arity : TruncatedArity order) (inputs : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hi : ∀ i, inputs.get i<BinaryFirstInverseProgram.colors security) (hb : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    HeightBound (left role security (precision.eval security) order programs scalar arity inputs centers).value.decode
      ((leftHeightPolynomial role order programs precision scalarBits).eval security) ∧
    (left role security (precision.eval security) order programs scalar arity inputs centers).work ≤
      (leftWorkPolynomial role order programs precision scalarBits).eval security := by
  cases role
  · exact BinaryConditionalPairProgram.current_bounds security order precision scalarBits scalar hs arity inputs centers hi hb
  · exact BinaryPairQuadraticProgram.current_bounds security order programs precision scalarBits scalar hs arity inputs centers hi hb

theorem product_bounds (role : Role) (security order : ℕ) (programs : List (Entry order)) (precision scalarBits : Polynomial ℕ)
    (scalar : IntegerBits) (hs : scalar.digits.length ≤ scalarBits.eval security)
    (arity : TruncatedArity order) (inputs : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hi : ∀ i, inputs.get i<BinaryFirstInverseProgram.colors security) (hb : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    HeightBound (product role security (precision.eval security) order programs scalar arity inputs centers).value.decode
      ((productHeightPolynomial role order programs precision scalarBits).eval security) ∧
    (product role security (precision.eval security) order programs scalar arity inputs centers).work ≤
      (productWorkPolynomial role order programs precision scalarBits).eval security :=
  BinaryCoefficientOperations.multiply_bounds order (BinaryFirstInverseProgram.colors security) security programs _ _ _ _ _ _
    (left_bounds role security order programs precision scalarBits scalar hs)
    (BinaryBackgroundLeaves.current_bounds .translation security order precision scalarBits scalar hs) arity inputs centers hi hb

theorem current_bounds (role : Role) (security order : ℕ) (programs : List (Entry order)) (precision scalarBits : Polynomial ℕ)
    (scalar : IntegerBits) (hs : scalar.digits.length ≤ scalarBits.eval security)
    (arity : TruncatedArity order) (inputs : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hi : ∀ i, inputs.get i<BinaryFirstInverseProgram.colors security) (hb : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    HeightBound (current role security (precision.eval security) order programs scalar arity inputs centers).value.decode
      ((heightPolynomial role order programs precision scalarBits).eval security) ∧
    (current role security (precision.eval security) order programs scalar arity inputs centers).work ≤
      (workPolynomial role order programs precision scalarBits).eval security := by
  cases role
  · exact BinaryCoefficientOperations.add_bounds order (BinaryFirstInverseProgram.colors security) security _ _ _ _ _ _
      (BinaryPairQuadraticProgram.current_bounds security order programs precision scalarBits scalar hs)
      (product_bounds .quadratic security order programs precision scalarBits scalar hs) arity inputs centers hi hb
  · exact product_bounds .cubic security order programs precision scalarBits scalar hs arity inputs centers hi hb

end
end CurrentAFT.BinaryLegConditional
