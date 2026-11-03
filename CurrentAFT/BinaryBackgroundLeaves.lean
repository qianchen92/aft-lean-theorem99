import CurrentAFT.BinaryFiniteCoefficient
import CurrentAFT.BinaryBackgroundFamilies
import CurrentAFT.BinaryPrimaryDeviation
import CurrentAFT.BinaryMarkedMixedFamily
import CurrentAFT.BinaryDiffuseFamily

/-! # The actual background coefficient leaves in the common finite program format -/
namespace CurrentAFT.BinaryBackgroundLeaves
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open BinaryFamilyProduct
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

inductive Role where
  | free | translation | primaryDeviation | markedMixed | diffuse
  deriving DecidableEq

def finite (role : Role) (security bits order : ℕ) (scalar : IntegerBits) : BinaryFiniteCoefficient.FiniteProgram security order :=
  match role with
  | .free => BinaryBackgroundFamilies.free security bits order
  | .translation => BinaryBackgroundFamilies.translation security bits order scalar
  | .primaryDeviation => BinaryPrimaryDeviation.current security bits order
  | .markedMixed => BinaryMarkedMixedFamily.current security bits order scalar
  | .diffuse => BinaryDiffuseFamily.current security bits order scalar

def ideal (role : Role) (security bits order : ℕ) (scalar : ℤ) : RationalFamilyProductProgram.Table ℚ ℕ ℕ order :=
  match role with
  | .free => RationalBackgroundProgram.free security bits order
  | .translation => RationalBackgroundProgram.translation security bits order scalar
  | .primaryDeviation => RationalPrimaryDeviationProgram.current security bits order
  | .markedMixed => RationalMarkedCertificateProgram.current security bits order scalar
  | .diffuse => RationalDiffuseFamilyProgram.current security bits order scalar

def current (role : Role) (security bits order : ℕ) (scalar : IntegerBits) : CoefficientProgram order :=
  BinaryFiniteCoefficient.lift security order (finite role security bits order scalar)

theorem finite_value (role : Role) (security bits order : ℕ) (scalar : IntegerBits)
    (arity : TruncatedArity order)
    (inputs : Vector (Fin (BinaryFirstInverseProgram.colors security)) arity.val.1.val)
    (centers : Vector (Fin (BinaryFirstInverseProgram.colors security)) arity.val.2.val) :
    (finite role security bits order scalar arity inputs centers).data.decode=
      ideal role security bits order scalar.decode arity (fun index => (inputs.get index).val) (fun index => (centers.get index).val) := by
  cases role
  · exact BinaryBackgroundFamilies.free_value security bits order arity inputs centers
  · exact BinaryBackgroundFamilies.translation_value security bits order scalar arity inputs centers
  · exact BinaryPrimaryDeviation.current_value security bits order arity inputs centers
  · exact BinaryMarkedMixedFamily.current_value security bits order scalar arity inputs centers
  · exact BinaryDiffuseFamily.current_value security bits order scalar arity inputs centers

theorem current_value (role : Role) (security bits order : ℕ) (scalar : IntegerBits)
    (arity : TruncatedArity order) (inputs : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hi : ∀ index, inputs.get index<BinaryFirstInverseProgram.colors security)
    (hb : ∀ index, centers.get index<BinaryFirstInverseProgram.colors security) :
    (current role security bits order scalar arity inputs centers).value.decode=
      ideal role security bits order scalar.decode arity inputs.get centers.get :=
  BinaryFiniteCoefficient.lift_value security order (finite role security bits order scalar)
    (ideal role security bits order scalar.decode) (finite_value role security bits order scalar) arity inputs centers hi hb

noncomputable section
noncomputable def heightPolynomial (role : Role) (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  match role with
  | .free => BinaryBackgroundFamilies.freeHeightPolynomial precision
  | .translation => BinaryBackgroundFamilies.translationHeightPolynomial precision scalarBits
  | .primaryDeviation => BinaryPrimaryDeviation.heightPolynomial precision
  | .markedMixed => BinaryMarkedMixedFamily.heightPolynomial precision
  | .diffuse => BinaryDiffuseFamily.heightPolynomial precision scalarBits
noncomputable def finiteWorkPolynomial (role : Role) (order : ℕ) (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  match role with
  | .free => BinaryBackgroundFamilies.freeWorkPolynomial order precision
  | .translation => BinaryBackgroundFamilies.translationWorkPolynomial order precision scalarBits
  | .primaryDeviation => BinaryPrimaryDeviation.workPolynomial order precision
  | .markedMixed => BinaryMarkedMixedFamily.workPolynomial order precision scalarBits
  | .diffuse => BinaryDiffuseFamily.workPolynomial order precision scalarBits
noncomputable def workPolynomial (role : Role) (order : ℕ) (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFiniteCoefficient.workPolynomial order (finiteWorkPolynomial role order precision scalarBits)

theorem finite_bounds (role : Role) (security order : ℕ) (precision scalarBits : Polynomial ℕ) (scalar : IntegerBits)
    (hs : scalar.digits.length ≤ scalarBits.eval security) (arity : TruncatedArity order)
    (inputs : Vector (Fin (BinaryFirstInverseProgram.colors security)) arity.val.1.val)
    (centers : Vector (Fin (BinaryFirstInverseProgram.colors security)) arity.val.2.val) :
    HeightBound (finite role security (precision.eval security) order scalar arity inputs centers).data.decode
      ((heightPolynomial role precision scalarBits).eval security) ∧
    (finite role security (precision.eval security) order scalar arity inputs centers).work ≤
      (finiteWorkPolynomial role order precision scalarBits).eval security := by
  cases role
  · exact BinaryBackgroundFamilies.free_bounds security order precision arity inputs centers
  · exact BinaryBackgroundFamilies.translation_bounds security order precision scalarBits scalar hs arity inputs centers
  · exact BinaryPrimaryDeviation.current_bounds security order precision arity inputs centers
  · exact BinaryMarkedMixedFamily.current_bounds security order precision scalarBits scalar hs arity inputs centers
  · exact BinaryDiffuseFamily.current_bounds security order precision scalarBits scalar hs arity inputs centers

theorem current_bounds (role : Role) (security order : ℕ) (precision scalarBits : Polynomial ℕ) (scalar : IntegerBits)
    (hs : scalar.digits.length ≤ scalarBits.eval security) (arity : TruncatedArity order)
    (inputs : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hi : ∀ index, inputs.get index<BinaryFirstInverseProgram.colors security)
    (hb : ∀ index, centers.get index<BinaryFirstInverseProgram.colors security) :
    HeightBound (current role security (precision.eval security) order scalar arity inputs centers).value.decode
      ((heightPolynomial role precision scalarBits).eval security) ∧
    (current role security (precision.eval security) order scalar arity inputs centers).work ≤
      (workPolynomial role order precision scalarBits).eval security :=
  BinaryFiniteCoefficient.lift_bounds security order (heightPolynomial role precision scalarBits)
    (finiteWorkPolynomial role order precision scalarBits) (finite role security (precision.eval security) order scalar)
    (fun arity inputs centers => (finite_bounds role security order precision scalarBits scalar hs arity inputs centers).1)
    (fun arity inputs centers => (finite_bounds role security order precision scalarBits scalar hs arity inputs centers).2)
    arity inputs centers hi hb

end
end CurrentAFT.BinaryBackgroundLeaves
