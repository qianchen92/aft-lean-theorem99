import CurrentAFT.BinaryMarkedSeed
import CurrentAFT.BinaryCoefficientFiber
import CurrentAFT.RationalMarkedCertificateProgram

/-! # The original marked mixed coefficient fiber as a complete binary program -/
namespace CurrentAFT.BinaryMarkedMixedFamily
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryMarkedSeed.current BinaryCoefficientFiber.current PublicParameterProgram.modulus

def kernel (security bits : ℕ) (scalar : IntegerBits)
    (inputs centers : Vector (Fin (BinaryFirstInverseProgram.colors security)) 1) : RationalResult :=
  let primary := readVector (BinaryFirstFamily.first security) inputs 0
  let center := readVector (BinaryFirstFamily.first security) centers 0
  let result := BinaryMarkedSeed.current security bits scalar primary.value center.value
  ⟨result.data,primary.work+center.work+result.work+3⟩

theorem kernel_value (security bits : ℕ) (scalar : IntegerBits)
    (inputs centers : Vector (Fin (BinaryFirstInverseProgram.colors security)) 1) :
    (kernel security bits scalar inputs centers).data.decode=
      RationalMarkedSeedProgram.inverseDensity security bits scalar.decode (inputs.get 0).val (centers.get 0).val := by
  simp only [kernel,readVector_value,BinaryMarkedSeed.current_value]

def current (security bits order : ℕ) (scalar : IntegerBits) (arity : TruncatedArity order)
    (inputs : Vector (Fin (BinaryFirstInverseProgram.colors security)) arity.val.1.val)
    (centers : Vector (Fin (BinaryFirstInverseProgram.colors security)) arity.val.2.val) : RationalResult :=
  BinaryCoefficientFiber.current security arity.val.1.val arity.val.2.val 1 1 inputs centers (kernel security bits scalar)

theorem current_value (security bits order : ℕ) (scalar : IntegerBits) (arity : TruncatedArity order)
    (inputs : Vector (Fin (BinaryFirstInverseProgram.colors security)) arity.val.1.val)
    (centers : Vector (Fin (BinaryFirstInverseProgram.colors security)) arity.val.2.val) :
    (current security bits order scalar arity inputs centers).data.decode=
      RationalMarkedCertificateProgram.current security bits order scalar.decode arity
        (fun index => (inputs.get index).val) (fun index => (centers.get index).val) := by
  rw [current,BinaryCoefficientFiber.current_value]
  unfold RationalMarkedCertificateProgram.current
  split_ifs
  · rw [kernel_value]
    simp only [Vector.get_cast]
    rfl
  · rfl

noncomputable section
noncomputable def heightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ := BinaryMarkedSeed.heightPolynomial precision
noncomputable def workPolynomial (order : ℕ) (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryMarkedSeed.workPolynomial precision scalarBits+Polynomial.C (6*order+61)

theorem kernel_bounds (security : ℕ) (precision scalarBits : Polynomial ℕ) (scalar : IntegerBits)
    (hs : scalar.digits.length ≤ scalarBits.eval security)
    (inputs centers : Vector (Fin (BinaryFirstInverseProgram.colors security)) 1) :
    HeightBound (kernel security (precision.eval security) scalar inputs centers).data.decode
      ((heightPolynomial precision).eval security) ∧
      (kernel security (precision.eval security) scalar inputs centers).work≤
        (BinaryMarkedSeed.workPolynomial precision scalarBits).eval security+15 := by
  have h := BinaryMarkedSeed.current_bounds security precision scalarBits scalar hs
    (readVector (BinaryFirstFamily.first security) inputs 0).value (readVector (BinaryFirstFamily.first security) centers 0).value
  constructor
  · exact h.1
  · have wp := readVector_work (BinaryFirstFamily.first security) inputs 0
    have wb := readVector_work (BinaryFirstFamily.first security) centers 0
    change _+_+_+3≤_
    omega

theorem current_bounds (security order : ℕ) (precision scalarBits : Polynomial ℕ) (scalar : IntegerBits)
    (hs : scalar.digits.length ≤ scalarBits.eval security) (arity : TruncatedArity order)
    (inputs : Vector (Fin (BinaryFirstInverseProgram.colors security)) arity.val.1.val)
    (centers : Vector (Fin (BinaryFirstInverseProgram.colors security)) arity.val.2.val) :
    HeightBound (current security (precision.eval security) order scalar arity inputs centers).data.decode
      ((heightPolynomial precision).eval security) ∧
      (current security (precision.eval security) order scalar arity inputs centers).work≤(workPolynomial order precision scalarBits).eval security := by
  have h := BinaryCoefficientFiber.current_bounds security arity.val.1.val arity.val.2.val 1 1 inputs centers
    (kernel security (precision.eval security) scalar) ((heightPolynomial precision).eval security)
    ((BinaryMarkedSeed.workPolynomial precision scalarBits).eval security+15)
    (fun inputs centers => (kernel_bounds security precision scalarBits scalar hs inputs centers).1)
    (fun inputs centers => (kernel_bounds security precision scalarBits scalar hs inputs centers).2)
  refine ⟨h.1,h.2.trans ?_⟩
  have hd := arity.property
  simp only [workPolynomial,Polynomial.eval_add,Polynomial.eval_C]
  omega

end
end CurrentAFT.BinaryMarkedMixedFamily
