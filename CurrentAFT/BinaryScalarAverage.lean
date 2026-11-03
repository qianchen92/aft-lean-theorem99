import CurrentAFT.BinaryCoefficientScalarAverage

/-! # The same executed scalar average for a scalar-valued finite mass -/
namespace CurrentAFT.BinaryScalarAverage
open AFT GaussianSource RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
  RationalRejectionProgram BinaryFamilyProduct GradedControlAlgebra
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def table (kernel : IntegerBits → RationalResult) (scalar : IntegerBits) : CoefficientProgram 0 :=
  fun _ _ _ => ⟨(kernel scalar).data,(kernel scalar).work⟩

def current (security bits : ℕ) (kernel : IntegerBits → RationalResult) : RationalResult :=
  let result := BinaryCoefficientScalarAverage.current security bits 0 (table kernel)
    (zeroArity 0) #v[] #v[]
  ⟨result.value,result.work⟩

theorem current_value (security bits : ℕ) (kernel : IntegerBits → RationalResult) (ideal : ℤ → ℚ)
    (hvalue : ∀ scalar, (kernel scalar).data.decode=ideal scalar.decode) :
    (current security bits kernel).data.decode=
      ∑ scalar : Window (RationalBackgroundLinearProgram.cutoff security),
        RationalProposalProgram.gaussianWeight security (RationalBackgroundLinearProgram.cutoff security) bits scalar*ideal scalar.val := by
  change (BinaryCoefficientScalarAverage.current _ _ _ _ _ _ _).value.decode = _
  rw [BinaryCoefficientScalarAverage.current_value security bits 0 (table kernel)
    (fun scalar _ _ _ => ideal scalar) (fun scalar _ _ _ => hvalue scalar)]
  rfl

noncomputable section
open scoped BigOperators

theorem current_bounds (security : ℕ) (precision leafBits leafWork : Polynomial ℕ) (kernel : IntegerBits → RationalResult)
    (hkernel : ∀ scalar, scalar.digits.length ≤ BinaryCoefficientScalarAverage.scalarBitsPolynomial.eval security →
      HeightBound (kernel scalar).data.decode (leafBits.eval security) ∧ (kernel scalar).work ≤ leafWork.eval security) :
    HeightBound (current security (precision.eval security) kernel).data.decode
      ((BinaryCoefficientScalarAverage.heightPolynomial precision leafBits).eval security) ∧
      (current security (precision.eval security) kernel).work ≤
        (BinaryCoefficientScalarAverage.workPolynomial precision leafBits leafWork).eval security :=
  BinaryCoefficientScalarAverage.current_bounds security 0 1 precision leafBits leafWork (table kernel)
    (fun scalar hs _ _ _ _ _ => hkernel scalar hs) (zeroArity 0) #v[] #v[]
    (fun index => Fin.elim0 index) (fun index => Fin.elim0 index)

end
end CurrentAFT.BinaryScalarAverage
