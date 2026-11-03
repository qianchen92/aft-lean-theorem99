import CurrentAFT.BinaryCoefficientInput
import CurrentAFT.BinaryFamilyArithmetic

/-! # Concrete palette programs as guarded natural coefficient programs -/
namespace CurrentAFT.BinaryFiniteCoefficient
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open BinaryFamilyProduct
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

abbrev FiniteProgram (security order : ℕ) := (arity : TruncatedArity order) →
  Vector (Fin (BinaryFirstInverseProgram.colors security)) arity.val.1.val →
    Vector (Fin (BinaryFirstInverseProgram.colors security)) arity.val.2.val → RationalResult

def lift (security order : ℕ) (kernel : FiniteProgram security order) : CoefficientProgram order :=
  fun arity inputs centers =>
    let result := BinaryCoefficientInput.current security arity.val.1.val arity.val.2.val inputs centers (kernel arity)
    ⟨result.data,result.work+1⟩

theorem lift_value (security order : ℕ) (kernel : FiniteProgram security order)
    (table : RationalFamilyProductProgram.Table ℚ ℕ ℕ order)
    (hkernel : ∀ arity inputs centers, (kernel arity inputs centers).data.decode=
      table arity (fun index => (inputs.get index).val) (fun index => (centers.get index).val))
    (arity : TruncatedArity order) (inputs : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hi : ∀ index, inputs.get index<BinaryFirstInverseProgram.colors security)
    (hb : ∀ index, centers.get index<BinaryFirstInverseProgram.colors security) :
    (lift security order kernel arity inputs centers).value.decode=table arity inputs.get centers.get := by
  change (BinaryCoefficientInput.current _ _ _ _ _ _).data.decode=_
  rw [BinaryCoefficientInput.current_value _ _ _ _ _ _ hi hb,hkernel]
  simp only [Vector.get_ofFn]

noncomputable section
noncomputable def workPolynomial (order : ℕ) (kernelWork : Polynomial ℕ) : Polynomial ℕ :=
  BinaryCoefficientInput.workPolynomial order kernelWork+1

theorem lift_bounds (security order : ℕ) (kernelBits kernelWork : Polynomial ℕ) (kernel : FiniteProgram security order)
    (hh : ∀ arity inputs centers, HeightBound (kernel arity inputs centers).data.decode (kernelBits.eval security))
    (hw : ∀ arity inputs centers, (kernel arity inputs centers).work ≤ kernelWork.eval security)
    (arity : TruncatedArity order) (inputs : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hi : ∀ index, inputs.get index<BinaryFirstInverseProgram.colors security)
    (hb : ∀ index, centers.get index<BinaryFirstInverseProgram.colors security) :
    HeightBound (lift security order kernel arity inputs centers).value.decode (kernelBits.eval security) ∧
      (lift security order kernel arity inputs centers).work ≤ (workPolynomial order kernelWork).eval security := by
  have h := BinaryCoefficientInput.current_bounds security order kernelBits kernelWork arity inputs centers (kernel arity) hi hb (hh arity) (hw arity)
  exact ⟨h.1,by simpa only [lift,workPolynomial,Polynomial.eval_add,Polynomial.eval_one] using Nat.add_le_add_right h.2 1⟩

end
end CurrentAFT.BinaryFiniteCoefficient
