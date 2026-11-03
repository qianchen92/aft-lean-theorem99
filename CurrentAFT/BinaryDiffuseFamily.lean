import CurrentAFT.BinaryDiffuseResidual
import CurrentAFT.BinaryDiffuseBodyDensity
import CurrentAFT.BinaryMassLiftTensor
import CurrentAFT.BinaryCoefficientFiber
import CurrentAFT.RationalDiffuseFamilyProgram

/-! # The complete original diffuse certificate, with both mixed coefficient fibers -/
namespace CurrentAFT.BinaryDiffuseFamily
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryDiffuseResidual.current BinaryDiffuseBodyDensity.current
  BinaryMassLiftTensor.current BinaryCoefficientFiber.current
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def residual (security bits : ℕ) (scalar : IntegerBits) (word : Vector (Fin (colors security)) 2) : RationalResult :=
  let first := readVector (BinaryFirstFamily.first security) word 0
  let second := readVector (BinaryFirstFamily.first security) word 1
  let result := BinaryDiffuseResidual.current security bits scalar first.value second.value
  ⟨result.data,first.work+second.work+result.work+3⟩

theorem residual_value (security bits : ℕ) (scalar : IntegerBits) (word : Vector (Fin (colors security)) 2) :
    (residual security bits scalar word).data.decode=
      RationalDiffuseResidualProgram.residual security bits scalar.decode (word.get 0).val (word.get 1).val := by
  simp only [residual,readVector_value,BinaryDiffuseResidual.current_value]

def primaryKernel (security bits : ℕ) (scalar : IntegerBits)
    (inputs : Vector (Fin (colors security)) 2) (_centers : Vector (Fin (colors security)) 0) : RationalResult :=
  BinaryMassLiftTensor.current security bits 2 inputs (residual security bits scalar)

theorem primaryKernel_value (security bits : ℕ) (scalar : IntegerBits)
    (inputs : Vector (Fin (colors security)) 2) (centers : Vector (Fin (colors security)) 0) :
    (primaryKernel security bits scalar inputs centers).data.decode=
      RationalMassLiftTensorProgram.current security bits 2
        (fun word => RationalDiffuseResidualProgram.residual security bits scalar.decode (word 0) (word 1))
        (fun slot => (inputs.get slot).val) :=
  BinaryMassLiftTensor.current_value security bits 2 inputs (residual security bits scalar) _ (residual_value security bits scalar)

def bodyKernel (security bits : ℕ) (scalar : IntegerBits)
    (_inputs : Vector (Fin (colors security)) 0) (centers : Vector (Fin (colors security)) 2) : RationalResult :=
  let first := readVector (BinaryFirstFamily.first security) centers 0
  let second := readVector (BinaryFirstFamily.first security) centers 1
  let result := BinaryDiffuseBodyDensity.current security bits scalar first.value second.value
  ⟨result.data,first.work+second.work+result.work+3⟩

theorem bodyKernel_value (security bits : ℕ) (scalar : IntegerBits)
    (inputs : Vector (Fin (colors security)) 0) (centers : Vector (Fin (colors security)) 2) :
    (bodyKernel security bits scalar inputs centers).data.decode=
      RationalDiffuseResidualProgram.bodyDensity security bits scalar.decode (centers.get 0).val (centers.get 1).val := by
  simp only [bodyKernel,readVector_value,BinaryDiffuseBodyDensity.current_value]

def body (security bits order : ℕ) (scalar : IntegerBits) (arity : TruncatedArity order)
    (inputs : Vector (Fin (colors security)) arity.val.1.val) (centers : Vector (Fin (colors security)) arity.val.2.val) : RationalResult :=
  BinaryCoefficientFiber.current security arity.val.1.val arity.val.2.val 0 2 inputs centers (bodyKernel security bits scalar)

def primary (security bits order : ℕ) (scalar : IntegerBits) (arity : TruncatedArity order)
    (inputs : Vector (Fin (colors security)) arity.val.1.val) (centers : Vector (Fin (colors security)) arity.val.2.val) : RationalResult :=
  BinaryCoefficientFiber.current security arity.val.1.val arity.val.2.val 2 0 inputs centers (primaryKernel security bits scalar)

theorem body_value (security bits order : ℕ) (scalar : IntegerBits) (arity : TruncatedArity order)
    (inputs : Vector (Fin (colors security)) arity.val.1.val) (centers : Vector (Fin (colors security)) arity.val.2.val) :
    (body security bits order scalar arity inputs centers).data.decode=RationalDiffuseFamilyProgram.body security bits order scalar.decode arity
      (fun index => (inputs.get index).val) (fun index => (centers.get index).val) := by
  rw [body,BinaryCoefficientFiber.current_value]
  unfold RationalDiffuseFamilyProgram.body RationalDiffuseFamilyProgram.bodyTable
  split_ifs
  · rw [bodyKernel_value]
    simp only [Vector.get_cast]
    congr 1
  · rfl

theorem primary_value (security bits order : ℕ) (scalar : IntegerBits) (arity : TruncatedArity order)
    (inputs : Vector (Fin (colors security)) arity.val.1.val) (centers : Vector (Fin (colors security)) arity.val.2.val) :
    (primary security bits order scalar arity inputs centers).data.decode=RationalDiffuseFamilyProgram.primary security bits order scalar.decode arity
      (fun index => (inputs.get index).val) (fun index => (centers.get index).val) := by
  rw [primary,BinaryCoefficientFiber.current_value]
  unfold RationalDiffuseFamilyProgram.primary RationalDiffuseFamilyProgram.primaryTable
  split_ifs with h h'
  · rw [primaryKernel_value]
    congr 1
  · omega
  · omega
  · rfl

def current (security bits order : ℕ) (scalar : IntegerBits) (arity : TruncatedArity order)
    (inputs : Vector (Fin (colors security)) arity.val.1.val) (centers : Vector (Fin (colors security)) arity.val.2.val) : RationalResult :=
  let body := body security bits order scalar arity inputs centers
  let primary := primary security bits order scalar arity inputs centers
  let result := RationalBits.add body.data primary.data
  ⟨result.data,body.work+primary.work+result.work+3⟩

theorem current_value (security bits order : ℕ) (scalar : IntegerBits) (arity : TruncatedArity order)
    (inputs : Vector (Fin (colors security)) arity.val.1.val) (centers : Vector (Fin (colors security)) arity.val.2.val) :
    (current security bits order scalar arity inputs centers).data.decode=RationalDiffuseFamilyProgram.current security bits order scalar.decode arity
      (fun index => (inputs.get index).val) (fun index => (centers.get index).val) := by
  simp only [current,RationalBits.add_value,body_value,primary_value,RationalDiffuseFamilyProgram.current,Pi.add_apply]

noncomputable section
noncomputable def residualWorkPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ := BinaryDiffuseResidual.workPolynomial precision scalarBits+21
noncomputable def primaryHeightPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryMassLiftTensor.heightPolynomial 2 precision (BinaryDiffuseResidual.heightPolynomial precision scalarBits)
noncomputable def primaryWorkPolynomial (order : ℕ) (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryMassLiftTensor.workPolynomial 2 precision (BinaryDiffuseResidual.heightPolynomial precision scalarBits)
    (residualWorkPolynomial precision scalarBits)+Polynomial.C (6*order+46)
noncomputable def bodyWorkPolynomial (order : ℕ) (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryDiffuseBodyDensity.workPolynomial precision scalarBits+Polynomial.C (6*order+67)
noncomputable def operandPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryDiffuseBodyDensity.heightPolynomial precision scalarBits+primaryHeightPolynomial precision scalarBits
noncomputable def heightPolynomial (precision scalarBits : Polynomial ℕ) : Polynomial ℕ := operandPolynomial precision scalarBits+1
noncomputable def workPolynomial (order : ℕ) (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  bodyWorkPolynomial order precision scalarBits+primaryWorkPolynomial order precision scalarBits+
    primitiveWorkPolynomial (operandPolynomial precision scalarBits)+3

theorem residual_bounds (security : ℕ) (precision scalarBits : Polynomial ℕ) (scalar : IntegerBits)
    (hs : scalar.digits.length ≤ scalarBits.eval security) (word : Vector (Fin (colors security)) 2) :
    HeightBound (residual security (precision.eval security) scalar word).data.decode
      ((BinaryDiffuseResidual.heightPolynomial precision scalarBits).eval security) ∧
    (residual security (precision.eval security) scalar word).work ≤ (residualWorkPolynomial precision scalarBits).eval security := by
  have h := BinaryDiffuseResidual.current_bounds security precision scalarBits scalar hs
    (readVector (BinaryFirstFamily.first security) word 0).value (readVector (BinaryFirstFamily.first security) word 1).value
  refine ⟨h.1,?_⟩
  have wf := readVector_work (BinaryFirstFamily.first security) word 0
  have ws := readVector_work (BinaryFirstFamily.first security) word 1
  change _+_+_+3 ≤ _
  simp only [residualWorkPolynomial,Polynomial.eval_add,Polynomial.eval_ofNat]
  omega

theorem primary_bounds (security order : ℕ) (precision scalarBits : Polynomial ℕ) (scalar : IntegerBits)
    (hs : scalar.digits.length ≤ scalarBits.eval security) (arity : TruncatedArity order)
    (inputs : Vector (Fin (colors security)) arity.val.1.val) (centers : Vector (Fin (colors security)) arity.val.2.val) :
    HeightBound (primary security (precision.eval security) order scalar arity inputs centers).data.decode
      ((primaryHeightPolynomial precision scalarBits).eval security) ∧
    (primary security (precision.eval security) order scalar arity inputs centers).work ≤ (primaryWorkPolynomial order precision scalarBits).eval security := by
  have hk (inputs : Vector (Fin (colors security)) 2) (_centers : Vector (Fin (colors security)) 0) :=
    BinaryMassLiftTensor.current_bounds security 2 precision (BinaryDiffuseResidual.heightPolynomial precision scalarBits)
      (residualWorkPolynomial precision scalarBits) inputs (residual security (precision.eval security) scalar)
      (fun source => (residual_bounds security precision scalarBits scalar hs source).1)
      (fun source => (residual_bounds security precision scalarBits scalar hs source).2)
  have h := BinaryCoefficientFiber.current_bounds security arity.val.1.val arity.val.2.val 2 0 inputs centers
    (primaryKernel security (precision.eval security) scalar) ((primaryHeightPolynomial precision scalarBits).eval security)
    ((BinaryMassLiftTensor.workPolynomial 2 precision (BinaryDiffuseResidual.heightPolynomial precision scalarBits) (residualWorkPolynomial precision scalarBits)).eval security)
    (fun inputs centers => (hk inputs centers).1) (fun inputs centers => (hk inputs centers).2)
  refine ⟨h.1,h.2.trans ?_⟩
  have hd := arity.property
  simp only [primaryWorkPolynomial,Polynomial.eval_add,Polynomial.eval_C]
  omega

theorem bodyKernel_bounds (security : ℕ) (precision scalarBits : Polynomial ℕ) (scalar : IntegerBits)
    (hs : scalar.digits.length ≤ scalarBits.eval security) (inputs : Vector (Fin (colors security)) 0) (centers : Vector (Fin (colors security)) 2) :
    HeightBound (bodyKernel security (precision.eval security) scalar inputs centers).data.decode
      ((BinaryDiffuseBodyDensity.heightPolynomial precision scalarBits).eval security) ∧
    (bodyKernel security (precision.eval security) scalar inputs centers).work ≤ (BinaryDiffuseBodyDensity.workPolynomial precision scalarBits).eval security+21 := by
  have h := BinaryDiffuseBodyDensity.current_bounds security precision scalarBits scalar hs
    (readVector (BinaryFirstFamily.first security) centers 0).value (readVector (BinaryFirstFamily.first security) centers 1).value
  refine ⟨h.1,?_⟩
  have wf := readVector_work (BinaryFirstFamily.first security) centers 0
  have ws := readVector_work (BinaryFirstFamily.first security) centers 1
  change _+_+_+3 ≤ _
  omega

theorem body_bounds (security order : ℕ) (precision scalarBits : Polynomial ℕ) (scalar : IntegerBits)
    (hs : scalar.digits.length ≤ scalarBits.eval security) (arity : TruncatedArity order)
    (inputs : Vector (Fin (colors security)) arity.val.1.val) (centers : Vector (Fin (colors security)) arity.val.2.val) :
    HeightBound (body security (precision.eval security) order scalar arity inputs centers).data.decode
      ((BinaryDiffuseBodyDensity.heightPolynomial precision scalarBits).eval security) ∧
    (body security (precision.eval security) order scalar arity inputs centers).work ≤ (bodyWorkPolynomial order precision scalarBits).eval security := by
  have h := BinaryCoefficientFiber.current_bounds security arity.val.1.val arity.val.2.val 0 2 inputs centers
    (bodyKernel security (precision.eval security) scalar) ((BinaryDiffuseBodyDensity.heightPolynomial precision scalarBits).eval security)
    ((BinaryDiffuseBodyDensity.workPolynomial precision scalarBits).eval security+21)
    (fun inputs centers => (bodyKernel_bounds security precision scalarBits scalar hs inputs centers).1)
    (fun inputs centers => (bodyKernel_bounds security precision scalarBits scalar hs inputs centers).2)
  refine ⟨h.1,h.2.trans ?_⟩
  have hd := arity.property
  simp only [bodyWorkPolynomial,Polynomial.eval_add,Polynomial.eval_C]
  omega

theorem current_bounds (security order : ℕ) (precision scalarBits : Polynomial ℕ) (scalar : IntegerBits)
    (hs : scalar.digits.length ≤ scalarBits.eval security) (arity : TruncatedArity order)
    (inputs : Vector (Fin (colors security)) arity.val.1.val) (centers : Vector (Fin (colors security)) arity.val.2.val) :
    HeightBound (current security (precision.eval security) order scalar arity inputs centers).data.decode
      ((heightPolynomial precision scalarBits).eval security) ∧
    (current security (precision.eval security) order scalar arity inputs centers).work ≤ (workPolynomial order precision scalarBits).eval security := by
  let b := body security (precision.eval security) order scalar arity inputs centers
  let p := primary security (precision.eval security) order scalar arity inputs centers
  let H := (operandPolynomial precision scalarBits).eval security
  have hH : H=(BinaryDiffuseBodyDensity.heightPolynomial precision scalarBits).eval security+
      (primaryHeightPolynomial precision scalarBits).eval security := by simp only [H,operandPolynomial,Polynomial.eval_add]
  have hb := body_bounds security order precision scalarBits scalar hs arity inputs centers
  have hp := primary_bounds security order precision scalarBits scalar hs arity inputs centers
  have wa := RationalBits.add_work b.data p.data H (hb.1.mono (by rw [hH]; omega)) (hp.1.mono (by rw [hH]; omega))
  constructor
  · change HeightBound (RationalBits.add b.data p.data).data.decode _
    rw [RationalBits.add_value]
    simpa only [heightPolynomial,operandPolynomial,Polynomial.eval_add,Polynomial.eval_one] using hb.1.add hp.1
  · change b.work+p.work+(RationalBits.add b.data p.data).work+3 ≤ _
    simp only [workPolynomial,Polynomial.eval_add,Polynomial.eval_ofNat,primitiveWorkPolynomial_eval]
    change _ ≤ (bodyWorkPolynomial order precision scalarBits).eval security+(primaryWorkPolynomial order precision scalarBits).eval security+primitiveWorkBound H+3
    dsimp only [b,p] at wa ⊢
    omega

end
end CurrentAFT.BinaryDiffuseFamily
