import CurrentAFT.BinaryBackgroundLeaves
import CurrentAFT.BinaryFamilyValidSemantics
import CurrentAFT.RationalMarkedPairProgram

/-! # The actual marked quadratic certificate, including its mixed product -/
namespace CurrentAFT.BinaryMarkedPairProgram
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open BinaryFamilyProduct FixedFamilyPrograms
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def product (security bits order : ℕ) (programs : List (Entry order)) (scalar : IntegerBits) : CoefficientProgram order :=
  BinaryFamilyArithmetic.multiply order programs
    (BinaryBackgroundLeaves.current .primaryDeviation security bits order scalar)
    (BinaryBackgroundLeaves.current .free security bits order scalar)

def current (security bits order : ℕ) (programs : List (Entry order)) (scalar : IntegerBits) : CoefficientProgram order :=
  fun arity inputs centers =>
    let mixed := BinaryBackgroundLeaves.current .markedMixed security bits order scalar arity inputs centers
    let product := product security bits order programs scalar arity inputs centers
    let result := RationalBits.add mixed.value product.value
    ⟨result.data,mixed.work+product.work+result.work+3⟩

noncomputable section
theorem product_value (security bits order : ℕ) (programs : List (Entry order))
    (hcorrect : Correct order programs) (hcomplete : Complete order programs) (scalar : IntegerBits)
    (arity : TruncatedArity order) (inputs : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hi : ∀ index, inputs.get index<BinaryFirstInverseProgram.colors security)
    (hb : ∀ index, centers.get index<BinaryFirstInverseProgram.colors security) :
    (product security bits order programs scalar arity inputs centers).value.decode=
      RationalFamilyProductProgram.product order (RationalPrimaryDeviationProgram.current security bits order)
        (RationalBackgroundProgram.free security bits order) arity inputs.get centers.get :=
  BinaryFamilyValidSemantics.multiply_value order (BinaryFirstInverseProgram.colors security) programs hcorrect hcomplete _ _ _ _
    (BinaryBackgroundLeaves.current_value .primaryDeviation security bits order scalar)
    (BinaryBackgroundLeaves.current_value .free security bits order scalar) arity inputs centers hi hb

theorem current_value (security bits order : ℕ) (programs : List (Entry order))
    (hcorrect : Correct order programs) (hcomplete : Complete order programs) (scalar : IntegerBits)
    (arity : TruncatedArity order) (inputs : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hi : ∀ index, inputs.get index<BinaryFirstInverseProgram.colors security)
    (hb : ∀ index, centers.get index<BinaryFirstInverseProgram.colors security) :
    (current security bits order programs scalar arity inputs centers).value.decode=
      RationalMarkedPairProgram.current security bits order scalar.decode arity inputs.get centers.get := by
  simp only [current,RationalBits.add_value,BinaryBackgroundLeaves.current_value .markedMixed security bits order scalar arity inputs centers hi hb,
    product_value security bits order programs hcorrect hcomplete scalar arity inputs centers hi hb,RationalMarkedPairProgram.current,BinaryBackgroundLeaves.ideal]

noncomputable def productOperandHeight (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryBackgroundLeaves.heightPolynomial .primaryDeviation precision scalarBits+BinaryBackgroundLeaves.heightPolynomial .free precision scalarBits
noncomputable def productOperandWork (order : ℕ) (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryBackgroundLeaves.workPolynomial .primaryDeviation order precision scalarBits+BinaryBackgroundLeaves.workPolynomial .free order precision scalarBits
noncomputable def productHeightPolynomial (order : ℕ) (programs : List (Entry order)) (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyArithmetic.heightPolynomial order programs (productOperandHeight precision scalarBits)
noncomputable def productWorkPolynomial (order : ℕ) (programs : List (Entry order)) (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyArithmetic.workPolynomial order programs (productOperandHeight precision scalarBits) (productOperandWork order precision scalarBits)
noncomputable def operandPolynomial (order : ℕ) (programs : List (Entry order)) (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryBackgroundLeaves.heightPolynomial .markedMixed precision scalarBits+productHeightPolynomial order programs precision scalarBits
noncomputable def heightPolynomial (order : ℕ) (programs : List (Entry order)) (precision scalarBits : Polynomial ℕ) : Polynomial ℕ := operandPolynomial order programs precision scalarBits+1
noncomputable def workPolynomial (order : ℕ) (programs : List (Entry order)) (precision scalarBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryBackgroundLeaves.workPolynomial .markedMixed order precision scalarBits+productWorkPolynomial order programs precision scalarBits+
    primitiveWorkPolynomial (operandPolynomial order programs precision scalarBits)+3

theorem product_bounds (security order : ℕ) (programs : List (Entry order)) (precision scalarBits : Polynomial ℕ)
    (scalar : IntegerBits) (hs : scalar.digits.length ≤ scalarBits.eval security)
    (arity : TruncatedArity order) (inputs : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hi : ∀ index, inputs.get index<BinaryFirstInverseProgram.colors security)
    (hb : ∀ index, centers.get index<BinaryFirstInverseProgram.colors security) :
    HeightBound (product security (precision.eval security) order programs scalar arity inputs centers).value.decode
      ((productHeightPolynomial order programs precision scalarBits).eval security) ∧
    (product security (precision.eval security) order programs scalar arity inputs centers).work ≤
      (productWorkPolynomial order programs precision scalarBits).eval security := by
  have hfirst : ∀ arity inputs centers, (∀ i, inputs.get i<BinaryFirstInverseProgram.colors security) →
      (∀ i, centers.get i<BinaryFirstInverseProgram.colors security) →
      HeightBound (BinaryBackgroundLeaves.current .primaryDeviation security (precision.eval security) order scalar arity inputs centers).value.decode
        ((productOperandHeight precision scalarBits).eval security) ∧
      (BinaryBackgroundLeaves.current .primaryDeviation security (precision.eval security) order scalar arity inputs centers).work ≤
        (productOperandWork order precision scalarBits).eval security := by
    intro arity inputs centers hi hb
    have h := BinaryBackgroundLeaves.current_bounds .primaryDeviation security order precision scalarBits scalar hs arity inputs centers hi hb
    exact ⟨h.1.mono (by simp only [productOperandHeight,Polynomial.eval_add]; omega),h.2.trans (by simp only [productOperandWork,Polynomial.eval_add]; omega)⟩
  have hsecond : ∀ arity inputs centers, (∀ i, inputs.get i<BinaryFirstInverseProgram.colors security) →
      (∀ i, centers.get i<BinaryFirstInverseProgram.colors security) →
      HeightBound (BinaryBackgroundLeaves.current .free security (precision.eval security) order scalar arity inputs centers).value.decode
        ((productOperandHeight precision scalarBits).eval security) ∧
      (BinaryBackgroundLeaves.current .free security (precision.eval security) order scalar arity inputs centers).work ≤
        (productOperandWork order precision scalarBits).eval security := by
    intro arity inputs centers hi hb
    have h := BinaryBackgroundLeaves.current_bounds .free security order precision scalarBits scalar hs arity inputs centers hi hb
    exact ⟨h.1.mono (by simp only [productOperandHeight,Polynomial.eval_add]; omega),h.2.trans (by simp only [productOperandWork,Polynomial.eval_add]; omega)⟩
  rw [productHeightPolynomial,BinaryFamilyArithmetic.heightPolynomial_eval,productWorkPolynomial,BinaryFamilyArithmetic.workPolynomial_eval]
  exact BinaryFamilyArithmetic.multiply_bounds order (BinaryFirstInverseProgram.colors security) _ _ programs _ _ hfirst hsecond arity inputs centers hi hb

theorem current_bounds (security order : ℕ) (programs : List (Entry order)) (precision scalarBits : Polynomial ℕ)
    (scalar : IntegerBits) (hs : scalar.digits.length ≤ scalarBits.eval security)
    (arity : TruncatedArity order) (inputs : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hi : ∀ index, inputs.get index<BinaryFirstInverseProgram.colors security)
    (hb : ∀ index, centers.get index<BinaryFirstInverseProgram.colors security) :
    HeightBound (current security (precision.eval security) order programs scalar arity inputs centers).value.decode
      ((heightPolynomial order programs precision scalarBits).eval security) ∧
    (current security (precision.eval security) order programs scalar arity inputs centers).work ≤
      (workPolynomial order programs precision scalarBits).eval security := by
  let m := BinaryBackgroundLeaves.current .markedMixed security (precision.eval security) order scalar arity inputs centers
  let p := product security (precision.eval security) order programs scalar arity inputs centers
  let H := (operandPolynomial order programs precision scalarBits).eval security
  have hH : H=(BinaryBackgroundLeaves.heightPolynomial .markedMixed precision scalarBits).eval security+
      (productHeightPolynomial order programs precision scalarBits).eval security := by simp only [H,operandPolynomial,Polynomial.eval_add]
  have hm := BinaryBackgroundLeaves.current_bounds .markedMixed security order precision scalarBits scalar hs arity inputs centers hi hb
  have hp := product_bounds security order programs precision scalarBits scalar hs arity inputs centers hi hb
  have wa := RationalBits.add_work m.value p.value H (hm.1.mono (by rw [hH]; omega)) (hp.1.mono (by rw [hH]; omega))
  constructor
  · change HeightBound (RationalBits.add m.value p.value).data.decode _
    rw [RationalBits.add_value]
    simpa only [heightPolynomial,operandPolynomial,Polynomial.eval_add,Polynomial.eval_one] using hm.1.add hp.1
  · change m.work+p.work+(RationalBits.add m.value p.value).work+3 ≤ _
    simp only [workPolynomial,Polynomial.eval_add,Polynomial.eval_ofNat,primitiveWorkPolynomial_eval]
    change _ ≤ (BinaryBackgroundLeaves.workPolynomial .markedMixed order precision scalarBits).eval security+
      (productWorkPolynomial order programs precision scalarBits).eval security+primitiveWorkBound H+3
    dsimp only [m,p] at wa ⊢
    omega

end
end CurrentAFT.BinaryMarkedPairProgram
