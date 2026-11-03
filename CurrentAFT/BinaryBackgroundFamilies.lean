import CurrentAFT.BinaryFirstFamily
import CurrentAFT.BinaryBackgroundPrimary
import CurrentAFT.BinaryBackgroundResidual
import CurrentAFT.BinaryBackgroundSeed
import CurrentAFT.RationalBackgroundProgram

/-! # Actual binary producers of the original mixed free and translation tables -/
namespace CurrentAFT.BinaryBackgroundFamilies
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryBackgroundPrimary.current BinaryBackgroundResidual.current
  BinaryBackgroundBody.current BinaryBackgroundSeed.current BinaryFirstFamily.current PublicParameterProgram.modulus

def translationPrimary (security bits : ℕ) (shift : IntegerBits)
    (output : Fin (BinaryFirstInverseProgram.colors security)) : RationalResult :=
  let first := BinaryBackgroundPrimary.current security bits output
  let residual := BinaryBackgroundResidual.current security bits shift output
  let result := RationalBits.add first.data residual.data
  ⟨result.data,first.work+residual.work+result.work+3⟩

theorem translationPrimary_value (security bits : ℕ) (shift : IntegerBits)
    (output : Fin (BinaryFirstInverseProgram.colors security)) :
    (translationPrimary security bits shift output).data.decode=
      RationalBackgroundDensities.primary security bits output.val+
        RationalBackgroundDensities.residual security bits shift.decode output.val := by
  simp only [translationPrimary,RationalBits.add_value,BinaryBackgroundPrimary.current_value,BinaryBackgroundResidual.current_value]

def free (security bits order : ℕ) (arity : TruncatedArity order)
    (inputs : Vector (Fin (BinaryFirstInverseProgram.colors security)) arity.val.1.val)
    (centers : Vector (Fin (BinaryFirstInverseProgram.colors security)) arity.val.2.val) : RationalResult :=
  BinaryFirstFamily.current security arity.val.1.val arity.val.2.val
    (BinaryBackgroundPrimary.current security bits) (BinaryBackgroundBody.current security bits) inputs centers

def translation (security bits order : ℕ) (shift : IntegerBits) (arity : TruncatedArity order)
    (inputs : Vector (Fin (BinaryFirstInverseProgram.colors security)) arity.val.1.val)
    (centers : Vector (Fin (BinaryFirstInverseProgram.colors security)) arity.val.2.val) : RationalResult :=
  BinaryFirstFamily.current security arity.val.1.val arity.val.2.val
    (translationPrimary security bits shift) (BinaryBackgroundSeed.current security bits shift) inputs centers

theorem free_value (security bits order : ℕ) (arity : TruncatedArity order)
    (inputs : Vector (Fin (BinaryFirstInverseProgram.colors security)) arity.val.1.val)
    (centers : Vector (Fin (BinaryFirstInverseProgram.colors security)) arity.val.2.val) :
    (free security bits order arity inputs centers).data.decode=RationalBackgroundProgram.free security bits order arity
      (fun index => (inputs.get index).val) (fun index => (centers.get index).val) :=
  BinaryFirstFamily.current_value security order arity _ _ _ _ inputs centers
    (BinaryBackgroundPrimary.current_value security bits) (BinaryBackgroundBody.current_value security bits)

theorem translation_value (security bits order : ℕ) (shift : IntegerBits) (arity : TruncatedArity order)
    (inputs : Vector (Fin (BinaryFirstInverseProgram.colors security)) arity.val.1.val)
    (centers : Vector (Fin (BinaryFirstInverseProgram.colors security)) arity.val.2.val) :
    (translation security bits order shift arity inputs centers).data.decode=RationalBackgroundProgram.translation security bits order shift.decode arity
      (fun index => (inputs.get index).val) (fun index => (centers.get index).val) :=
  BinaryFirstFamily.current_value security order arity _ _ _ _ inputs centers
    (translationPrimary_value security bits shift) (BinaryBackgroundSeed.current_value security bits shift)

noncomputable section
noncomputable def primaryOperandHeightPolynomial (precision shiftBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryBackgroundPrimary.heightPolynomial precision+BinaryBackgroundResidual.heightPolynomial precision shiftBits
noncomputable def primaryHeightPolynomial (precision shiftBits : Polynomial ℕ) : Polynomial ℕ :=
  primaryOperandHeightPolynomial precision shiftBits+1
noncomputable def primaryWorkPolynomial (precision shiftBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryBackgroundPrimary.workPolynomial precision+BinaryBackgroundResidual.workPolynomial precision shiftBits+
    primitiveWorkPolynomial (primaryOperandHeightPolynomial precision shiftBits)+3
noncomputable def freeHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryBackgroundPrimary.heightPolynomial precision+BinaryBackgroundBody.heightPolynomial precision
noncomputable def freeWorkPolynomial (order : ℕ) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryBackgroundPrimary.workPolynomial precision+BinaryBackgroundBody.workPolynomial precision+Polynomial.C (15*order+50)
noncomputable def translationHeightPolynomial (precision shiftBits : Polynomial ℕ) : Polynomial ℕ :=
  primaryHeightPolynomial precision shiftBits+BinaryBackgroundSeed.heightPolynomial precision shiftBits
noncomputable def translationWorkPolynomial (order : ℕ) (precision shiftBits : Polynomial ℕ) : Polynomial ℕ :=
  primaryWorkPolynomial precision shiftBits+BinaryBackgroundSeed.workPolynomial precision shiftBits+Polynomial.C (15*order+50)

theorem translationPrimary_bounds (security : ℕ) (precision shiftBits : Polynomial ℕ) (shift : IntegerBits)
    (hs : shift.digits.length ≤ shiftBits.eval security) (output : Fin (BinaryFirstInverseProgram.colors security)) :
    HeightBound (translationPrimary security (precision.eval security) shift output).data.decode
      ((primaryHeightPolynomial precision shiftBits).eval security) ∧
      (translationPrimary security (precision.eval security) shift output).work≤(primaryWorkPolynomial precision shiftBits).eval security := by
  have hp := BinaryBackgroundPrimary.current_bounds security precision output
  have hr := BinaryBackgroundResidual.current_bounds security precision shiftBits shift hs output
  let H := (primaryOperandHeightPolynomial precision shiftBits).eval security
  have hH : H=(BinaryBackgroundPrimary.heightPolynomial precision).eval security+
      (BinaryBackgroundResidual.heightPolynomial precision shiftBits).eval security := by
    simp only [H,primaryOperandHeightPolynomial,Polynomial.eval_add]
  have wa := RationalBits.add_work (BinaryBackgroundPrimary.current security (precision.eval security) output).data
    (BinaryBackgroundResidual.current security (precision.eval security) shift output).data H
    (hp.1.mono (by rw [hH]; omega)) (hr.1.mono (by rw [hH]; omega))
  constructor
  · change HeightBound (RationalBits.add _ _).data.decode _
    rw [RationalBits.add_value]
    simpa only [primaryHeightPolynomial,primaryOperandHeightPolynomial,Polynomial.eval_add,Polynomial.eval_one]
      using hp.1.add hr.1
  · change _+_+_+3≤_
    simp only [primaryWorkPolynomial,Polynomial.eval_add,Polynomial.eval_ofNat,primitiveWorkPolynomial_eval]
    change _≤(BinaryBackgroundPrimary.workPolynomial precision).eval security+
      (BinaryBackgroundResidual.workPolynomial precision shiftBits).eval security+primitiveWorkBound H+3
    omega

theorem free_bounds (security order : ℕ) (precision : Polynomial ℕ) (arity : TruncatedArity order)
    (inputs : Vector (Fin (BinaryFirstInverseProgram.colors security)) arity.val.1.val)
    (centers : Vector (Fin (BinaryFirstInverseProgram.colors security)) arity.val.2.val) :
    HeightBound (free security (precision.eval security) order arity inputs centers).data.decode
      ((freeHeightPolynomial precision).eval security) ∧
      (free security (precision.eval security) order arity inputs centers).work≤(freeWorkPolynomial order precision).eval security := by
  have h := BinaryFirstFamily.current_bounds security arity.val.1.val arity.val.2.val
    (BinaryBackgroundPrimary.current security (precision.eval security)) (BinaryBackgroundBody.current security (precision.eval security)) inputs centers
    ((BinaryBackgroundPrimary.heightPolynomial precision).eval security) ((BinaryBackgroundBody.heightPolynomial precision).eval security)
    ((BinaryBackgroundPrimary.workPolynomial precision).eval security) ((BinaryBackgroundBody.workPolynomial precision).eval security)
    (fun color => (BinaryBackgroundPrimary.current_bounds security precision color).1)
    (fun color => (BinaryBackgroundBody.current_bounds security precision color).1)
    (fun color => (BinaryBackgroundPrimary.current_bounds security precision color).2)
    (fun color => (BinaryBackgroundBody.current_bounds security precision color).2)
  refine ⟨?_,h.2.trans ?_⟩
  · simpa only [freeHeightPolynomial,Polynomial.eval_add] using h.1
  · have hd := arity.property
    simp only [BinaryFirstFamily.work,freeWorkPolynomial,Polynomial.eval_add,Polynomial.eval_C]
    omega

theorem translation_bounds (security order : ℕ) (precision shiftBits : Polynomial ℕ) (shift : IntegerBits)
    (hs : shift.digits.length ≤ shiftBits.eval security) (arity : TruncatedArity order)
    (inputs : Vector (Fin (BinaryFirstInverseProgram.colors security)) arity.val.1.val)
    (centers : Vector (Fin (BinaryFirstInverseProgram.colors security)) arity.val.2.val) :
    HeightBound (translation security (precision.eval security) order shift arity inputs centers).data.decode
      ((translationHeightPolynomial precision shiftBits).eval security) ∧
      (translation security (precision.eval security) order shift arity inputs centers).work≤(translationWorkPolynomial order precision shiftBits).eval security := by
  have h := BinaryFirstFamily.current_bounds security arity.val.1.val arity.val.2.val
    (translationPrimary security (precision.eval security) shift) (BinaryBackgroundSeed.current security (precision.eval security) shift) inputs centers
    ((primaryHeightPolynomial precision shiftBits).eval security) ((BinaryBackgroundSeed.heightPolynomial precision shiftBits).eval security)
    ((primaryWorkPolynomial precision shiftBits).eval security) ((BinaryBackgroundSeed.workPolynomial precision shiftBits).eval security)
    (fun color => (translationPrimary_bounds security precision shiftBits shift hs color).1)
    (fun color => (BinaryBackgroundSeed.current_bounds security precision shiftBits shift hs color).1)
    (fun color => (translationPrimary_bounds security precision shiftBits shift hs color).2)
    (fun color => (BinaryBackgroundSeed.current_bounds security precision shiftBits shift hs color).2)
  refine ⟨?_,h.2.trans ?_⟩
  · simpa only [translationHeightPolynomial,Polynomial.eval_add] using h.1
  · have hd := arity.property
    simp only [BinaryFirstFamily.work,translationWorkPolynomial,Polynomial.eval_add,Polynomial.eval_C]
    omega

end
end CurrentAFT.BinaryBackgroundFamilies
