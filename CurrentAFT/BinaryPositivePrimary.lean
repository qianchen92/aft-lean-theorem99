import CurrentAFT.BinaryPrimaryFamily
import CurrentAFT.BinaryPositiveAverage
import CurrentAFT.BinaryFamilyValidSemantics
import CurrentAFT.RationalPositiveFamilyProgram

/-! The computed independent positive reference and its actual finite reciprocal. -/
namespace CurrentAFT.BinaryPositivePrimary
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
  GradedControlAlgebra BinaryFamilyProduct FixedFamilyPrograms
open BinaryPrimarySelectedCoefficient
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def positive (security bits order : ℕ) (fallback : BinaryPrimarySelectedCoefficient.Entry)
    (entries : Vector BinaryPrimarySelectedCoefficient.Entry 16) : CoefficientProgram order :=
  BinaryPrimaryFamily.positive security bits order fallback entries (BinaryPositiveAverage.current security bits)

def inverse (security bits order : ℕ) (programs : List (FixedFamilyPrograms.Entry order))
    (fallback : BinaryPrimarySelectedCoefficient.Entry) (entries : Vector BinaryPrimarySelectedCoefficient.Entry 16) : CoefficientProgram order :=
  BinaryFamilyReciprocal.current order programs (positive security bits order fallback entries)

noncomputable section
open scoped Classical

theorem positive_value (security bits order : ℕ) (fallback : BinaryPrimarySelectedCoefficient.Entry)
    (entries : Vector BinaryPrimarySelectedCoefficient.Entry 16) (ordering : Fin 16 ≃ Finset (Fin 4))
    (hselected : ∀ index, (entries.get index).selected=ordering index) (hvalid : ∀ index, Valid (entries.get index))
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i<BinaryFirstInverseProgram.colors security) (hd : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    (positive security bits order fallback entries arity colors centers).value.decode=
      RationalPositiveFamilyProgram.positive security bits order arity colors.get centers.get :=
  BinaryPrimaryFamily.positive_value security bits order fallback entries ordering hselected hvalid
    (BinaryPositiveAverage.current security bits) (RationalPositiveReferenceProgram.current security bits)
    (BinaryPositiveAverage.current_value security bits) arity colors centers hc hd

theorem inverse_value (security bits order : ℕ) (programs : List (FixedFamilyPrograms.Entry order))
    (hcorrect : Correct order programs) (hcomplete : Complete order programs)
    (fallback : BinaryPrimarySelectedCoefficient.Entry) (entries : Vector BinaryPrimarySelectedCoefficient.Entry 16)
    (ordering : Fin 16 ≃ Finset (Fin 4)) (hselected : ∀ index, (entries.get index).selected=ordering index)
    (hvalid : ∀ index, Valid (entries.get index))
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i<BinaryFirstInverseProgram.colors security) (hd : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    (inverse security bits order programs fallback entries arity colors centers).value.decode=
      RationalPositiveFamilyProgram.inverse security bits order arity colors.get centers.get :=
  BinaryFamilyValidSemantics.reciprocal_value order (BinaryFirstInverseProgram.colors security) programs hcorrect hcomplete
    (positive security bits order fallback entries) (RationalPositiveFamilyProgram.positive security bits order)
    (positive_value security bits order fallback entries ordering hselected hvalid) arity colors centers hc hd

noncomputable def positiveHeight (entries : Vector BinaryPrimarySelectedCoefficient.Entry 16) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryPrimaryFamily.positiveHeightPolynomial entries precision (BinaryPositiveAverage.heightPolynomial precision)
noncomputable def positiveWork (order : ℕ) (entries : Vector BinaryPrimarySelectedCoefficient.Entry 16) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryPrimaryFamily.positiveWorkPolynomial order entries precision
    (BinaryPositiveAverage.heightPolynomial precision) (BinaryPositiveAverage.workPolynomial precision)

theorem positive_bounds (security order : ℕ) (fallback : BinaryPrimarySelectedCoefficient.Entry)
    (entries : Vector BinaryPrimarySelectedCoefficient.Entry 16) (precision : Polynomial ℕ)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i<BinaryFirstInverseProgram.colors security) (hd : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    HeightBound (positive security (precision.eval security) order fallback entries arity colors centers).value.decode
      ((positiveHeight entries precision).eval security) ∧
      (positive security (precision.eval security) order fallback entries arity colors centers).work ≤
        (positiveWork order entries precision).eval security :=
  BinaryPrimaryFamily.positive_bounds security order fallback entries precision
    (BinaryPositiveAverage.heightPolynomial precision) (BinaryPositiveAverage.workPolynomial precision)
    (BinaryPositiveAverage.current security (precision.eval security))
    (fun word => (BinaryPositiveAverage.current_bounds security precision word).1)
    (fun word => (BinaryPositiveAverage.current_bounds security precision word).2) arity colors centers hc hd

noncomputable def heightPolynomial (order : ℕ) (programs : List (FixedFamilyPrograms.Entry order))
    (entries : Vector BinaryPrimarySelectedCoefficient.Entry 16) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyReciprocal.heightPolynomial order programs (positiveHeight entries precision)
noncomputable def workPolynomial (order : ℕ) (programs : List (FixedFamilyPrograms.Entry order))
    (entries : Vector BinaryPrimarySelectedCoefficient.Entry 16) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyReciprocal.workPolynomial order programs (positiveHeight entries precision) (positiveWork order entries precision)

theorem inverse_bounds (security order : ℕ) (programs : List (FixedFamilyPrograms.Entry order))
    (fallback : BinaryPrimarySelectedCoefficient.Entry) (entries : Vector BinaryPrimarySelectedCoefficient.Entry 16) (precision : Polynomial ℕ)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i<BinaryFirstInverseProgram.colors security) (hd : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    HeightBound (inverse security (precision.eval security) order programs fallback entries arity colors centers).value.decode
      ((heightPolynomial order programs entries precision).eval security) ∧
      (inverse security (precision.eval security) order programs fallback entries arity colors centers).work ≤
        (workPolynomial order programs entries precision).eval security :=
  BinaryFamilyReciprocal.polynomial_bounds order (BinaryFirstInverseProgram.colors security) security programs
    (positive security (precision.eval security) order fallback entries) (positiveHeight entries precision) (positiveWork order entries precision)
    (positive_bounds security order fallback entries precision) arity colors centers hc hd

end
end CurrentAFT.BinaryPositivePrimary
