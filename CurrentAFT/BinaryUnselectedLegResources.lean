import CurrentAFT.BinaryUnselectedLeg
import CurrentAFT.BinaryFamilyProductClosure

/-! # The complete unselected leg has derived polynomial binary resources -/
namespace CurrentAFT.BinaryUnselectedLeg
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
  RationalRejectionProgram BinaryFamilyProduct FixedFamilyPrograms
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
noncomputable section

def higherHeightPolynomial (entries : Vector Descriptor 8) (precision rootBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryLegFamily.sumHeightPolynomial entries precision (BinaryLegMass.differenceHeightPolynomial precision rootBits)
def higherWorkPolynomial (order : ℕ) (entries : Vector Descriptor 8) (precision rootBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryLegFamily.sumWorkPolynomial order 2 entries precision (BinaryLegMass.differenceHeightPolynomial precision rootBits)
    (BinaryLegMass.differenceWorkPolynomial precision rootBits)
def positiveHeightPolynomial (entries : Vector Descriptor 8) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryLegFamily.positiveHeightPolynomial entries precision (BinaryLegMass.meanHeightPolynomial precision)
def positiveWorkPolynomial (order : ℕ) (entries : Vector Descriptor 8) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryLegFamily.positiveWorkPolynomial order entries precision (BinaryLegMass.meanHeightPolynomial precision)
    (BinaryLegMass.meanWorkPolynomial precision)

theorem higher_bounds (security order : ℕ) (fallback : Descriptor) (entries : Vector Descriptor 8)
    (precision rootBits : Polynomial ℕ) (root : IntegerBits) (hr : root.digits.length ≤ rootBits.eval security)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i<BinaryFirstInverseProgram.colors security) (hd : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    HeightBound (higher security (precision.eval security) order fallback entries root arity colors centers).value.decode
      ((higherHeightPolynomial entries precision rootBits).eval security) ∧
      (higher security (precision.eval security) order fallback entries root arity colors centers).work ≤
        (higherWorkPolynomial order entries precision rootBits).eval security :=
  BinaryLegFamily.sum_bounds security order 2 fallback entries precision (BinaryLegMass.differenceHeightPolynomial precision rootBits)
    (BinaryLegMass.differenceWorkPolynomial precision rootBits) (BinaryLegMass.difference security (precision.eval security) root)
    (fun word => (BinaryLegMass.difference_bounds security precision rootBits root word hr).1)
    (fun word => (BinaryLegMass.difference_bounds security precision rootBits root word hr).2) arity colors centers hc hd

theorem positive_bounds (security order : ℕ) (fallback : Descriptor) (entries : Vector Descriptor 8)
    (precision : Polynomial ℕ)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i<BinaryFirstInverseProgram.colors security) (hd : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    HeightBound (positive security (precision.eval security) order fallback entries arity colors centers).value.decode
      ((positiveHeightPolynomial entries precision).eval security) ∧
      (positive security (precision.eval security) order fallback entries arity colors centers).work ≤
        (positiveWorkPolynomial order entries precision).eval security :=
  BinaryLegFamily.positive_bounds security order fallback entries precision (BinaryLegMass.meanHeightPolynomial precision)
    (BinaryLegMass.meanWorkPolynomial precision) (BinaryLegMass.mean security (precision.eval security))
    (fun word => (BinaryLegMass.mean_bounds security precision word).1)
    (fun word => (BinaryLegMass.mean_bounds security precision word).2) arity colors centers hc hd

def inverseHeightPolynomial (order : ℕ) (programs : List (Entry order)) (entries : Vector Descriptor 8)
    (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyReciprocal.heightPolynomial order programs (positiveHeightPolynomial entries precision)
def inverseWorkPolynomial (order : ℕ) (programs : List (Entry order)) (entries : Vector Descriptor 8)
    (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyReciprocal.workPolynomial order programs (positiveHeightPolynomial entries precision)
    (positiveWorkPolynomial order entries precision)

theorem inverse_bounds (security order : ℕ) (programs : List (Entry order)) (fallback : Descriptor) (entries : Vector Descriptor 8)
    (precision : Polynomial ℕ)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i<BinaryFirstInverseProgram.colors security) (hd : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    HeightBound (inverse security (precision.eval security) order programs fallback entries arity colors centers).value.decode
      ((inverseHeightPolynomial order programs entries precision).eval security) ∧
      (inverse security (precision.eval security) order programs fallback entries arity colors centers).work ≤
        (inverseWorkPolynomial order programs entries precision).eval security :=
  BinaryFamilyReciprocal.polynomial_bounds order (BinaryFirstInverseProgram.colors security) security programs
    (positive security (precision.eval security) order fallback entries) (positiveHeightPolynomial entries precision)
    (positiveWorkPolynomial order entries precision) (positive_bounds security order fallback entries precision) arity colors centers hc hd

def numeratorOperandPolynomial (entries : Vector Descriptor 8) (precision rootBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryRootSingleton.firstHeightPolynomial precision 0 rootBits+higherHeightPolynomial entries precision rootBits
def numeratorHeightPolynomial (entries : Vector Descriptor 8) (precision rootBits : Polynomial ℕ) : Polynomial ℕ :=
  numeratorOperandPolynomial entries precision rootBits+1
def numeratorWorkPolynomial (order : ℕ) (entries : Vector Descriptor 8) (precision rootBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryRootSingleton.firstWorkPolynomial order precision 0 rootBits+higherWorkPolynomial order entries precision rootBits+
    primitiveWorkPolynomial (numeratorOperandPolynomial entries precision rootBits)+2

theorem numerator_bounds (security order : ℕ) (fallback : Descriptor) (entries : Vector Descriptor 8)
    (precision rootBits : Polynomial ℕ) (root : IntegerBits) (hr : root.digits.length ≤ rootBits.eval security)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i<BinaryFirstInverseProgram.colors security) (hd : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    HeightBound (numerator security (precision.eval security) order fallback entries root arity colors centers).value.decode
      ((numeratorHeightPolynomial entries precision rootBits).eval security) ∧
      (numerator security (precision.eval security) order fallback entries root arity colors centers).work ≤
        (numeratorWorkPolynomial order entries precision rootBits).eval security := by
  let first := BinaryRootSingleton.first security (precision.eval security) order .attachment BinaryProfileLookup.zeroRoot root arity colors centers
  let higher := higher security (precision.eval security) order fallback entries root arity colors centers
  let H := (numeratorOperandPolynomial entries precision rootBits).eval security
  have hf := BinaryRootSingleton.first_bounds security order precision 0 rootBits .attachment BinaryProfileLookup.zeroRoot root
    (by simp [BinaryProfileLookup.zeroRoot]) hr arity colors centers hc hd
  have hh := higher_bounds security order fallback entries precision rootBits root hr arity colors centers hc hd
  have hH : H=(BinaryRootSingleton.firstHeightPolynomial precision 0 rootBits).eval security+
      (higherHeightPolynomial entries precision rootBits).eval security := by
    simp only [H,numeratorOperandPolynomial,Polynomial.eval_add]
  have wm := RationalBits.add_work first.value higher.value H
    (hf.1.mono (by rw [hH]; omega)) (hh.1.mono (by rw [hH]; omega))
  have wf : first.work ≤ (BinaryRootSingleton.firstWorkPolynomial order precision 0 rootBits).eval security := hf.2
  have wh : higher.work ≤ (higherWorkPolynomial order entries precision rootBits).eval security := hh.2
  constructor
  · change HeightBound (RationalBits.add first.value higher.value).data.decode _
    rw [RationalBits.add_value]
    simpa only [numeratorHeightPolynomial,numeratorOperandPolynomial,Polynomial.eval_add,Polynomial.eval_one] using hf.1.add hh.1
  · change first.work+higher.work+(RationalBits.add first.value higher.value).work+2 ≤ _
    simp only [numeratorWorkPolynomial,Polynomial.eval_add,Polynomial.eval_ofNat,primitiveWorkPolynomial_eval]
    dsimp only [H] at wm
    omega

def heightPolynomial (order : ℕ) (programs : List (Entry order)) (entries : Vector Descriptor 8)
    (precision rootBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyProductClosure.heightPolynomial order programs (numeratorHeightPolynomial entries precision rootBits)
    (inverseHeightPolynomial order programs entries precision)
def workPolynomial (order : ℕ) (programs : List (Entry order)) (entries : Vector Descriptor 8)
    (precision rootBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyProductClosure.workPolynomial order programs (numeratorHeightPolynomial entries precision rootBits)
    (inverseHeightPolynomial order programs entries precision) (numeratorWorkPolynomial order entries precision rootBits)
    (inverseWorkPolynomial order programs entries precision)

theorem current_bounds (security order : ℕ) (programs : List (Entry order)) (fallback : Descriptor) (entries : Vector Descriptor 8)
    (precision rootBits : Polynomial ℕ) (root : IntegerBits) (hr : root.digits.length ≤ rootBits.eval security)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i<BinaryFirstInverseProgram.colors security) (hd : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    HeightBound (current security (precision.eval security) order programs fallback entries root arity colors centers).value.decode
      ((heightPolynomial order programs entries precision rootBits).eval security) ∧
      (current security (precision.eval security) order programs fallback entries root arity colors centers).work ≤
        (workPolynomial order programs entries precision rootBits).eval security :=
  BinaryFamilyProductClosure.polynomial_bounds order (BinaryFirstInverseProgram.colors security) security programs
    (numerator security (precision.eval security) order fallback entries root) (inverse security (precision.eval security) order programs fallback entries)
    (numeratorHeightPolynomial entries precision rootBits) (inverseHeightPolynomial order programs entries precision)
    (numeratorWorkPolynomial order entries precision rootBits) (inverseWorkPolynomial order programs entries precision)
    (numerator_bounds security order fallback entries precision rootBits root hr)
    (inverse_bounds security order programs fallback entries precision) arity colors centers hc hd

end
end CurrentAFT.BinaryUnselectedLeg
