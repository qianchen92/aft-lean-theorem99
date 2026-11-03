import CurrentAFT.BinaryOrdinaryCoefficient
import CurrentAFT.BinaryFamilyProductClosure

/-! # Polynomial resources for the actual ordinary numerator and denominator -/
namespace CurrentAFT.BinaryOrdinaryCoefficient
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
  RationalRejectionProgram BinaryFamilyProduct FixedFamilyPrograms
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryReferenceTables.current
noncomputable section

def bodyDeltaHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ := BinaryReferenceTables.heightPolynomial precision+2
def bodyDeltaWorkPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryReferenceTables.currentWorkPolynomial precision+15*BinaryFirstInverseProgram.colorsPolynomial+
    2*primitiveWorkPolynomial (BinaryReferenceTables.heightPolynomial precision+1)+16

theorem bodyDelta_bounds (security : ℕ) (precision : Polynomial ℕ) (source output : Fin (colors security)) :
    HeightBound (bodyDelta security (precision.eval security) source output).data.decode
      ((bodyDeltaHeightPolynomial precision).eval security) ∧
      (bodyDelta security (precision.eval security) source output).work ≤ (bodyDeltaWorkPolynomial precision).eval security := by
  let reference := BinaryReferenceTables.current security (precision.eval security)
  let sourceValue := readVector zero reference.center source
  let point := BinaryMassLiftColumn.point source output
  let result := difference point.data sourceValue.value
  let H := (BinaryReferenceTables.heightPolynomial precision).eval security
  have hh := BinaryReferenceTables.current_bounds security precision
  have hs : HeightBound sourceValue.value.decode H := by rw [readVector_value]; exact hh.2.1 source
  have hp : HeightBound point.data.decode 1 := BinaryMassLiftColumn.point_height source output
  have wr : reference.work ≤ (BinaryReferenceTables.currentWorkPolynomial precision).eval security := hh.2.2.2.2
  have ws : sourceValue.work ≤ 3*colors security+3 := readVector_work zero reference.center source
  have wp : point.work ≤ 12*colors security+7 := BinaryMassLiftColumn.point_work source output
  have wc : result.work ≤ 2*primitiveWorkBound (H+1)+2 := difference_work point.data sourceValue.value (H+1)
    (hp.mono (by omega)) (hs.mono (by omega))
  have hq : colors security ≤ BinaryFirstInverseProgram.colorsPolynomial.eval security := BinaryFirstInverseProgram.colors_bound security
  constructor
  · change HeightBound result.data.decode _
    rw [difference_value,sub_eq_add_neg]
    apply (hp.add hs.neg).mono
    simp only [bodyDeltaHeightPolynomial,Polynomial.eval_add,Polynomial.eval_ofNat]
    dsimp only [H]
    omega
  · change reference.work+sourceValue.work+point.work+result.work+4 ≤ _
    simp only [bodyDeltaWorkPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
      Polynomial.eval_one,primitiveWorkPolynomial_eval]
    dsimp only [H] at wc
    omega

def firstHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryProfileCoefficient.heightPolynomial (BinaryOrdinaryProfile.heightPolynomial precision)
def firstWorkPolynomial (order : ℕ) (precision rootBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryProfileCoefficient.workPolynomial order (BinaryOrdinaryProfile.heightPolynomial precision)
    (BinaryOrdinaryProfile.workPolynomial precision rootBits)
def bodyFirstHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryProfileCoefficient.heightPolynomial (bodyDeltaHeightPolynomial precision)
def bodyFirstWorkPolynomial (order : ℕ) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryProfileCoefficient.workPolynomial order (bodyDeltaHeightPolynomial precision) (bodyDeltaWorkPolynomial precision)

theorem first_bounds (security order : ℕ) (precision rootBits : Polynomial ℕ) (source : Fin (colors security))
    (root : IntegerBits) (hr : root.digits.length ≤ rootBits.eval security)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i<BinaryProfileLookup.colors security) (hd : ∀ i, centers.get i<BinaryProfileLookup.colors security) :
    HeightBound (first security (precision.eval security) order source root arity colors centers).value.decode
      ((firstHeightPolynomial precision).eval security) ∧
      (first security (precision.eval security) order source root arity colors centers).work ≤
        (firstWorkPolynomial order precision rootBits).eval security :=
  BinaryProfileCoefficient.current_bounds security order true (BinaryOrdinaryProfile.heightPolynomial precision)
    (BinaryOrdinaryProfile.workPolynomial precision rootBits) (BinaryOrdinaryProfile.density security (precision.eval security) source root)
    (fun color => (BinaryOrdinaryProfile.density_bounds security precision rootBits source root color hr).1)
    (fun color => (BinaryOrdinaryProfile.density_bounds security precision rootBits source root color hr).2)
    arity colors centers hc hd

theorem bodyFirst_bounds (security order : ℕ) (precision : Polynomial ℕ) (source : Fin (colors security))
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i<BinaryProfileLookup.colors security) (hd : ∀ i, centers.get i<BinaryProfileLookup.colors security) :
    HeightBound (bodyFirst security (precision.eval security) order source arity colors centers).value.decode
      ((bodyFirstHeightPolynomial precision).eval security) ∧
      (bodyFirst security (precision.eval security) order source arity colors centers).work ≤
        (bodyFirstWorkPolynomial order precision).eval security :=
  BinaryProfileCoefficient.current_bounds security order false (bodyDeltaHeightPolynomial precision) (bodyDeltaWorkPolynomial precision)
    (bodyDelta security (precision.eval security) source) (fun color => (bodyDelta_bounds security precision source color).1)
    (fun color => (bodyDelta_bounds security precision source color).2) arity colors centers hc hd

def atRootHeightPolynomial (order : ℕ) (programs : List (Entry order)) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyProductClosure.heightPolynomial order programs (firstHeightPolynomial precision)
    (BinaryRootSingleton.inverseHeightPolynomial order programs precision 0)
def atRootWorkPolynomial (order : ℕ) (programs : List (Entry order)) (precision rootBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyProductClosure.workPolynomial order programs (firstHeightPolynomial precision)
    (BinaryRootSingleton.inverseHeightPolynomial order programs precision 0) (firstWorkPolynomial order precision rootBits)
    (BinaryRootSingleton.inverseWorkPolynomial order programs precision 0)
def independentHeightPolynomial (order : ℕ) (programs : List (Entry order)) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyProductClosure.heightPolynomial order programs (bodyFirstHeightPolynomial precision)
    (BinaryRootSingleton.inverseHeightPolynomial order programs precision 0)
def independentWorkPolynomial (order : ℕ) (programs : List (Entry order)) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFamilyProductClosure.workPolynomial order programs (bodyFirstHeightPolynomial precision)
    (BinaryRootSingleton.inverseHeightPolynomial order programs precision 0) (bodyFirstWorkPolynomial order precision)
    (BinaryRootSingleton.inverseWorkPolynomial order programs precision 0)

theorem atRoot_bounds (security order : ℕ) (programs : List (Entry order)) (precision rootBits : Polynomial ℕ)
    (source : Fin (colors security)) (root : IntegerBits) (hr : root.digits.length ≤ rootBits.eval security)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i<BinaryProfileLookup.colors security) (hd : ∀ i, centers.get i<BinaryProfileLookup.colors security) :
    HeightBound (atRoot security (precision.eval security) order programs source root arity colors centers).value.decode
      ((atRootHeightPolynomial order programs precision).eval security) ∧
      (atRoot security (precision.eval security) order programs source root arity colors centers).work ≤
        (atRootWorkPolynomial order programs precision rootBits).eval security :=
  BinaryFamilyProductClosure.polynomial_bounds order (BinaryProfileLookup.colors security) security programs
    (first security (precision.eval security) order source root)
    (BinaryRootSingleton.inverse security (precision.eval security) order programs .free BinaryProfileLookup.zeroRoot)
    (firstHeightPolynomial precision) (BinaryRootSingleton.inverseHeightPolynomial order programs precision 0)
    (firstWorkPolynomial order precision rootBits) (BinaryRootSingleton.inverseWorkPolynomial order programs precision 0)
    (first_bounds security order precision rootBits source root hr)
    (BinaryRootSingleton.inverse_bounds security order programs precision 0 .free BinaryProfileLookup.zeroRoot (by simp [BinaryProfileLookup.zeroRoot]))
    arity colors centers hc hd

theorem independent_bounds (security order : ℕ) (programs : List (Entry order)) (precision : Polynomial ℕ)
    (source : Fin (colors security))
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i<BinaryProfileLookup.colors security) (hd : ∀ i, centers.get i<BinaryProfileLookup.colors security) :
    HeightBound (independent security (precision.eval security) order programs source arity colors centers).value.decode
      ((independentHeightPolynomial order programs precision).eval security) ∧
      (independent security (precision.eval security) order programs source arity colors centers).work ≤
        (independentWorkPolynomial order programs precision).eval security :=
  BinaryFamilyProductClosure.polynomial_bounds order (BinaryProfileLookup.colors security) security programs
    (bodyFirst security (precision.eval security) order source)
    (BinaryRootSingleton.inverse security (precision.eval security) order programs .free BinaryProfileLookup.zeroRoot)
    (bodyFirstHeightPolynomial precision) (BinaryRootSingleton.inverseHeightPolynomial order programs precision 0)
    (bodyFirstWorkPolynomial order precision) (BinaryRootSingleton.inverseWorkPolynomial order programs precision 0)
    (bodyFirst_bounds security order precision source)
    (BinaryRootSingleton.inverse_bounds security order programs precision 0 .free BinaryProfileLookup.zeroRoot (by simp [BinaryProfileLookup.zeroRoot]))
    arity colors centers hc hd

end
end CurrentAFT.BinaryOrdinaryCoefficient
