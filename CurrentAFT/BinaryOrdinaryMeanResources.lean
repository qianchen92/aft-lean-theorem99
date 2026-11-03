import CurrentAFT.BinaryOrdinaryMean
import CurrentAFT.BinaryRootAverage

/-! # All ordinary hybrid costs use the actual computed reference-root law -/
namespace CurrentAFT.BinaryOrdinaryMean
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
  RationalRejectionProgram BinaryFamilyProduct FixedFamilyPrograms
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
noncomputable section

def meanHeightPolynomial (order : ℕ) (programs : List (Entry order)) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryRootAverage.heightPolynomial precision (BinaryOrdinaryCoefficient.atRootHeightPolynomial order programs precision)
def meanWorkPolynomial (order : ℕ) (programs : List (Entry order)) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryRootAverage.workPolynomial precision (BinaryOrdinaryCoefficient.atRootHeightPolynomial order programs precision)
    (BinaryOrdinaryCoefficient.atRootWorkPolynomial order programs precision BinaryFirstInverseProgram.colorsPolynomial)

theorem mean_bounds (security order : ℕ) (programs : List (Entry order)) (precision : Polynomial ℕ)
    (source : Fin (colors security))
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i<BinaryProfileLookup.colors security) (hd : ∀ i, centers.get i<BinaryProfileLookup.colors security) :
    HeightBound (mean security (precision.eval security) order programs source arity colors centers).value.decode
      ((meanHeightPolynomial order programs precision).eval security) ∧
      (mean security (precision.eval security) order programs source arity colors centers).work ≤
        (meanWorkPolynomial order programs precision).eval security := by
  let kernel := fun root : IntegerBits =>
    let result := BinaryOrdinaryCoefficient.atRoot security (precision.eval security) order programs source root arity colors centers
    (⟨result.value,result.work⟩:RationalResult)
  have hk root hr := BinaryOrdinaryCoefficient.atRoot_bounds security order programs precision BinaryFirstInverseProgram.colorsPolynomial
    source root hr arity colors centers hc hd
  exact BinaryRootAverage.current_bounds security precision
    (BinaryOrdinaryCoefficient.atRootHeightPolynomial order programs precision)
    (BinaryOrdinaryCoefficient.atRootWorkPolynomial order programs precision BinaryFirstInverseProgram.colorsPolynomial) kernel hk

def heightPolynomial (order : ℕ) (programs : List (Entry order)) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryOrdinaryCoefficient.independentHeightPolynomial order programs precision+
    BinaryOrdinaryCoefficient.atRootHeightPolynomial order programs precision+meanHeightPolynomial order programs precision+2
def workPolynomial (order : ℕ) (programs : List (Entry order)) (precision rootBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryOrdinaryCoefficient.independentWorkPolynomial order programs precision+
    BinaryOrdinaryCoefficient.atRootWorkPolynomial order programs precision rootBits+meanWorkPolynomial order programs precision+
    3*primitiveWorkPolynomial (heightPolynomial order programs precision)+7

theorem current_bounds (security order : ℕ) (programs : List (Entry order)) (precision rootBits : Polynomial ℕ)
    (source : Fin (colors security)) (root : IntegerBits) (hr : root.digits.length ≤ rootBits.eval security)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i<BinaryProfileLookup.colors security) (hd : ∀ i, centers.get i<BinaryProfileLookup.colors security) :
    HeightBound (current security (precision.eval security) order programs source root arity colors centers).value.decode
      ((heightPolynomial order programs precision).eval security) ∧
      (current security (precision.eval security) order programs source root arity colors centers).work ≤
        (workPolynomial order programs precision rootBits).eval security := by
  let independent := BinaryOrdinaryCoefficient.independent security (precision.eval security) order programs source arity colors centers
  let atRoot := BinaryOrdinaryCoefficient.atRoot security (precision.eval security) order programs source root arity colors centers
  let average := mean security (precision.eval security) order programs source arity colors centers
  let combined := RationalBits.add independent.value atRoot.value
  let H := (heightPolynomial order programs precision).eval security
  let I := (BinaryOrdinaryCoefficient.independentHeightPolynomial order programs precision).eval security
  let A := (BinaryOrdinaryCoefficient.atRootHeightPolynomial order programs precision).eval security
  let M := (meanHeightPolynomial order programs precision).eval security
  have hH : H=I+A+M+2 := by simp only [H,I,A,M,heightPolynomial,Polynomial.eval_add,Polynomial.eval_ofNat]
  have hi := BinaryOrdinaryCoefficient.independent_bounds security order programs precision source arity colors centers hc hd
  have ha := BinaryOrdinaryCoefficient.atRoot_bounds security order programs precision rootBits source root hr arity colors centers hc hd
  have hm := mean_bounds security order programs precision source arity colors centers hc hd
  have hcmb : HeightBound combined.data.decode (I+A+1) := by
    rw [RationalBits.add_value]
    exact hi.1.add ha.1
  have wa := RationalBits.add_work independent.value atRoot.value H
    (hi.1.mono (by rw [hH]; omega)) (ha.1.mono (by rw [hH]; omega))
  change combined.work ≤ primitiveWorkBound H at wa
  have wd := difference_work combined.data average.value H
    (hcmb.mono (by rw [hH]; omega)) (hm.1.mono (by rw [hH]; omega))
  have wi : independent.work ≤ (BinaryOrdinaryCoefficient.independentWorkPolynomial order programs precision).eval security := hi.2
  have wr : atRoot.work ≤ (BinaryOrdinaryCoefficient.atRootWorkPolynomial order programs precision rootBits).eval security := ha.2
  have wm : average.work ≤ (meanWorkPolynomial order programs precision).eval security := hm.2
  constructor
  · change HeightBound (difference combined.data average.value).data.decode _
    rw [difference_value,sub_eq_add_neg]
    apply (hcmb.add hm.1.neg).mono
    change I+A+1+M+1 ≤ H
    rw [hH]
    omega
  · change independent.work+atRoot.work+average.work+combined.work+(difference combined.data average.value).work+5 ≤ _
    simp only [workPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,primitiveWorkPolynomial_eval]
    dsimp only [H] at wa wd
    omega

end
end CurrentAFT.BinaryOrdinaryMean
