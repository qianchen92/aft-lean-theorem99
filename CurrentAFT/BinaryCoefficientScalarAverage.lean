import CurrentAFT.BinaryRootPreProfileResources
import CurrentAFT.BinaryFamilyArithmetic
import CurrentAFT.RationalScalarFamilyAverage

/-! # One shared actual scalar averaged after complete coefficient products -/
namespace CurrentAFT.BinaryCoefficientScalarAverage
open AFT GaussianSource RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
  RationalRejectionProgram BinaryFamilyProduct GradedControlAlgebra FiniteConvolutionProgram
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryActivationProgram.cutoff

def term (order cutoff : ℕ) (table : IntegerBits → CoefficientProgram order)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (index : Fin (2*cutoff+1)) : RationalResult :=
  let scalar := BinaryAnchorProgram.coordinate cutoff index.val
  let result := table ⟨scalar.negative,scalar.digits⟩ arity colors centers
  ⟨result.value,scalar.work+result.work+2⟩

def current (security bits order : ℕ) (table : IntegerBits → CoefficientProgram order) : CoefficientProgram order :=
  fun arity colors centers =>
    let window := BinaryActivationProgram.cutoff security
    let result := BinaryWindowAverage.evaluate security window.count bits (term order window.count table arity colors centers)
    ⟨result.data,window.work+result.work+2⟩

theorem current_value (security bits order : ℕ) (table : IntegerBits → CoefficientProgram order)
    (ideal : ℤ → RationalFamilyProductProgram.Table ℚ ℕ ℕ order)
    (hvalue : ∀ scalar arity colors centers, (table scalar arity colors centers).value.decode=
      ideal scalar.decode arity colors.get centers.get)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val) :
    (current security bits order table arity colors centers).value.decode=
      RationalScalarFamilyAverage.current security bits order ideal arity colors.get centers.get := by
  unfold current
  rw [BinaryWindowAverage.evaluate_value,BinaryActivationProgram.cutoff_value]
  simp only [term,hvalue,IntegerBits.decode,BinaryAnchorProgram.coordinate_value]
  unfold RationalScalarFamilyAverage.current
  have hc : RationalBackgroundLinearProgram.cutoff security=(security+2)^2-1 := rfl
  rw [hc]
  have hreindex := (windowIndexEquiv ((security+2)^2-1)).sum_comp (fun scalar : Window ((security+2)^2-1) =>
    RationalProposalProgram.gaussianWeight security ((security+2)^2-1) bits scalar *
      ideal scalar.val arity colors.get centers.get)
  rw [← hreindex]
  apply Finset.sum_congr rfl
  intro index _
  rw [RationalProposalProgram.gaussianWeight_eq]
  rfl

noncomputable section
def scalarBitsPolynomial : Polynomial ℕ := BinaryRootProfile.scalarBitsPolynomial
def heightPolynomial (precision leafBits : Polynomial ℕ) : Polynomial ℕ :=
  (2*BinaryRootProfile.cutoffPolynomial+1)*(500000000*((Polynomial.X+2)^2+precision+2)^6+leafBits+1)
def workPolynomial (precision leafBits leafWork : Polynomial ℕ) : Polynomial ℕ :=
  BinaryActivationProgram.cutoffWorkPolynomial+
    BinaryWindowAverage.evaluateWorkPolynomial BinaryRootProfile.cutoffPolynomial precision leafBits
      (BinaryAnchorProgram.coordinateWorkPolynomial BinaryRootProfile.cutoffPolynomial+leafWork+2)+2

theorem current_bounds (security order base : ℕ) (precision leafBits leafWork : Polynomial ℕ)
    (table : IntegerBits → CoefficientProgram order)
    (htable : ∀ scalar, scalar.digits.length ≤ scalarBitsPolynomial.eval security →
      ∀ arity colors centers, (∀ i, colors.get i<base) → (∀ i, centers.get i<base) →
        HeightBound (table scalar arity colors centers).value.decode (leafBits.eval security) ∧
          (table scalar arity colors centers).work ≤ leafWork.eval security)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i<base) (hd : ∀ i, centers.get i<base) :
    HeightBound (current security (precision.eval security) order table arity colors centers).value.decode
      ((heightPolynomial precision leafBits).eval security) ∧
      (current security (precision.eval security) order table arity colors centers).work ≤
        (workPolynomial precision leafBits leafWork).eval security := by
  let window := BinaryActivationProgram.cutoff security
  have hcut : window.count≤(security+2)^2 := by rw [BinaryActivationProgram.cutoff_value]; omega
  have ht (index : Fin (2*window.count+1)) :
      HeightBound (term order window.count table arity colors centers index).data.decode (leafBits.eval security) ∧
        (term order window.count table arity colors centers index).work ≤
          (BinaryAnchorProgram.coordinateWorkPolynomial BinaryRootProfile.cutoffPolynomial+leafWork+2).eval security := by
    let scalar := BinaryAnchorProgram.coordinate window.count index.val
    have hs := BinaryAnchorProgram.coordinate_bounds window.count index.val ((security+2)^2) hcut (by have := index.isLt; omega)
    have hl : scalar.digits.length ≤ scalarBitsPolynomial.eval security := by
      simpa only [scalarBitsPolynomial,BinaryRootProfile.scalarBitsPolynomial,BinaryRootProfile.cutoffPolynomial,
        Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one] using hs.1
    have hp := htable ⟨scalar.negative,scalar.digits⟩ hl arity colors centers hc hd
    have ws : scalar.work ≤ (BinaryAnchorProgram.coordinateWorkPolynomial BinaryRootProfile.cutoffPolynomial).eval security := by
      simpa only [BinaryAnchorProgram.coordinateWorkPolynomial,BinaryAnchorProgram.coordinateWork,BinaryRootProfile.cutoffPolynomial,
        Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one] using hs.2
    constructor
    · exact hp.1
    · change scalar.work+(table ⟨scalar.negative,scalar.digits⟩ arity colors centers).work+2 ≤ _
      simpa only [Polynomial.eval_add,Polynomial.eval_ofNat] using Nat.add_le_add_right (Nat.add_le_add ws hp.2) 2
  have he := BinaryWindowAverage.evaluate_bounds security window.count (precision.eval security)
    (term order window.count table arity colors centers) (leafBits.eval security)
    ((BinaryAnchorProgram.coordinateWorkPolynomial BinaryRootProfile.cutoffPolynomial+leafWork+2).eval security)
    hcut (fun index => (ht index).1) (fun index => (ht index).2)
  have ww := BinaryActivationProgram.cutoff_work security
  constructor
  · apply he.1.mono
    simp only [heightPolynomial,BinaryRootProfile.cutoffPolynomial,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one,
      BinaryWindowAverage.sumHeight,BinaryGaussianAverage.gaussianHeight,CurrentGaussianBits.budget]
    gcongr
  · change window.work+(BinaryWindowAverage.evaluate security window.count (precision.eval security)
      (term order window.count table arity colors centers)).work+2 ≤ _
    rw [workPolynomial,Polynomial.eval_add,Polynomial.eval_add,Polynomial.eval_ofNat,
      BinaryActivationProgram.cutoffWorkPolynomial_eval,BinaryWindowAverage.evaluateWorkPolynomial_eval]
    have wm : BinaryWindowAverage.evaluateWork security window.count (precision.eval security) (leafBits.eval security)
        ((BinaryAnchorProgram.coordinateWorkPolynomial BinaryRootProfile.cutoffPolynomial+leafWork+2).eval security) ≤
      BinaryWindowAverage.evaluateWork security (BinaryRootProfile.cutoffPolynomial.eval security) (precision.eval security) (leafBits.eval security)
        ((BinaryAnchorProgram.coordinateWorkPolynomial BinaryRootProfile.cutoffPolynomial+leafWork+2).eval security) := by
      unfold BinaryWindowAverage.evaluateWork
      apply Nat.add_le_add_right
      apply Nat.add_le_add_left
      exact BinaryWindowAverage.sumWork_mono (by simpa only [BinaryRootProfile.cutoffPolynomial,Polynomial.eval_pow,
        Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_ofNat] using Nat.add_le_add_right (Nat.mul_le_mul_left 2 hcut) 1) le_rfl le_rfl le_rfl
    exact Nat.add_le_add_right (Nat.add_le_add ww (he.2.trans wm)) 2

end
end CurrentAFT.BinaryCoefficientScalarAverage
