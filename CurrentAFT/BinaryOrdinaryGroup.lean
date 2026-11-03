import CurrentAFT.BinaryOrdinaryMeanResources
import CurrentAFT.BinaryNormalizedCoefficients

/-! # The ordinary group reads its one actual control and root exactly once -/
namespace CurrentAFT.BinaryOrdinaryGroup
open AFT GradedControlAlgebra RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
  RationalRejectionProgram BinaryFamilyProduct FixedFamilyPrograms
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def current (security bits order : ℕ) (programs : List (Entry order))
    (source : Vector (Fin (colors security)) 3) : CoefficientProgram order := fun arity colors centers =>
  let root := readVector (BinaryFirstFamily.first security) source 0
  let center := readVector (BinaryFirstFamily.first security) source 1
  let code := canonicalCounter root.value.val
  let result := BinaryOrdinaryMean.current security bits order programs center.value ⟨false,code.digits⟩ arity colors centers
  ⟨result.value,root.work+center.work+code.work+result.work+4⟩

noncomputable section
open scoped Classical

theorem current_value (security bits order : ℕ) (programs : List (Entry order))
    (hcorrect : Correct order programs) (hcomplete : Complete order programs)
    (source : Vector (Fin (colors security)) 3)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i<BinaryFirstInverseProgram.colors security) (hd : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    (current security bits order programs source arity colors centers).value.decode=
      RationalOrdinaryFamilyProgram.current security bits order (source.get 1).val (source.get 0).val arity colors.get centers.get := by
  simp only [current,readVector_value,BinaryOrdinaryMean.current_value security bits order programs hcorrect hcomplete,
    IntegerBits.decode,signedValue,Bool.false_eq_true,if_false,canonicalCounter_value]
  exact BinaryRootSingleton.normalized_point security order _ arity colors.get centers.get hc hd

def heightPolynomial (order : ℕ) (programs : List (Entry order)) (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryOrdinaryMean.heightPolynomial order programs precision
def workPolynomial (order : ℕ) (programs : List (Entry order)) (precision : Polynomial ℕ) : Polynomial ℕ :=
  50*(BinaryFirstInverseProgram.colorsPolynomial+1)^2+
    BinaryOrdinaryMean.workPolynomial order programs precision BinaryFirstInverseProgram.colorsPolynomial+28

theorem current_bounds (security order : ℕ) (programs : List (Entry order)) (precision : Polynomial ℕ)
    (source : Vector (Fin (colors security)) 3)
    (arity : TruncatedArity order) (colors : Vector ℕ arity.val.1.val) (centers : Vector ℕ arity.val.2.val)
    (hc : ∀ i, colors.get i<BinaryFirstInverseProgram.colors security) (hd : ∀ i, centers.get i<BinaryFirstInverseProgram.colors security) :
    HeightBound (current security (precision.eval security) order programs source arity colors centers).value.decode
      ((heightPolynomial order programs precision).eval security) ∧
      (current security (precision.eval security) order programs source arity colors centers).work ≤
        (workPolynomial order programs precision).eval security := by
  let root := readVector (BinaryFirstFamily.first security) source 0
  let center := readVector (BinaryFirstFamily.first security) source 1
  let code := canonicalCounter root.value.val
  have hr := root.value.isLt.le.trans (BinaryFirstInverseProgram.colors_bound security)
  have hl : code.digits.length ≤ BinaryFirstInverseProgram.colorsPolynomial.eval security := by
    rw [canonicalCounter_length]
    exact (Nat.size_le.mpr (Nat.lt_two_pow_self (n:=root.value.val))).trans hr
  have h := BinaryOrdinaryMean.current_bounds security order programs precision BinaryFirstInverseProgram.colorsPolynomial
    center.value ⟨false,code.digits⟩ hl arity colors centers hc hd
  have wr : root.work ≤ 12 := readVector_work (BinaryFirstFamily.first security) source 0
  have wc : center.work ≤ 12 := readVector_work (BinaryFirstFamily.first security) source 1
  have wk : code.work ≤ 50*(BinaryFirstInverseProgram.colorsPolynomial.eval security+1)^2 :=
    (canonicalCounter_work root.value.val).trans
      (Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (Nat.add_le_add_right hr 1) 2))
  constructor
  · exact h.1
  · change root.work+center.work+code.work+
      (BinaryOrdinaryMean.current security (precision.eval security) order programs center.value ⟨false,code.digits⟩ arity colors centers).work+4 ≤ _
    simp only [workPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_ofNat,Polynomial.eval_one]
    omega

end
end CurrentAFT.BinaryOrdinaryGroup
