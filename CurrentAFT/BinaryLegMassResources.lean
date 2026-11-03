import CurrentAFT.BinaryLegMass
import CurrentAFT.BinaryRootAverage

/-! # Polynomial resources for the complete centered leg mass -/
namespace CurrentAFT.BinaryLegMass
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
noncomputable section

def meanHeightPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryRootAverage.heightPolynomial precision (atRootHeightPolynomial precision BinaryFirstInverseProgram.colorsPolynomial)
def meanWorkPolynomial (precision : Polynomial ℕ) : Polynomial ℕ :=
  BinaryRootAverage.workPolynomial precision (atRootHeightPolynomial precision BinaryFirstInverseProgram.colorsPolynomial)
    (atRootWorkPolynomial precision BinaryFirstInverseProgram.colorsPolynomial)

theorem mean_bounds (security : ℕ) (precision : Polynomial ℕ) (word : Vector (Fin (colors security)) 3) :
    HeightBound (mean security (precision.eval security) word).data.decode ((meanHeightPolynomial precision).eval security) ∧
      (mean security (precision.eval security) word).work ≤ (meanWorkPolynomial precision).eval security :=
  BinaryRootAverage.current_bounds security precision (atRootHeightPolynomial precision BinaryFirstInverseProgram.colorsPolynomial)
    (atRootWorkPolynomial precision BinaryFirstInverseProgram.colorsPolynomial)
    (fun root => atRoot security (precision.eval security) root word)
    (fun root hr => atRoot_bounds security precision BinaryFirstInverseProgram.colorsPolynomial root word hr)

def differenceOperandPolynomial (precision rootBits : Polynomial ℕ) : Polynomial ℕ :=
  atRootHeightPolynomial precision rootBits+meanHeightPolynomial precision
def differenceHeightPolynomial (precision rootBits : Polynomial ℕ) : Polynomial ℕ :=
  differenceOperandPolynomial precision rootBits+1
def differenceWorkPolynomial (precision rootBits : Polynomial ℕ) : Polynomial ℕ :=
  atRootWorkPolynomial precision rootBits+meanWorkPolynomial precision+
    2*primitiveWorkPolynomial (differenceOperandPolynomial precision rootBits)+5

theorem difference_bounds (security : ℕ) (precision rootBits : Polynomial ℕ) (root : IntegerBits)
    (word : Vector (Fin (colors security)) 3) (hr : root.digits.length ≤ rootBits.eval security) :
    HeightBound (difference security (precision.eval security) root word).data.decode
      ((differenceHeightPolynomial precision rootBits).eval security) ∧
      (difference security (precision.eval security) root word).work ≤
        (differenceWorkPolynomial precision rootBits).eval security := by
  let first := atRoot security (precision.eval security) root word
  let second := mean security (precision.eval security) word
  let H := (differenceOperandPolynomial precision rootBits).eval security
  have hf := atRoot_bounds security precision rootBits root word hr
  have hs := mean_bounds security precision word
  have hH : H=(atRootHeightPolynomial precision rootBits).eval security+(meanHeightPolynomial precision).eval security := by
    simp only [H,differenceOperandPolynomial,Polynomial.eval_add]
  have wd := RationalBits.difference_work first.data second.data H
    (hf.1.mono (by rw [hH]; omega)) (hs.1.mono (by rw [hH]; omega))
  have wf : first.work ≤ (atRootWorkPolynomial precision rootBits).eval security := hf.2
  have ws : second.work ≤ (meanWorkPolynomial precision).eval security := hs.2
  constructor
  · change HeightBound (RationalBits.difference first.data second.data).data.decode _
    rw [RationalBits.difference_value,sub_eq_add_neg]
    simpa only [differenceHeightPolynomial,differenceOperandPolynomial,Polynomial.eval_add,Polynomial.eval_one]
      using hf.1.add hs.1.neg
  · change first.work+second.work+(RationalBits.difference first.data second.data).work+3 ≤ _
    simp only [differenceWorkPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
      primitiveWorkPolynomial_eval]
    dsimp only [H] at wd
    omega

end
end CurrentAFT.BinaryLegMass
