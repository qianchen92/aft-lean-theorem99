import CurrentAFT.BinaryRootReferenceResources
import CurrentAFT.BinaryRootMeanResources

/-! # Actual reference-root averaging of an arbitrary joint finite mass -/
namespace CurrentAFT.BinaryRootAverage
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryRootSignedMass.referenceEntry
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def term (security bits : ℕ) (kernel : IntegerBits → RationalResult) (root : Fin (colors security)) : RationalResult :=
  let code := canonicalCounter root.val
  let probability := BinaryRootSignedMass.referenceEntry security bits root.val
  let column := kernel ⟨false,code.digits⟩
  let result := RationalBits.multiply probability.data column.data
  ⟨result.data,code.work+probability.work+column.work+result.work+4⟩

def current (security bits : ℕ) (kernel : IntegerBits → RationalResult) : RationalResult :=
  let modulus := PublicParameterProgram.modulus security
  let result := sumFin modulus.count (term security bits kernel)
  ⟨result.data,modulus.work+result.work+2⟩

theorem current_value (security bits : ℕ) (kernel : IntegerBits → RationalResult) (ideal : ℤ → ℚ)
    (hvalue : ∀ root, (kernel root).data.decode=ideal root.decode) :
    (current security bits kernel).data.decode=
      ∑ root : Fin (colors security), RootSignedMassProgram.referenceEntry security bits root.val*ideal root.val := by
  simp only [current,sumFin_value,term,RationalBits.multiply_value,BinaryRootSignedMass.referenceEntry_value,hvalue,
    IntegerBits.decode,signedValue,Bool.false_eq_true,if_false,canonicalCounter_value]

noncomputable section
def termHeightPolynomial (precision leafBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryRootReferenceResources.heightPolynomial precision+leafBits
def termWorkPolynomial (precision leafBits leafWork : Polynomial ℕ) : Polynomial ℕ :=
  50*(BinaryFirstInverseProgram.colorsPolynomial+1)^2+
    BinaryRootReferenceResources.workPolynomial precision+leafWork+
    primitiveWorkPolynomial (termHeightPolynomial precision leafBits)+4
def heightPolynomial (precision leafBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFirstInverseProgram.colorsPolynomial*(termHeightPolynomial precision leafBits+1)
def workPolynomial (precision leafBits leafWork : Polynomial ℕ) : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+BinaryFirstInverseProgram.colorsPolynomial*
    (termWorkPolynomial precision leafBits leafWork+
      primitiveWorkPolynomial ((BinaryFirstInverseProgram.colorsPolynomial+1)*(termHeightPolynomial precision leafBits+1))+2)+4

theorem term_bounds (security : ℕ) (precision leafBits leafWork : Polynomial ℕ) (kernel : IntegerBits → RationalResult)
    (hkernel : ∀ root, root.digits.length ≤ BinaryFirstInverseProgram.colorsPolynomial.eval security →
      HeightBound (kernel root).data.decode (leafBits.eval security) ∧ (kernel root).work ≤ leafWork.eval security)
    (root : Fin (colors security)) :
    HeightBound (term security (precision.eval security) kernel root).data.decode
      ((termHeightPolynomial precision leafBits).eval security) ∧
      (term security (precision.eval security) kernel root).work ≤ (termWorkPolynomial precision leafBits leafWork).eval security := by
  let code := canonicalCounter root.val
  let probability := BinaryRootSignedMass.referenceEntry security (precision.eval security) root.val
  let column := kernel ⟨false,code.digits⟩
  let H := (termHeightPolynomial precision leafBits).eval security
  have hi := root.isLt.le.trans (BinaryFirstInverseProgram.colors_bound security)
  have hl : code.digits.length ≤ BinaryFirstInverseProgram.colorsPolynomial.eval security := by
    rw [canonicalCounter_length]
    exact (Nat.size_le.mpr (Nat.lt_two_pow_self (n:=root.val))).trans hi
  have hp := BinaryRootReferenceResources.referenceEntry_polynomial_bounds security precision root.val
    (root.isLt.le.trans (BinaryRootReferenceResources.colors_bound security))
  have hc := hkernel ⟨false,code.digits⟩ hl
  have hH : H=(BinaryRootReferenceResources.heightPolynomial precision).eval security+leafBits.eval security := by
    simp only [H,termHeightPolynomial,Polynomial.eval_add]
  have wm := RationalBits.multiply_work probability.data column.data H
    (hp.1.mono (by rw [hH]; omega)) (hc.1.mono (by rw [hH]; omega))
  have wc : code.work ≤ 50*(BinaryFirstInverseProgram.colorsPolynomial.eval security+1)^2 := (canonicalCounter_work root.val).trans
    (Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (Nat.add_le_add_right hi 1) 2))
  have wp : probability.work ≤ (BinaryRootReferenceResources.workPolynomial precision).eval security := hp.2
  have wk : column.work ≤ leafWork.eval security := hc.2
  constructor
  · change HeightBound (RationalBits.multiply probability.data column.data).data.decode _
    rw [RationalBits.multiply_value]
    simpa only [termHeightPolynomial,Polynomial.eval_add] using hp.1.mul hc.1
  · change code.work+probability.work+column.work+(RationalBits.multiply probability.data column.data).work+4 ≤ _
    simp only [termWorkPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
      Polynomial.eval_ofNat,Polynomial.eval_one,primitiveWorkPolynomial_eval]
    dsimp only [H] at wm
    omega

theorem current_bounds (security : ℕ) (precision leafBits leafWork : Polynomial ℕ) (kernel : IntegerBits → RationalResult)
    (hkernel : ∀ root, root.digits.length ≤ BinaryFirstInverseProgram.colorsPolynomial.eval security →
      HeightBound (kernel root).data.decode (leafBits.eval security) ∧ (kernel root).work ≤ leafWork.eval security) :
    HeightBound (current security (precision.eval security) kernel).data.decode ((heightPolynomial precision leafBits).eval security) ∧
      (current security (precision.eval security) kernel).work ≤ (workPolynomial precision leafBits leafWork).eval security := by
  let H := (termHeightPolynomial precision leafBits).eval security
  let W := (termWorkPolynomial precision leafBits leafWork).eval security
  have ht := term_bounds security precision leafBits leafWork kernel hkernel
  have hh := sumFin_height (colors security) H (term security (precision.eval security) kernel) (fun index => (ht index).1)
  have hw := sumFin_work (colors security) H W (term security (precision.eval security) kernel)
    (fun index => (ht index).1) (fun index => (ht index).2)
  have hq : colors security ≤ BinaryFirstInverseProgram.colorsPolynomial.eval security := BinaryFirstInverseProgram.colors_bound security
  have hm : (colors security)*(W+primitiveWorkBound ((colors security+1)*(H+1))+2)+2 ≤
      BinaryFirstInverseProgram.colorsPolynomial.eval security*
        (W+primitiveWorkBound ((BinaryFirstInverseProgram.colorsPolynomial.eval security+1)*(H+1))+2)+2 := by
    unfold primitiveWorkBound
    gcongr
  have wm := PublicParameterProgram.modulus_work security
  constructor
  · apply hh.mono
    simp only [heightPolynomial,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_one]
    exact Nat.mul_le_mul_right _ hq
  · change (PublicParameterProgram.modulus security).work+
      (sumFin (colors security) (term security (precision.eval security) kernel)).work+2 ≤ _
    simp only [workPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
      Polynomial.eval_one,primitiveWorkPolynomial_eval]
    rw [PublicParameterProgram.workPolynomial_eval]
    have ww := hw.trans hm
    dsimp only [H,W] at ww
    omega

end
end CurrentAFT.BinaryRootAverage
