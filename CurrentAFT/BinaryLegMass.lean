import CurrentAFT.BinaryPositiveReference
import CurrentAFT.BinaryScalarAverage
import CurrentAFT.BinaryRootSignedMass
import CurrentAFT.RationalLegMassProgram
import CurrentAFT.BinaryProfileLookup

/-! # The executed same-scalar joint mass of the three actual leg endpoints -/
namespace CurrentAFT.BinaryLegMass
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryPositiveReference.fixedMass
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

def fixedTerm (security bits : ℕ) (root scalar : IntegerBits) (word : Vector (Fin (colors security)) 3)
    (compensator : Fin (colors security)) : RationalResult :=
  let four := BinaryTupleSum.prepend compensator word
  let result := BinaryPositiveReference.fixedMass security bits BinaryProfileLookup.zeroRoot root scalar four.value
  ⟨result.data,four.work+result.work+2⟩

theorem fixedTerm_value (security bits : ℕ) (root scalar : IntegerBits) (word : Vector (Fin (colors security)) 3)
    (compensator : Fin (colors security)) :
    (fixedTerm security bits root scalar word compensator).data.decode=
      RationalPositiveReferenceProgram.fixedMass security bits 0 root.decode scalar.decode
        (Fin.cons compensator.val (fun index => (word.get index).val)) := by
  simp only [fixedTerm,BinaryPositiveReference.fixedMass_value,BinaryProfileLookup.zeroRoot,IntegerBits.decode,
    signedValue,Bool.false_eq_true,if_false,BinaryArithmetic.value]
  congr 1
  funext index
  rw [BinaryTupleSum.prepend_get]
  fin_cases index <;> rfl

def fixed (security bits : ℕ) (root scalar : IntegerBits) (word : Vector (Fin (colors security)) 3) : RationalResult :=
  let modulus := PublicParameterProgram.modulus security
  let result := sumFin modulus.count (fixedTerm security bits root scalar word)
  ⟨result.data,modulus.work+result.work+2⟩

theorem fixed_value (security bits : ℕ) (root scalar : IntegerBits) (word : Vector (Fin (colors security)) 3) :
    (fixed security bits root scalar word).data.decode=
      RationalLegMassProgram.fixed security bits root.decode scalar.decode (fun index => (word.get index).val) := by
  simp only [fixed,sumFin_value,fixedTerm_value,RationalLegMassProgram.fixed]

def atRoot (security bits : ℕ) (root : IntegerBits) (word : Vector (Fin (colors security)) 3) : RationalResult :=
  BinaryScalarAverage.current security bits (fun scalar => fixed security bits root scalar word)

theorem atRoot_value (security bits : ℕ) (root : IntegerBits) (word : Vector (Fin (colors security)) 3) :
    (atRoot security bits root word).data.decode=
      RationalLegMassProgram.atRoot security bits root.decode (fun index => (word.get index).val) := by
  rw [atRoot,BinaryScalarAverage.current_value security bits _
    (fun scalar => RationalLegMassProgram.fixed security bits root.decode scalar (fun index => (word.get index).val))
    (fun scalar => fixed_value security bits root scalar word)]
  rfl

def meanTerm (security bits : ℕ) (word : Vector (Fin (colors security)) 3) (root : Fin (colors security)) : RationalResult :=
  let code := canonicalCounter root.val
  let probability := BinaryRootSignedMass.referenceEntry security bits root.val
  let column := atRoot security bits ⟨false,code.digits⟩ word
  let result := RationalBits.multiply probability.data column.data
  ⟨result.data,code.work+probability.work+column.work+result.work+4⟩

theorem meanTerm_value (security bits : ℕ) (word : Vector (Fin (colors security)) 3) (root : Fin (colors security)) :
    (meanTerm security bits word root).data.decode=
      RootSignedMassProgram.referenceEntry security bits root.val*
        RationalLegMassProgram.atRoot security bits root.val (fun index => (word.get index).val) := by
  simp only [meanTerm,RationalBits.multiply_value,BinaryRootSignedMass.referenceEntry_value,atRoot_value,
    IntegerBits.decode,signedValue,Bool.false_eq_true,if_false,canonicalCounter_value]

def mean (security bits : ℕ) (word : Vector (Fin (colors security)) 3) : RationalResult :=
  let modulus := PublicParameterProgram.modulus security
  let result := sumFin modulus.count (meanTerm security bits word)
  ⟨result.data,modulus.work+result.work+2⟩

theorem mean_value (security bits : ℕ) (word : Vector (Fin (colors security)) 3) :
    (mean security bits word).data.decode=RationalLegMassProgram.mean security bits (fun index => (word.get index).val) := by
  simp only [mean,sumFin_value,meanTerm_value,RationalLegMassProgram.mean]

def difference (security bits : ℕ) (root : IntegerBits) (word : Vector (Fin (colors security)) 3) : RationalResult :=
  let first := atRoot security bits root word
  let second := mean security bits word
  let result := RationalBits.difference first.data second.data
  ⟨result.data,first.work+second.work+result.work+3⟩

theorem difference_value (security bits : ℕ) (root : IntegerBits) (word : Vector (Fin (colors security)) 3) :
    (difference security bits root word).data.decode=
      RationalLegMassProgram.difference security bits root.decode (fun index => (word.get index).val) := by
  simp only [difference,RationalBits.difference_value,atRoot_value,mean_value,RationalLegMassProgram.difference]

noncomputable section
def fixedHeightPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryFirstInverseProgram.colorsPolynomial*(BinaryPositiveReference.heightPolynomial precision inputBits+1)
def fixedWorkPolynomial (precision inputBits : Polynomial ℕ) : Polynomial ℕ :=
  PublicParameterProgram.workPolynomial+BinaryFirstInverseProgram.colorsPolynomial*
    (BinaryPositiveReference.workPolynomial precision inputBits+60+
      primitiveWorkPolynomial ((BinaryFirstInverseProgram.colorsPolynomial+1)*
        (BinaryPositiveReference.heightPolynomial precision inputBits+1))+2)+4

theorem fixed_bounds (security : ℕ) (precision inputBits : Polynomial ℕ) (root scalar : IntegerBits)
    (word : Vector (Fin (colors security)) 3)
    (hr : root.digits.length ≤ inputBits.eval security) (hs : scalar.digits.length ≤ inputBits.eval security) :
    HeightBound (fixed security (precision.eval security) root scalar word).data.decode
      ((fixedHeightPolynomial precision inputBits).eval security) ∧
      (fixed security (precision.eval security) root scalar word).work ≤ (fixedWorkPolynomial precision inputBits).eval security := by
  let H := (BinaryPositiveReference.heightPolynomial precision inputBits).eval security
  let W := (BinaryPositiveReference.workPolynomial precision inputBits).eval security
  have ht (compensator : Fin (colors security)) :
      HeightBound (fixedTerm security (precision.eval security) root scalar word compensator).data.decode H ∧
      (fixedTerm security (precision.eval security) root scalar word compensator).work ≤ W+60 := by
    have hp := BinaryPositiveReference.fixedMass_bounds security precision inputBits BinaryProfileLookup.zeroRoot root scalar
      (BinaryTupleSum.prepend compensator word).value (by simp [BinaryProfileLookup.zeroRoot]) hr hs
    have wp := BinaryTupleSum.prepend_work compensator word
    constructor
    · exact hp.1
    · change (BinaryTupleSum.prepend compensator word).work+
        (BinaryPositiveReference.fixedMass security (precision.eval security) BinaryProfileLookup.zeroRoot root scalar
          (BinaryTupleSum.prepend compensator word).value).work+2 ≤ W+60
      norm_num [BinaryTupleSum.prependWork] at wp
      omega
  have hh := sumFin_height (colors security) H (fixedTerm security (precision.eval security) root scalar word) (fun index => (ht index).1)
  have hw := sumFin_work (colors security) H (W+60) (fixedTerm security (precision.eval security) root scalar word)
    (fun index => (ht index).1) (fun index => (ht index).2)
  have hq : colors security ≤ BinaryFirstInverseProgram.colorsPolynomial.eval security := BinaryFirstInverseProgram.colors_bound security
  have hlarge : (colors security)*(W+60+primitiveWorkBound ((colors security+1)*(H+1))+2)+2 ≤
      BinaryFirstInverseProgram.colorsPolynomial.eval security*
        (W+60+primitiveWorkBound ((BinaryFirstInverseProgram.colorsPolynomial.eval security+1)*(H+1))+2)+2 := by
    unfold primitiveWorkBound
    gcongr
  have wm := PublicParameterProgram.modulus_work security
  constructor
  · apply hh.mono
    simp only [fixedHeightPolynomial,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_one]
    exact Nat.mul_le_mul_right _ hq
  · change (PublicParameterProgram.modulus security).work+
      (sumFin (colors security) (fixedTerm security (precision.eval security) root scalar word)).work+2 ≤ _
    simp only [fixedWorkPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
      Polynomial.eval_one,primitiveWorkPolynomial_eval]
    rw [PublicParameterProgram.workPolynomial_eval]
    have ww := hw.trans hlarge
    dsimp only [H,W] at ww
    omega

def atRootHeightPolynomial (precision rootBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryCoefficientScalarAverage.heightPolynomial precision
    (fixedHeightPolynomial precision (rootBits+BinaryCoefficientScalarAverage.scalarBitsPolynomial))
def atRootWorkPolynomial (precision rootBits : Polynomial ℕ) : Polynomial ℕ :=
  BinaryCoefficientScalarAverage.workPolynomial precision
    (fixedHeightPolynomial precision (rootBits+BinaryCoefficientScalarAverage.scalarBitsPolynomial))
    (fixedWorkPolynomial precision (rootBits+BinaryCoefficientScalarAverage.scalarBitsPolynomial))

theorem atRoot_bounds (security : ℕ) (precision rootBits : Polynomial ℕ) (root : IntegerBits)
    (word : Vector (Fin (colors security)) 3) (hr : root.digits.length ≤ rootBits.eval security) :
    HeightBound (atRoot security (precision.eval security) root word).data.decode ((atRootHeightPolynomial precision rootBits).eval security) ∧
      (atRoot security (precision.eval security) root word).work ≤ (atRootWorkPolynomial precision rootBits).eval security := by
  apply BinaryScalarAverage.current_bounds security precision
    (fixedHeightPolynomial precision (rootBits+BinaryCoefficientScalarAverage.scalarBitsPolynomial))
    (fixedWorkPolynomial precision (rootBits+BinaryCoefficientScalarAverage.scalarBitsPolynomial))
  intro scalar hs
  apply fixed_bounds security precision (rootBits+BinaryCoefficientScalarAverage.scalarBitsPolynomial) root scalar word
  · simp only [Polynomial.eval_add]; omega
  · simp only [Polynomial.eval_add]; omega

end
end CurrentAFT.BinaryLegMass
